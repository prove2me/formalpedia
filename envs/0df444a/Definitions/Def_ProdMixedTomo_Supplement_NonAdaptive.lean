-- Prove2me | Definitions.Def_ProdMixedTomo_Supplement_NonAdaptive
-- name    : ProdMixedTomo_Supplement_NonAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:31:31.139824+00:00
-- url     : https://prove2.me/theorems/5ac05b6c-2d17-4b49-86d8-69b9414364f8
-- title:
--   Non-adaptive measuring programs
-- statement:
--   Consider a program $L$ of the base mission's measuring machine, started on the learner input $(n,N,\epsilon,\delta)$. An **execution path** is a sequence of machine states in which each step follows the program, with the random choices made arbitrarily: a `coin` instruction may give either bit, and a `measure` instruction may return any outcome string $o\in\{0,1\}^n$ (including strings of Born probability $0$). Along a path, record the direction tuple $(b_0,\dots,b_{n-1})$ used by each executed `measure`, in order; the $k$-th entry is the measurement made on the $k$-th copy of the unknown state.
--
--   The program $L$ is **non-adaptive** if, for every learner input and every two execution paths from it, the $k$-th recorded direction tuples coincide whenever both paths make a $k$-th measurement.
--
--   So the measurement applied to each copy is fixed by the input alone: it depends neither on earlier measurement outcomes, nor on coin flips, nor on the unknown state. The classical post-processing after (or between) the measurements may still be randomized. This is the restriction "using only non-adaptively chosen, single-copy, single-qubit measurements" of Theorem 3.6.
--
--   **Formalization Note** Because every outcome is allowed in a path, a path of probability zero cannot escape the condition. Comparison is entrywise on the common prefix, so a path that stops measuring earlier performs a prefix of the same measurement sequence.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6, p.19 (PDF p.21); remark after its proof, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_Machine

namespace ProdMixedTomo.Supplement

/-- One transition of the measuring machine on `n`-qubit inputs, with the random outcome chosen
arbitrarily: a halted state stays put, `coin d` may give either bit, `measure a` may give any
outcome string `o ∈ {0,1}ⁿ`, every other instruction is the base `detStep`.

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6, p.19 (PDF p.21): "using only non-adaptively chosen, single-copy, single-qubit
measurements"; p.20 (PDF p.22): "Theorem 3.6 only relies on the non-adaptive portion of Algorithm 1".

**Formalization Note.** This is the support of the base `stepLaw` with every outcome allowed,
including outcomes of Born weight `0`; it does not depend on the state `ρ`. -/
noncomputable def Succ (n : ℕ) (P : Program) (s s' : MState) : Prop :=
  if s.halted then s' = s else
    match P[s.core.pc]? with
    | some (.coin d) => ∃ c : Bool, s' = coinResult s d c
    | some (.measure a) => ∃ o : Cube n, s' = measureResult n s a o
    | _ => s' = detStep P s

/-- `path` is an execution path of `t` transitions from `s₀` (states `path 0, …, path t`). -/
def IsPath (n : ℕ) (P : Program) (s₀ : MState) (t : ℕ) (path : ℕ → MState) : Prop :=
  path 0 = s₀ ∧ ∀ i < t, Succ n P (path i) (path (i + 1))

/-- The directions `(b₀, …, b_{n−1})` read by the instruction about to execute in `s`, if that
instruction is a `measure` (and `s` is not halted). -/
noncomputable def measDir (n : ℕ) (P : Program) (s : MState) : Option (Fin n → Fin 3 → ℝ) :=
  if s.halted then none else
    match P[s.core.pc]? with
    | some (.measure a) => some (directions n s a)
    | _ => none

/-- The list of direction tuples of the `measure` calls executed along the first `t` transitions of
`path`, in order: its `k`-th entry is the measurement made on the `k`-th copy consumed. -/
noncomputable def measRecord (n : ℕ) (P : Program) (t : ℕ) (path : ℕ → MState) :
    List (Fin n → Fin 3 → ℝ) :=
  (List.range t).filterMap fun i => measDir n P (path i)

/-- A **non-adaptive** learner program: on every learner input `(n, N, ϵ, δ)`, the measurement made
on the `k`-th copy is the same along every two execution paths that make a `k`-th measurement.
The directions thus depend only on the input, never on coin results, on earlier outcomes, or on the
unknown state.

**Formalization Note.** Paths are taken over all coin and outcome choices (`Succ`), not only over
runs of positive probability; the comparison is prefix-wise, so a path that stops earlier makes a
prefix of the same measurement sequence. Classical post-processing may use coins freely. -/
def NonAdaptive (P : Program) : Prop :=
  ∀ (n N : ℕ) (ϵ δ : ℝ) (t t' : ℕ) (path path' : ℕ → MState),
    IsPath n P (learnerInput n N ϵ δ) t path → IsPath n P (learnerInput n N ϵ δ) t' path' →
    ∀ (k : ℕ) (b b' : Fin n → Fin 3 → ℝ),
      (measRecord n P t path)[k]? = some b → (measRecord n P t' path')[k]? = some b' → b = b'

end ProdMixedTomo.Supplement


