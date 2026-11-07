-- Prove2me | Definitions.Def_TargetedSamplers_IsConsistentMachine
-- name    : TargetedSamplers_IsConsistentMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:29.939925+00:00
-- url     : https://prove2.me/theorems/d7c5309d-9cd8-4ca2-9c35-13050433906d
-- title:
--   Probabilistic non-deterministic machines consistent with $f$ (Definition 4.19)
-- statement:
--   Let $M$ be a machine, $f:\{0,1\}^*\to\{0,1\}^*$, and $R,T,S:\mathbb N\to\mathbb N$. $M$ is an $\mathsf F(\mathsf{MA}\cap\mathsf{AM})_R\mathsf{TISP}[T,S]$ machine **consistent with $f$** (relative to an oracle class $\mathcal O$) if for every $x\in\{0,1\}^n$ and every $O\in\mathcal O$:
--
--   1. **Complexity.** For every $w\in\{0,1\}^{T(n)}$ and $r\in\{0,1\}^{R(n)}$, $M(x,w,r)$ halts within time $T(n)$ and space $S(n)$ and reads $w$ once. The machine model enforces the read-once condition.
--   2. **Completeness (possibly vacuous).** Some, possibly empty, set $W_x$ of witnesses satisfies $\Pr_r[M(x,w,r)=f(x)]=1$ for every $w\in W_x$.
--   3. **Soundness.** $\Pr_r[\forall w:\ M(x,w,r)\in\{f(x),\bot\}]\ge 2/3$.
--
--   $M$ **computes $f$ at $x$** if some witness $w\in\{0,1\}^{T(n)}$ gives $\Pr_r[M(x,w,r)=f(x)]=1$ (Definition 4.20: $W_x\ne\emptyset$).
--
--   **Formalization Note** Item 2 is kept as printed; with $W_x=\emptyset$ it always holds. "$W_x\neq\emptyset$" is read as the existence of one good witness, the only non-vacuous reading and the one Proposition 4.26 uses. Time and space are exact (cost and space of the log-cost RAM); the theorems choose the functions. A machine without an oracle uses the trivial oracle.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definitions 4.19–4.20, pp.28–29 (pdf pp.30–31)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_coinProb

namespace TargetedSamplers

/-- `M` computes `f` at `x` relative to the oracle `O` (Chen, Doron, Ebtehaj, Tell, Targeted
Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 4.20, p.29: "M computes f
at x if W_x ≠ ∅"): some witness `w ∈ {0,1}^{T(n)}` makes `M(x, w, r) = f(x)` with probability 1
over `r ∈ {0,1}^{R(n)}`.

**Formalization Note** Definition 4.19 lets `W_x` be any, "possibly empty", set of good witnesses,
which as printed has no content. `W_x ≠ ∅` is read as the existence of one good witness, which is
the only non-vacuous reading and the one Proposition 4.26 uses. -/
def ComputesAt (M : Program) (f : List Bool → List Bool) (R T : ℕ → ℕ) (O : List Bool → ℕ)
    (x : List Bool) : Prop :=
  ∃ w : List Bool, w.length = T x.length ∧
    coinProb (R x.length) (fun r => M.Outputs ⟨x, r, w, O⟩ (some (f x))) = 1

/-- `M` is an `F(MA ∩ AM)_R TISP[T, S]` (oracle) machine consistent with `f`, relative to the oracle
class `Ocl` (Definition 4.19, pp.28–29): for every `x ∈ {0,1}ⁿ` and every `O ∈ Ocl`,

1. *Complexity.* for every `w ∈ {0,1}^{T(n)}` and `r ∈ {0,1}^{R(n)}`, `M(x, w, r)` halts within time
   `T(n)` and space `S(n)`, reading `w` once (built into the machine: the witness cursor only moves
   forward);
2. *Completeness (possibly vacuous).* some, possibly empty, set `W_x` of witnesses gives
   `Pr_r[M(x, w, r) = f(x)] = 1` for each `w ∈ W_x`;
3. *Soundness.* `Pr_r[∀ w : M(x, w, r) ∈ {f(x), ⊥}] ≥ 2/3`.

**Formalization Note** Time and space are exact here (cost `≤ T(n)`, space `≤ S(n)` on the log-cost
RAM); the theorems choose the functions. A machine without an oracle uses `Ocl = (· = noOracle)`.
Item 2 is kept as printed and is always satisfiable with `W_x = ∅`. -/
def IsConsistentMachine (M : Program) (f : List Bool → List Bool) (R T S : ℕ → ℕ)
    (Ocl : (List Bool → ℕ) → Prop) : Prop :=
  ∀ O, Ocl O → ∀ x : List Bool,
    (∀ w r : List Bool, w.length = T x.length → r.length = R x.length →
      ∃ v, M.Runs ⟨x, r, w, O⟩ (T x.length) (S x.length) v) ∧
    (∃ W : Set (List Bool), ∀ w ∈ W, w.length = T x.length ∧
      coinProb (R x.length) (fun r => M.Outputs ⟨x, r, w, O⟩ (some (f x))) = 1) ∧
    coinProb (R x.length) (fun r => ∀ w : List Bool, w.length = T x.length →
      M.Outputs ⟨x, r, w, O⟩ (some (f x)) ∨ M.Outputs ⟨x, r, w, O⟩ none) ≥ 2 / 3

end TargetedSamplers


