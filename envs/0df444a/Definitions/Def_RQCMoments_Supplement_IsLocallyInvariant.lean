-- Prove2me | Definitions.Def_RQCMoments_Supplement_IsLocallyInvariant
-- name    : RQCMoments_Supplement_IsLocallyInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:25.479448+00:00
-- url     : https://prove2.me/theorems/999e54a1-ee5f-430d-94e2-6062be8be0dc
-- title:
--   Definition 6.1 — $m$-locally invariant distributions on $n$-qubit unitaries, with $V\otimes I$
-- statement:
--   Identify the computational basis of $n$ qubits with $\{0,1\}^n$. For a set $S\subseteq[n]$ of qubits and an operator $V$ on the qubits of $S$, the operator $V\otimes I$ acts as $V$ on the qubits of $S$ and as the identity on the others: its entry at $(x,x')$ is $V_{x_S,x'_S}$ if $x$ and $x'$ agree outside $S$, and $0$ otherwise.
--
--   A distribution $\mu$ on the unitary group $U(2^n)$ is **$m$-locally invariant** if there is a set $S\subseteq[n]$ of $m$ qubits such that, for $U\sim\mu$,
--
--   $$(V\otimes I)\,U\sim\mu\qquad\text{for every fixed unitary }V\text{ acting on the qubits in }S.$$
--
--   Local invariance is the structural assumption of Section 6: it factorizes a single output probability into a block probability, controlled by the design property, times an independent beta variable, and it yields total-variation convergence to Porter–Thomas (Theorems 6.13, 6.20).
--
--   **Formalization Note** Basis states are $\mathrm{Fin}(2^n)$ through binary expansion (qubit $i$ is binary digit $i$), and the qubits of $S$ are enumerated increasingly; the condition ranges over every unitary $V$, so it does not depend on this enumeration. "$(V\otimes I)U\sim\mu$" is equality of the pushforward of $\mu$ under $U\mapsto(V\otimes I)U$ with $\mu$. The paper applies the notion to approximate designs; the predicate is stated for any distribution.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 6.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- The operator `V ⊗ I` on `n` qubits: an operator `V` on the qubits of `S ⊆ [n]` tensored with the
identity on the remaining qubits
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 6.1, p.38, PDF p.40).

**Formalization Note** Basis states `x ∈ {0,1}^n` are identified with `Fin (2^n)` by
`finFunctionFinEquiv` (qubit `i` is binary digit `i`), and basis states of the qubits in `S` with
`Fin (2^|S|)` through the increasing enumeration `S.orderIsoOfFin` of `S`. The entry
`(V ⊗ I)_{x,x'}` is `V_{x|_S, x'|_S}` when `x` and `x'` agree outside `S`, and `0` otherwise. -/
def tensorId {n : ℕ} (S : Finset (Fin n)) (V : Matrix (Fin (2 ^ S.card)) (Fin (2 ^ S.card)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun a b =>
    let xa : Fin n → Fin 2 := finFunctionFinEquiv.symm a
    let xb : Fin n → Fin 2 := finFunctionFinEquiv.symm b
    if ∀ i, i ∉ S → xa i = xb i then
      V (finFunctionFinEquiv (fun j : Fin S.card => xa (S.orderIsoOfFin rfl j)))
        (finFunctionFinEquiv (fun j : Fin S.card => xb (S.orderIsoOfFin rfl j)))
    else 0

open Classical in
/-- Left multiplication `U ↦ M U` on `U(N)`.

**Formalization Note** The fallback `U` is used only when `M U` is not unitary; for a unitary `M`
(such as `V ⊗ I` with `V` unitary) this never happens, so this is `U ↦ M U`. -/
noncomputable def leftMulOrSelf {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  if h : M * (U : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ then ⟨_, h⟩ else U

/-- Invariance of a distribution `μ` on `U(2^n)` under `U ↦ (V ⊗ I) U` for every fixed unitary `V` on
the qubits of `S` (Hung, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 6.1, p.38, PDF p.40). -/
def IsLocallyInvariantOn {n : ℕ} (S : Finset (Fin n)) (μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) :
    Prop :=
  ∀ V : Matrix.unitaryGroup (Fin (2 ^ S.card)) ℂ,
    μ.map (leftMulOrSelf (tensorId S (V : Matrix (Fin (2 ^ S.card)) (Fin (2 ^ S.card)) ℂ))) = μ

/-- **Definition 6.1** (locally invariant design)
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 6.1, p.38, PDF p.40).
A distribution `μ` on `n`-qubit unitaries is `m`-locally invariant if there is a set `S ⊆ [n]` of
`m` qubits such that, for `U ∼ μ`, `(V ⊗ I) U ∼ μ` for every fixed unitary `V` acting on the qubits
in `S`.

**Formalization Note** `μ` is a measure on `U(2^n)` (`Matrix.unitaryGroup (Fin (2^n)) ℂ`, published
Borel σ-algebra); "`(V ⊗ I) U ∼ μ`" is equality of the pushforward of `μ` under `U ↦ (V ⊗ I) U`
with `μ`. The condition quantifies over every `V`, so it does not depend on the enumeration of `S`
used by `tensorId`. The paper applies the notion to approximate designs; the predicate is stated for
any distribution. -/
def IsLocallyInvariant {n : ℕ} (m : ℕ) (μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : Prop :=
  ∃ S : Finset (Fin n), S.card = m ∧ IsLocallyInvariantOn S μ

end Supplement

end RQCMoments


