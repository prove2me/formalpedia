-- Prove2me | Definitions.Def_QThermalClassical_Supplement_STAB
-- name    : QThermalClassical_Supplement_STAB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:37:15.380644+00:00
-- url     : https://prove2.me/theorems/fd8efd04-b9bf-4e8f-a457-9a3b21e7ec19
-- title:
--   Pauli group, pure stabilizer states and $\mathrm{STAB}_n$
-- statement:
--   The **Pauli group** $\mathcal P_n$ consists of the operators $i^jP$ with $j\in\{0,1,2,3\}$ and $P$ a Pauli string. A unit vector $|\psi\rangle\in(\mathbb C^2)^{\otimes n}$ is a **stabilizer state** (Definition 2.1, eq. (8)) if there is an abelian subgroup $S\le\mathcal P_n$ with
--   $$
--   -I\notin S,\qquad |S|=2^n,\qquad g|\psi\rangle=|\psi\rangle\ \ \forall g\in S .
--   $$
--   $\mathrm{STAB}_n$ is the convex hull of the projectors $|\psi\rangle\langle\psi|$ of pure stabilizer states; a state **has magic** if it is not in $\mathrm{STAB}_n$.
--
--   **Formalization Note** $S$ is a subset of $\mathcal P_n$ containing $I$, closed under multiplication and pairwise commuting; since $\mathcal P_n$ is a finite group this is an abelian subgroup. The convex hull is the plain (finite) one over $\mathbb R$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, eq. (8), p.11

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The Pauli group `P_n = {i^j P : j ∈ {0,1,2,3}, P a Pauli string}` on the qubits `Q`, as a
set of operators.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, eq. (8), p.11. -/
def pauliGroup (Q : Type) [Fintype Q] : Set (Op Q) :=
  {M | ∃ (j : Fin 4) (P : PauliWord Q), M = (Complex.I ^ (j : ℕ)) • pauliOp P}

/-- A pure stabilizer state (Definition 2.1, eq. (8)): a unit vector `|ψ⟩ ∈ (ℂ²)^{⊗Q}` for which
there is an abelian subgroup `S ≤ P_n` with `−I ∉ S`, `|S| = 2^n` and `g|ψ⟩ = |ψ⟩` for all
`g ∈ S`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, eq. (8), p.11.

**Formalization Note.** `S` is a subset of `pauliGroup Q` containing `I`, closed under
multiplication and pairwise commuting; since `P_n` is a finite group, a nonempty
multiplicatively closed subset is a subgroup. `n` is `Fintype.card Q`. -/
def IsStabilizerState {Q : Type} [Fintype Q] [DecidableEq Q] (ψ : (Q → Bool) → ℂ) : Prop :=
  ∑ a, ‖ψ a‖ ^ 2 = 1 ∧
  ∃ S : Set (Op Q), S ⊆ pauliGroup Q ∧ (1 : Op Q) ∈ S ∧
    (∀ g ∈ S, ∀ h ∈ S, g * h ∈ S) ∧ (∀ g ∈ S, ∀ h ∈ S, Commute g h) ∧
    (-1 : Op Q) ∉ S ∧ S.ncard = 2 ^ Fintype.card Q ∧
    ∀ g ∈ S, Matrix.mulVec g ψ = ψ

/-- `STAB_n`, the convex hull of the pure `n`-qubit stabilizer states `|ψ⟩⟨ψ|`. A state *has
magic* when it is not in `STAB_n`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, p.11.

**Formalization Note.** The plain convex hull over `ℝ` (finite convex combinations), as in the
definition of `Sep_n`; `|ψ⟩⟨ψ|` is `Matrix.vecMulVec ψ (star ψ)`. -/
def STAB {Q : Type} [Fintype Q] [DecidableEq Q] : Set (Op Q) :=
  convexHull ℝ {ρ : Op Q | ∃ ψ : (Q → Bool) → ℂ, IsStabilizerState ψ ∧
    ρ = Matrix.vecMulVec ψ (star ψ)}

end QThermalClassical.Supplement


