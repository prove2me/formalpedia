-- Prove2me | Definitions.Def_RainsSep_Distill_IsSeparableSuperop
-- name    : RainsSep_Distill_IsSeparableSuperop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:33.993973+00:00
-- url     : https://prove2.me/theorems/a6e62377-124f-4902-bedf-d3ada1d56fb3
-- title:
--   Separable superoperator from $A_1\otimes A_2$ to $B_1\otimes B_2$
-- statement:
--   Let $A_1,A_2,B_1,B_2$ be finite-dimensional Hilbert spaces. A map $\mathcal P$ from operators on $A_1\otimes A_2$ to operators on $B_1\otimes B_2$ is a **separable superoperator** if it has a Kraus representation by product operators:
--
--   $$
--   \mathcal P(\rho)=\sum_i \big(P_i^{(1)}\otimes P_i^{(2)}\big)\,\rho\,\big(P_i^{(1)}\otimes P_i^{(2)}\big)^\dagger ,\qquad \sum_i \big(P_i^{(1)}\otimes P_i^{(2)}\big)^\dagger\big(P_i^{(1)}\otimes P_i^{(2)}\big)=\mathrm{Id},
--   $$
--
--   with $P_i^{(j)}$ a linear map from $A_j$ to $B_j$, the identity holding for every operator $\rho$. Every protocol of local operations with one- or two-way classical communication is of this form, so bounds for separable superoperators bound all such protocols.
--
--   **Formalization Note** The Kraus family is finite (indexed by $\{0,\dots,m-1\}$); in finite dimension this excludes no separable superoperator. The normalization makes $\mathcal P$ trace preserving; the first tensor factor is Alice's.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, p. 1, Eqs. (5)–(6) and the definition of a separable superoperator; Eq. (13), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RainsSep.Distill

/-- **Separable superoperator.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, p. 1, Eqs. (5)–(6): "a superoperator can always be written in the form ρ ↦ Σ_i A_i ρ A_i†,
(5) where the A_i are linear transformations from V to W such that Σ_i A_i† A_i = Id(V), (6) …
If V = V1 ⊗ V2 and W = W1 ⊗ W2, a separable superoperator is one which has a representation of
the form (5), in which each A_i = A_i(1) ⊗ A_i(2), with A_i(j) a linear transformation from Vj to
Wj." See also Eq. (13), p. 2.

`P` maps operators on `A₁ ⊗ A₂` to operators on `B₁ ⊗ B₂` and equals, on every operator, the
Kraus map `ρ ↦ Σ_i (P₁ i ⊗ P₂ i) ρ (P₁ i ⊗ P₂ i)†` of a normalized family of product operators
(`Σ_i (P₁ i ⊗ P₂ i)† (P₁ i ⊗ P₂ i) = Id`).

**Formalization Note.** The Kraus index set is finite (`Fin m`). In finite dimension this
excludes no separable superoperator: its Choi matrix lies in the finite-dimensional cone of
separable operators, so finitely many product terms suffice (Carathéodory). The first tensor
factor is Alice's. -/
def IsSeparableSuperop {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
    [DecidableEq A₁] [DecidableEq A₂] (P : QAlgorithms.Superop (A₁ × A₂) (B₁ × B₂)) : Prop :=
  ∃ (m : ℕ) (P₁ : Fin m → Matrix B₁ A₁ ℂ) (P₂ : Fin m → Matrix B₂ A₂ ℂ),
    QAlgorithms.IsKrausFamily (fun i => Matrix.kronecker (P₁ i) (P₂ i)) ∧
      ∀ ρ, P ρ = QAlgorithms.krausApply (fun i => Matrix.kronecker (P₁ i) (P₂ i)) ρ

end RainsSep.Distill


