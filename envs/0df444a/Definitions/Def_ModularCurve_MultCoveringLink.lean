-- Prove2me | Definitions.Def_ModularCurve_MultCoveringLink
-- name    : ModularCurve_MultCoveringLink
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/7aab89a8-6bac-53ce-b8b0-07415415d85e
-- title:
--   Link matrices and comparison constant for good families
-- statement:
--   Fix a prime $p$ and $r \in \mathbb{N}$, and work inside $\bar{\mathbb{Q}}(X_0(1\cdot p))$, i.e. the base-changed modular function field `modularFunctionFieldBar (1 * p)` over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $\Phi$ be a good-family context `FamCtx p r`, whose member family $\Phi.t : \mathrm{Fin}\,r \to \bar{\mathbb{Q}}(X_0(p))$ satisfies the predicate `IsEmbBasis (1 * p)` (its second component identifies the $\bar{\mathbb{Q}}$-span of the range with a fixed subspace, the same for every family satisfying the predicate; its first component is a basis of that span indexed by $\mathrm{Fin}\,r$), and let $s$ be any further family satisfying `IsEmbBasis (1 * p)`. The two opening lemmas record that each $s_i$ lies in the span of the range of $\Phi.t$ and each $\Phi.t_j$ in the span of the range of $s$. Consequently one may define two matrices over $\bar{\mathbb{Q}}$: `linkMatrix` has $(i,j)$ entry the $j$-th coordinate of $s_i$ in the basis supplied by $\Phi$.`t_basis`, and `linkMatrixInv` has $(i,j)$ entry the $j$-th coordinate of $\Phi.t_i$ in the basis supplied by $s$; that the second is inverse to the first is not asserted here. `linkBudget` is the infimum, in $\mathbb{N}$, of those $B$ such that for every valuation subring $A \subseteq \bar{\mathbb{Q}}$ lying over $p$ and all $i,j$ both $p^{B}\cdot(\mathtt{linkMatrix})_{ij}$ and $p^{B}\cdot(\mathtt{linkMatrixInv})_{ij}$ belong to $A$ (so $0$ if no such $B$ exists, by the convention for `sInf` on $\mathbb{N}$); the quantification over $A$ is inside, so one budget serves all places above $p$. Finally `compConst` is the real number $4\bigl(\mathtt{linkBudget} + \mathtt{modulusExp}\bigr)$, where `modulusExp` $= 3$; unfolding lemmas for the matrix entries and for `compConst`, and its non-negativity, complete the module.
--
--   **Relation to Mathlib.** The linear algebra used is Mathlib's (`Submodule.span`, `Basis.repr`, `ValuationSubring`, `sInf` on $\mathbb{N}$); the good-family context, the embedding-basis predicate, the link matrices, the budget and the comparison constant are the project's own notions.
--
--   **Where it is used.** These data feed the multiplicative covering theorem for $X_0(p)$ over $\bar{\mathbb{Q}}$, whose statement demands a single real constant and a single integral exponent chosen before the valuation subring above $p$: `compConst` is of the shape required for the proximity comparison clauses, and the link matrices transport chart data from the good family $\Phi.t$ to an arbitrary embedding basis $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MultCoveringLink.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve.MultCovering

section Link

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem mem_span_range_goodFamily (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) (i : Fin r) :
    s i ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range Φ.t) := by
  rw [Φ.t_basis.2, ← hs.2]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem goodFamily_mem_span_range (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) (j : Fin r) :
    Φ.t j ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
  rw [hs.2, ← Φ.t_basis.2]
  exact Submodule.subset_span ⟨j, rfl⟩

noncomputable def linkMatrix (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
  fun i j => (Φ.t_basis.1.repr ⟨s i, mem_span_range_goodFamily Φ s hs i⟩) j

noncomputable def linkMatrixInv (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
  fun i j => (hs.1.repr ⟨Φ.t i, goodFamily_mem_span_range Φ s hs i⟩) j

noncomputable def linkBudget (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : ℕ :=
  sInf {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ i j, (p : AlgebraicClosure ℚ) ^ B * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * linkMatrixInv Φ s hs i j ∈ A}

noncomputable def compConst (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : ℝ :=
  4 * ((linkBudget Φ s hs : ℝ) + (modulusExp : ℝ))

theorem linkMatrix_apply (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) (i j : Fin r) :
    linkMatrix Φ s hs i j = (Φ.t_basis.1.repr ⟨s i, mem_span_range_goodFamily Φ s hs i⟩) j := rfl

theorem linkMatrixInv_apply (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) (i j : Fin r) :
    linkMatrixInv Φ s hs i j = (hs.1.repr ⟨Φ.t i, goodFamily_mem_span_range Φ s hs i⟩) j := rfl

theorem compConst_eq (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) : compConst Φ s hs = 4 * ((linkBudget Φ s hs : ℝ) + (modulusExp : ℝ)) := rfl

theorem compConst_nonneg (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) : 0 ≤ compConst Φ s hs := by
  unfold compConst; positivity

end Link

end ModularCurve.MultCovering


