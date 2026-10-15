-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
-- name    : OAI_Analysis_ForestSpace_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:58:56.928768+00:00
-- url     : https://prove2.me/theorems/03805d70-4b0f-4316-a750-d98e69efa078
-- title:
--   Square-sum bounds for coordinates and for dual vectors, and root-to-vertex path vectors
-- statement:
--   Let $(V,\le)$ be a partially ordered set. Let $T(V)$ be the finitely supported real functions on $V$ with the disjoint-segment norm $\rho$, let $e_v^*$ be the coordinate functionals on its completion $J(V)$, and let $X(V)=\overline{\operatorname{span}}\{e_v^*:v\in V\}\subseteq J(V)^*$. The file contains two inequalities and one definition.
--
--   1. **Coordinates are square-summable.** For every $u\in T(V)$ and every finite $S\subseteq V$,
--   $$
--   \sum_{v\in S}u(v)^2\le\rho(u)^2 .
--   $$
--   2. **Upper $\ell_2$ estimates dualize.** Let $E$ be a real normed space and let $(v_i)_{i\in I}$ be a family in $E$, indexed by an arbitrary set $I$, such that
--   $$
--   \Bigl\|\sum_{i\in S}a_i v_i\Bigr\|\le\Bigl(\sum_{i\in S}a_i^2\Bigr)^{1/2}
--   $$
--   for every finite $S\subseteq I$ and all real coefficients $(a_i)_{i\in I}$. Then for every continuous linear functional $\varphi\in E^*$ and every finite $S\subseteq I$,
--   $$
--   \sum_{i\in S}\varphi(v_i)^2\le\|\varphi\|^2 .
--   $$
--   3. **Path vectors.** Let $v$ be a vertex with finitely many predecessors, meaning $\{w\in V: w\le v\}$ is finite. Its path vector is
--   $$
--   p_v=\sum_{w\le v}e_w^*\in X(V),
--   $$
--   the sum of the coordinate functionals along the path from the root to $v$, including $v$ itself.
--
--   The first inequality says that the formal identity from $(T(V),\rho)$ into $\ell_2(V)$ has norm at most $1$. The second is a dual counterpart for any family with an upper $\ell_2$ estimate, and it controls the coordinates of a dual vector. Path vectors are the tree-indexed elements of $X(V)$. Their differences along the children of a common vertex are the weakly null branches used against asymptotically uniformly convex renormings.
--
--   **Formalization Note** The two inequalities are `coordinate_squares_le` and `dual_vectors_squares_le`; in the latter the upper estimate is stated with `Real.sqrt`. `pathVector v hfin` takes the finiteness proof `hfin` of `Set.Iic v` as an argument and sums `eX w` over `hfin.toFinset`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Coordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateBounds
variable {V : Type} [PartialOrder V]

 theorem coordinate_squares_le (S : Finset V) (u : TestVector V) :
    ∑ v ∈ S, u v ^ 2 ≤ ‖u‖^2 := by
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp))
    S inferInstance (fun v : S => {(v : V)})
    (fun v => isSegment_singleton (v : V))
    (by
      intro i j hij
      apply Finset.disjoint_singleton.mpr
      exact fun he => hij (Subtype.ext he))
  have hh' : (∑ v : S, u (v : V)^2) ≤ ‖u‖^2 := by
    simpa only [segSum,Finset.sum_singleton,TestVector.norm_eq_rho] using hh
  rw [← Finset.sum_coe_sort S (fun v => u v^2)]
  exact hh'

 theorem dual_vectors_squares_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} (v : I → E)
    (h : ∀ (S : Finset I) (a : I → ℝ), ‖∑ i ∈ S, a i • v i‖ ≤ Real.sqrt (∑ i ∈ S, a i^2))
    (φ : StrongDual ℝ E) (S : Finset I) :
    ∑ i ∈ S, (φ (v i))^2 ≤ ‖φ‖^2 := by
  let A : ℝ := ∑ i ∈ S, (φ (v i))^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hroot := Real.sq_sqrt hA
  have hp : φ (∑ i ∈ S, φ (v i) • v i) = A := by
    simp only [map_sum, map_smul, smul_eq_mul, pow_two, A]
  have hh := φ.le_opNorm (∑ i ∈ S, φ (v i) • v i)
  rw [hp, Real.norm_of_nonneg hA] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left
    (h S (fun i => φ (v i))) (norm_nonneg φ))
  change A ≤ ‖φ‖*Real.sqrt A at hh'
  have hr : Real.sqrt A ≤ ‖φ‖ := by
    by_cases hz : Real.sqrt A = 0
    · simp [hz]
    · have hpos : 0 < Real.sqrt A := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      nlinarith
  change A ≤ ‖φ‖^2
  nlinarith [Real.sqrt_nonneg A, norm_nonneg φ]

noncomputable def pathVector (v : V) (hfin : (Set.Iic v).Finite) : X V :=
  ∑ w ∈ hfin.toFinset, eX w

end CoordinateBounds

end

end ForestSpace

end OAI


