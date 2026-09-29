-- Prove2me | Definitions.Def_LocalLanglands_IntegralSubgroupCompact
-- name    : LocalLanglands_IntegralSubgroupCompact
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/85f26ded-8e2a-5b91-aca7-87ccb32e01a1
-- title:
--   Compactness of GL₂ over a compact ring; GL₂(ℤ_p)
-- statement:
--   Four results on compactness of two-by-two general linear groups. First, for arbitrary index types $m,n$ and a compact topological space $R$, the matrix space `Matrix m n R` is compact, being the function space $m \to n \to R$ with the product topology; this is registered as an instance. Secondly, `gl2_compactSpace`: if $R$ is a commutative topological ring that is Hausdorff and compact, then $\mathrm{GL}_2(R)$, realised in Lean as the units of the matrix ring with its subspace-of-$M_2(R)\times M_2(R)$ topology, is a compact space. Thirdly, `isCompact_coe_integralSubgroup`: let $R$ be such a ring, let $K$ be a field equipped with a topology and an $R$-algebra structure whose structure map $R \to K$ is continuous; then the underlying subset of $\mathrm{GL}_2(K)$ attached to [`LocalGL2.integralSubgroup R K`](../def/LocalLanglands_LocalHeckeInstance.html#L13) is compact. Here `integralSubgroup R K` is by definition the image (range) of the group homomorphism $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced entrywise by $R \to K$, so it consists of those $x \in \mathrm{GL}_2(K)$ admitting a preimage in $\mathrm{GL}_2(R)$, i.e. having entries from $R$ together with an inverse of the same kind; compactness follows since it is the continuous image of a compact space. Finally, the two specialisations to $R = \mathbb{Z}_p$, $K = \mathbb{Q}_p$ for a prime $p$: the subset $\mathrm{GL}_2(\mathbb{Z}_p) \subseteq \mathrm{GL}_2(\mathbb{Q}_p)$ is compact, and the corresponding subgroup is a compact space in its subtype topology.
--
--   **Relation to Mathlib.** The topology and compactness of the unit group are taken from Mathlib's instances for units of a topological ring, and `Matrix.GeneralLinearGroup.map` is Mathlib's entrywise base-change homomorphism; the subgroup [`LocalGL2.integralSubgroup`](../def/LocalLanglands_LocalHeckeInstance.html#L13), defined as the range of that homomorphism, is the project's own notion.
--
--   **Where it is used.** Together with the corresponding openness statement, these results exhibit $\mathrm{GL}_2(\mathbb{Z}_p)$ as a compact open subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$, which is what is needed to normalise Haar measure and to make sense of local Hecke operators attached to double cosets of this subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean

import Mathlib
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FLT.SpectralSide

instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (Matrix m n R) :=
  inferInstanceAs <| CompactSpace (m → n → R)

theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K))) := by
  haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

theorem isCompact_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) :=
  isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val

theorem compactSpace_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    CompactSpace (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :=
  isCompact_iff_compactSpace.mp (isCompact_coe_integralSubgroup_padic p)

end FLT.SpectralSide


