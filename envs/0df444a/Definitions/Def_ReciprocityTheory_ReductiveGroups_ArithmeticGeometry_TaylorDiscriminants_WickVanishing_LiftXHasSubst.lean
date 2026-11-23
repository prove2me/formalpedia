-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:57.30099+00:00
-- url     : https://prove2.me/theorems/a54fab27-da77-46a8-8334-6b81f1e516aa
-- title:
--   Lift XHas Subst
-- statement:
--   Definitions and structural lemmas for Lift XHas Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
def nablaL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) : Module.End k (AA k d) where
  toFun := nabla k B h m u φ
  map_add' G G' := by
    unfold nabla Dx
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c G := by
    unfold nabla Dx
    simp only [Derivation.map_smul, mul_smul_comm, RingHom.id_apply, smul_add, smul_sub, Finset.smul_sum]
def sideE {ι : Type} [Fintype ι] (s : ι → Bool) :
    ι ≃ Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}) :=
  (Equiv.sumCompl (fun l => s l = true)).symm.trans (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
section Bridge
variable {ι : Type} [Fintype ι]
abbrev opL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (i : Fin (Fintype.card {l // s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inl i))).1 (ξ ((sideE s).symm (Sum.inl i))).2
abbrev opR (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inr j))).1 (ξ ((sideE s).symm (Sum.inr j))).2
end Bridge
end ReciprocityTheory.ChartRestriction.G.TB.SCPf


