-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:45.510497+00:00
-- url     : https://prove2.me/theorems/340e92cc-27c1-4634-9bd2-1c8ede1e69e0
-- title:
--   Abs Norm Discr Ideal Of Le
-- statement:
--   Definitions and structural lemmas for Abs Norm Discr Ideal Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormDiscrIdealOfLe.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_mem_of_smul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem IsStep.relIndex {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V}
    (S : IsStep P A B y) : A.toAddSubgroup.relIndex B.toAddSubgroup = Ideal.absNorm P := by
  classical
  let f : 𝓞 K →+ B.toAddSubgroup :=
    { toFun := fun c => ⟨c • y, B.smul_mem c S.mem⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp [add_smul] }
  let g : 𝓞 K →+ B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp f
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨c, hc⟩ := S.gen x.1 x.2
    refine ⟨c, ?_⟩
    simp only [g, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [f, neg_add_eq_sub] using hc
  have hker : g.ker = P.toAddSubgroup := by
    ext c
    simp only [AddMonoidHom.mem_ker, g, f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ⟨fun h => S.mem_of_smul_mem hP h, fun h => S.smul c h⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker,
    Ideal.absNorm_apply]
  rfl
end Formalism.HermitianLattices.Ext.L3.BallB


