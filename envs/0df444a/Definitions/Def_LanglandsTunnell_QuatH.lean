-- Prove2me | Definitions.Def_LanglandsTunnell_QuatH
-- name    : LanglandsTunnell_QuatH
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/db28e9d9-589f-5840-b744-7bd0b33c0f92
-- title:
--   Determinant-one and quaternionic subgroups and their fixed fields
-- statement:
--   Throughout, $L$ is a number field and $e$ is a chosen group isomorphism $(L \simeq_{\mathbb Q} L) \cong \mathrm{GL}_2(\mathbb{Z}/3)$. The abbreviation `fixFld H`, for a subgroup $H$ of the automorphism group of $L$ over $\mathbb{Q}$, is Mathlib's fixed-field construction `FixedPoints.intermediateField`, viewed as an intermediate field of $\mathbb{Q} \subseteq L$; `fixFld_le_fixFld_of_le` records that this construction is order-reversing in $H$.
--
--   Two subgroups are defined. First, `detKer e` is the kernel of the homomorphism obtained by composing $e$ with the determinant $\mathrm{GL}_2(\mathbb{Z}/3) \to (\mathbb{Z}/3)^\times$; `mem_detKer_iff` restates membership as the condition that the underlying $2 \times 2$ matrix of $e\gamma$ have determinant $1$, so `detKer e` is the preimage $e^{-1}(\mathrm{SL}_2(\mathbb{Z}/3))$, and it is registered as a normal subgroup. Second, `quatH e` is the intersection `sylowH e ⊓ detKer e`, where `sylowH e` consists of those $\gamma$ for which the matrix of $e\gamma$ is the entrywise reduction, along the ring homomorphism $\mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ sending $\sqrt{-2} \mapsto -1$, of one of the sixteen explicitly listed matrices `P16` over $\mathbb{Z}[\sqrt{-2}]$. The inclusions `quatH e ≤ sylowH e` and `quatH e ≤ detKer e` are recorded, together with the resulting inclusions of fixed fields $L^{\mathrm{sylowH}\,e} \subseteq L^{\mathrm{quatH}\,e}$ and $L^{\mathrm{detKer}\,e} \subseteq L^{\mathrm{quatH}\,e}$.
--
--   The remaining declarations equip these inclusions with algebra structures, and with the compatibilities over $\mathbb{Q}$ and over $L$, so that both fixed-field pairs form towers; the closing examples check that the induced algebra structures on the rings of integers, and their integrality, are available from these. No statement here asserts an order, index or degree; such facts belong to the octahedral case and are proved elsewhere.
--
--   **Relation to Mathlib.** `fixFld` is an abbreviation for Mathlib's `FixedPoints.intermediateField`; `detKer` is the kernel of a composite of Mathlib's determinant homomorphism on `GL (Fin 2) (ZMod 3)` with `e`. The subgroups `sylowH` and `quatH`, defined via the explicit lists of matrices over $\mathbb{Z}[\sqrt{-2}]$, are the project's own.
--
--   **Where it is used.** These subgroups and fixed fields organise the octahedral situation used in the Langlands–Tunnell step: the $3$-adic mod $3$ representation attached to the Frey curve has projective image in $\mathrm{GL}_2(\mathbb{F}_3)$, and the base-change argument is carried out along the tower formed by the fixed field of a $2$-Sylow-type subgroup, the fixed field of the determinant-one subgroup, and the fixed field of their intersection. The algebra and scalar-tower instances provided here are what allow base change of automorphic forms to be formed across both pairs of fields and their rings of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_QuatH.lean

import Definitions.Def_LanglandsTunnell_SylowH
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]

abbrev fixFld (H : Subgroup (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L :=
  FixedPoints.intermediateField (↥H)

theorem fixFld_le_fixFld_of_le {H H' : Subgroup (L ≃ₐ[ℚ] L)} (h : H' ≤ H) :
    fixFld H ≤ fixFld H' := by
  intro x hx
  rw [fixFld, FixedPoints.mem_intermediateField_iff] at hx ⊢
  exact fun g => hx ⟨g.1, h g.2⟩

def detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  (Matrix.GeneralLinearGroup.det.comp e.toMonoidHom).ker

theorem mem_detKer_iff (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (γ : L ≃ₐ[ℚ] L) :
    γ ∈ detKer e ↔
      ((e γ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  rw [detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Units.val_eq_one]
  rfl

instance detKer_normal (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : (detKer e).Normal := by
  unfold detKer; infer_instance

def quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  sylowH e ⊓ detKer e

theorem quatH_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ sylowH e :=
  inf_le_left

theorem quatH_le_detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ detKer e :=
  inf_le_right

theorem fixFld_sylowH_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_sylowH e)

theorem fixFld_detKer_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (detKer e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_detKer e)

section TowerInstances

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldQuatH :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldSylowH_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldSylowH_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_quatH e) x).symm)

noncomputable instance algebra_fixFldDetKer_fixFldQuatH :
    Algebra ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_detKer_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldDetKer_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldDetKer_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_detKer_le_fixFld_quatH e) x).symm)

end TowerInstances

section SynthProbe

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))
noncomputable example : Algebra (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example : Algebra (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
end SynthProbe

end LanglandsTunnell


