-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
-- name    : GroundTheory_HeightsAndTheta_Theta_Cartan
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:15.369007+00:00
-- url     : https://prove2.me/theorems/a381a329-9185-4a6d-975d-c18536f9e4a7
-- title:
--   Cartan
-- statement:
--   Definitions and structural lemmas for Cartan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Cartan.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isClosed
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_indefJ_conjTranspose
import Theorems.Thm_GroundTheory_Automorphic_isCompact_maxCompact_of_isClosed
import Theorems.Thm_GroundTheory_Automorphic_mem_maxCompact_indefiniteUnitary
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
theorem mul_indefJ_mul_conjTranspose {g : 𝔐} (hg : gᴴ * J * g = J) : g * J * gᴴ = J := by
  have h1 : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, indefJ_mul_self]
  have h2 : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 h1
  calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
        simp only [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]
theorem sqrt_preservesIndefJ {P : 𝔐} (hP : P.PosDef) (hPJ : Pᴴ * J * P = J) :
    (CFC.sqrt P)ᴴ * J * CFC.sqrt P = J := by
  set S := CFC.sqrt P with hSdef
  have hSpd : S.PosDef := by
    rw [← isStrictlyPositive_iff_posDef] at hP ⊢
    exact IsStrictlyPositive.sqrt _ hP
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hPh : Pᴴ = P := hP.isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg
  have hJh : Jᴴ = J := indefJ_conjTranspose p q
  have hJJ : J * J = 1 := indefJ_mul_self p q
  have hPJ' : P * J * P = J := by rwa [hPh] at hPJ
  have hJPJ : J * P * J = P⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc J * P * J * P = J * (P * J * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJ', hJJ]
  have h1 : CFC.sqrt (J * P * J) = J * S * J := by
    refine CFC.sqrt_unique ?_ ?_
    · calc J * S * J * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
        _ = J * P * J := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J S S, hSS]
    · have := hSpd.posSemidef.conjTranspose_mul_mul_same J
      rw [hJh] at this
      exact this.nonneg
  have h2 : CFC.sqrt P⁻¹ = S⁻¹ := by
    refine CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg
    rw [← Matrix.mul_inv_rev, hSS]
  have h3 : J * S * J = S⁻¹ := by rw [← h1, hJPJ, h2]
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  rw [hSh]
  calc S * J * S = S * (J * S * J) * J := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]
section Polar
local notation "G" => indefiniteUnitaryGroup p q
theorem mul_preservesIndefJ {a b : 𝔐} (ha : aᴴ * J * a = J) (hb : bᴴ * J * b = J) :
    (a * b)ᴴ * J * (a * b) = J := by
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * J * (a * b) = bᴴ * (aᴴ * J * a) * b := by simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]
theorem inv_preservesIndefJ {a : 𝔐} (hu : IsUnit a.det) (ha : aᴴ * J * a = J) :
    a⁻¹ᴴ * J * a⁻¹ = J := by
  calc a⁻¹ᴴ * J * a⁻¹ = a⁻¹ᴴ * (aᴴ * J * a) * a⁻¹ := by rw [ha]
    _ = (a * a⁻¹)ᴴ * J * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
def upqOfMatrix (m : 𝔐) (hm : mᴴ * J * m = J) : G :=
  ⟨⟨m, J * mᴴ * J, by
      calc m * (J * mᴴ * J) = m * J * mᴴ * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [mul_indefJ_mul_conjTranspose hm, indefJ_mul_self],
    by
      calc J * mᴴ * J * m = J * (mᴴ * J * m) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hm, indefJ_mul_self]⟩, hm⟩
@[simp] theorem coe_upqOfMatrix (m : 𝔐) (hm : mᴴ * J * m = J) :
    ((upqOfMatrix m hm : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = m := rfl
theorem continuous_upqOfMatrix {X : Type*} [TopologicalSpace X] {f : X → 𝔐}
    (hf : Continuous f) (hfJ : ∀ x, (f x)ᴴ * J * f x = J) :
    Continuous fun x => upqOfMatrix (f x) (hfJ x) := by
  have h : Continuous fun x => ((upqOfMatrix (f x) (hfJ x) : G) : GL (Fin p ⊕ Fin q) ℂ) :=
    Units.continuous_iff.2
      ⟨hf, (continuous_const.mul hf.matrix_conjTranspose).mul continuous_const⟩
  exact h.subtype_mk _
theorem continuous_coe_indefiniteUnitary :
    Continuous fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) :=
  Units.continuous_val.comp continuous_subtype_val
theorem polarPos_preservesIndefJ (g : G) :
    (polarPos (g : GL (Fin p ⊕ Fin q) ℂ))ᴴ * J * polarPos (g : GL (Fin p ⊕ Fin q) ℂ) = J := by
  set m := ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)
  have hg : mᴴ * J * m = J := g.2
  have hg' : m * J * mᴴ = J := mul_indefJ_mul_conjTranspose hg
  refine sqrt_preservesIndefJ (posDef_conjTranspose_mul_self_GL _) ?_
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc mᴴ * m * J * (mᴴ * m) = mᴴ * (m * J * mᴴ) * m := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hg', hg]
theorem polarUnitary_preservesIndefJ (g : G) :
    (polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ))ᴴ * J * polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ) =
      J :=
  mul_preservesIndefJ g.2 (inv_preservesIndefJ (isUnit_det_of_posDef (polarPos_posDef _))
    (polarPos_preservesIndefJ g))
def cartanPos (p q : ℕ) : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  {s | s.PosDef ∧ sᴴ * indefJ p q * s = indefJ p q}
def cartanMul (ks : maxCompact G × cartanPos p q) : G :=
  (ks.1 : G) * upqOfMatrix ks.2.1 ks.2.2.2
noncomputable def cartanSplit (g : G) : maxCompact G × cartanPos p q :=
  (⟨upqOfMatrix (polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ)) (polarUnitary_preservesIndefJ g),
      polarUnitary_mem (g : GL (Fin p ⊕ Fin q) ℂ)⟩,
    ⟨polarPos (g : GL (Fin p ⊕ Fin q) ℂ), polarPos_posDef _, polarPos_preservesIndefJ g⟩)
noncomputable def cartanHomeomorph : maxCompact G × cartanPos p q ≃ₜ G where
  toFun := cartanMul
  invFun := cartanSplit
  left_inv ks := by
    obtain ⟨⟨k, hk⟩, ⟨s, hs, hsJ⟩⟩ := ks
    have h := polar_unique (g := (cartanMul (⟨k, hk⟩, ⟨s, hs, hsJ⟩) : GL (Fin p ⊕ Fin q) ℂ))
      (k := ((k : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) (p := s) hk hs rfl
    refine Prod.ext (Subtype.ext (Subtype.ext (Units.ext ?_))) (Subtype.ext ?_)
    · exact h.2
    · exact h.1
  right_inv g := Subtype.ext (Units.ext (polarUnitary_mul_polarPos (g : GL (Fin p ⊕ Fin q) ℂ)))
  continuous_toFun := by
    refine Continuous.mul (continuous_subtype_val.comp continuous_fst) ?_
    exact continuous_upqOfMatrix (continuous_subtype_val.comp continuous_snd) _
  continuous_invFun := by
    have hP : Continuous fun g : G => polarPos (g : GL (Fin p ⊕ Fin q) ℂ) :=
      (continuous_polarPos CFC.continuousOn_sqrt).comp continuous_subtype_val
    have hU : Continuous fun g : G => polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ) :=
      continuous_coe_indefiniteUnitary.mul
        (continuousOn_matrix_inv.comp_continuous hP fun g => (polarPos_posDef _).isUnit)
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    exact (continuous_upqOfMatrix hU _).subtype_mk _
end Polar
section MaxCompact
local notation "G" => indefiniteUnitaryGroup p q
theorem isClosed_indefiniteUnitaryGroup : IsClosed (G : Set (GL (Fin p ⊕ Fin q) ℂ)) :=
  (isExpLieAlgebra_indefiniteUnitary p q).isClosed
theorem isCompact_maxCompact_indefiniteUnitary :
    IsCompact ((maxCompact G : Subgroup G) : Set G) :=
  isCompact_maxCompact_of_isClosed isClosed_indefiniteUnitaryGroup
instance : CompactSpace (maxCompact G) :=
  isCompact_iff_compactSpace.1 isCompact_maxCompact_indefiniteUnitary
end MaxCompact
section Blocks
local notation "G" => indefiniteUnitaryGroup p q
theorem indefJ_eq_fromBlocks : J = fromBlocks 1 0 0 (-1) := by
  rw [indefJ, ← fromBlocks_diagonal, diagonal_one, ← diagonal_one, ← diagonal_neg]
  rfl
theorem fromBlocks_preservesIndefJ (a : unitaryGroup (Fin p) ℂ) (b : unitaryGroup (Fin q) ℂ) :
    (fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ))ᴴ * J *
      fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ) = J := by
  have ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 a.2
  have hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 b.2
  rw [indefJ_eq_fromBlocks, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [ha, hb]
theorem fromBlocks_mem_unitaryGroup (a : unitaryGroup (Fin p) ℂ) (b : unitaryGroup (Fin q) ℂ) :
    fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ) ∈
      unitaryGroup (Fin p ⊕ Fin q) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  have ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 a.2
  have hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 b.2
  simp [ha, hb, fromBlocks_one]
def blockDiagK (ab : unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ) : maxCompact G :=
  ⟨upqOfMatrix _ (fromBlocks_preservesIndefJ ab.1 ab.2), fromBlocks_mem_unitaryGroup ab.1 ab.2⟩
theorem coe_blockDiagK (ab : unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ) :
    ((((blockDiagK ab : maxCompact G) : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      fromBlocks (ab.1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (ab.2 : Matrix (Fin q) (Fin q) ℂ) := rfl
theorem toBlocks_mem_unitaryGroup (k : maxCompact G) :
    (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐).toBlocks₁₁ ∈ unitaryGroup (Fin p) ℂ ∧
      (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐).toBlocks₂₂ ∈ unitaryGroup (Fin q) ℂ := by
  obtain ⟨hu, h12, h21⟩ := mem_maxCompact_indefiniteUnitary.1 k.2
  set m := (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)
  have hm : m = fromBlocks m.toBlocks₁₁ 0 0 m.toBlocks₂₂ := by
    rw [← h12, ← h21, fromBlocks_toBlocks]
  have h := mem_unitaryGroup_iff'.1 hu
  rw [star_eq_conjTranspose, hm, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact ⟨mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.1),
    mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.2.2.2)⟩
noncomputable def maxCompactEquivProd :
    unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ ≃ₜ* maxCompact G where
  toFun := blockDiagK
  invFun k := (⟨_, (toBlocks_mem_unitaryGroup k).1⟩, ⟨_, (toBlocks_mem_unitaryGroup k).2⟩)
  left_inv ab := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact toBlocks_fromBlocks₁₁ _ _ _ _
    · exact toBlocks_fromBlocks₂₂ _ _ _ _
  right_inv k := by
    obtain ⟨hu, h12, h21⟩ := mem_maxCompact_indefiniteUnitary.1 k.2
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    rw [coe_blockDiagK]
    simp only
    rw [← h12, ← h21, fromBlocks_toBlocks]
  map_mul' a b := by
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul, coe_blockDiagK, Prod.fst_mul, Prod.snd_mul,
      Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_upqOfMatrix ?_ _) _
    exact Continuous.matrix_fromBlocks (continuous_subtype_val.comp continuous_fst)
      continuous_const continuous_const (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hk : Continuous fun k : maxCompact G => (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) :=
      continuous_coe_indefiniteUnitary.comp continuous_subtype_val
    exact Continuous.prodMk ((hk.matrix_submatrix _ _).subtype_mk _)
      ((hk.matrix_submatrix _ _).subtype_mk _)
end Blocks
section Topology
local notation "G" => indefiniteUnitaryGroup p q
theorem range_coe_indefiniteUnitary :
    Set.range (fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) = {m | mᴴ * J * m = J} := by
  ext m
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hm
    exact ⟨upqOfMatrix m hm, rfl⟩
theorem isClosedEmbedding_coe_indefiniteUnitary :
    Topology.IsClosedEmbedding (fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) := by
  refine ⟨Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [range_coe_indefiniteUnitary]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const
instance : T2Space G := isClosedEmbedding_coe_indefiniteUnitary.isEmbedding.t2Space
instance : LocallyCompactSpace G := isClosedEmbedding_coe_indefiniteUnitary.locallyCompactSpace
instance : SecondCountableTopology G :=
  isClosedEmbedding_coe_indefiniteUnitary.isEmbedding.isInducing.secondCountableTopology
end Topology
end GroundTheory.Heights₂.Theta


