-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:01:08.073035+00:00
-- url     : https://prove2.me/theorems/597920c3-a22f-5f12-a52c-c026d4c8071e
-- title:
--   Statements Stabilizer Levi
-- statement:
--   Definitions and structural lemmas for Statements Stabilizer Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsStabilizerLevi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal
noncomputable section
section Radical
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
def unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w ∧ ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w}
  one_mem' w := ⟨by simp, fun z _ => ⟨0, by simp⟩⟩
  mul_mem' {a b} ha hb w := by
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, (hb w).1,
        (ha w).1]
    · obtain ⟨c, hc⟩ := (hb w).2 z hz
      obtain ⟨d, hd⟩ := (ha w).2 z hz
      refine ⟨d + c, ?_⟩
      simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hc,
        Matrix.mulVec_add, Matrix.mulVec_smul, hd, (ha w).1, add_smul]
      abel
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hx : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x₀ w = vecAt v x₀ w := by
      conv_lhs => rw [← (ha w).1]
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    refine ⟨hx, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := (ha w).2 z hz
    refine ⟨-c, ?_⟩
    have := congrArg ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ ·) hc
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hx] at this
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← this]
omit [NumberField E] in
theorem mem_unipRadical {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ unipRadical h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w :=
  Iff.rfl
omit [NumberField E] in

theorem isClosed_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (unipRadical h v x₀ : Set (archUnitary h v)) := by
  have hc : ∀ w, Continuous fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
  have : (unipRadical h v x₀ : Set (archUnitary h v)) = ⋂ w, ({g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} ∩
      ⋂ z ∈ {z : ι → ℂ | star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0},
        (fun g : archUnitary h v => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z - z) ⁻¹'
          (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ))) := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRadical, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, Submodule.mem_span_singleton]
    refine forall_congr' fun w => and_congr Iff.rfl (forall_congr' fun z => imp_congr_right
      fun _ => ⟨fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩⟩)
  rw [this]
  refine isClosed_iInter fun w => (isClosed_eq ((hc w).matrix_mulVec continuous_const)
    continuous_const).inter (isClosed_biInter fun z _ => ?_)
  exact (Submodule.closed_of_finiteDimensional _).preimage
    (((hc w).matrix_mulVec continuous_const).sub continuous_const)
instance locallyCompactSpace_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (unipRadical h v x₀) :=
  (isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance secondCountableTopology_unipRadical (h : HermitianForm F E W) (v : Basis ι E W)
    (x₀ : W) : SecondCountableTopology (unipRadical h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _
end Radical
section Structure
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def StabilizerLevi.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∀ (n : ℕ) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
    ∃ (i : archUnitary h' v' →* vecFixGroup h v x₀) (q : vecFixGroup h v x₀ →* archUnitary h' v'),
      Continuous i ∧ Continuous q ∧ (∀ m, q (i m) = m) ∧
      (∀ g, q g = 1 ↔ (g : archUnitary h v) ∈ unipRadical h v x₀) ∧
      (∀ m, ((i m : vecFixGroup h v x₀) : archUnitary h v) ∈ vecFixGroup h v w₀) ∧
      ∀ (γ : h.unitaryGroup) (m : h'.unitaryGroup), γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        ((i (archEmbed h' v' m) : vecFixGroup h v x₀) : archUnitary h v) = archEmbed h v γ
def UnipotentModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure],
    ∀ g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀,
      μ.map (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) = μ.map Subtype.val
def UnipotentCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ C : Set (unipRadical h v x₀), IsCompact C ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧ δ * n ∈ C
def CongruenceLift.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∃ (D' : ℕ) (La' : AddSubgroup (hypComplement h x₀ w₀)) (G'' : Subgroup h'.unitaryGroup),
      IsDIntegral h' D' La' ∧ G'' ≤ latticeStab h' La' ∧ G''.relIndex (latticeStab h' La') ≠ 0 ∧
      ∀ m ∈ G'', ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        γ ∈ latticeStab h La
end Structure
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


