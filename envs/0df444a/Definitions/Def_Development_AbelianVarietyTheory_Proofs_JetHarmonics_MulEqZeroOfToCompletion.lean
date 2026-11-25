-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MulEqZeroOfToCompletion
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_MulEqZeroOfToCompletion
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:27:42.840802+00:00
-- url     : https://prove2.me/theorems/ad6ae717-42f5-4da3-b6ca-9a359823ab3e
-- title:
--   Mul Eq Zero Of To Completion
-- statement:
--   Definitions and structural lemmas for Mul Eq Zero Of To Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MulEqZeroOfToCompletion.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_map_comp
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_HodgeTateCompare_finite_projective_of_smooth
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_TorusNil_exists_retraction
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace GlobalTheory.EigenLieCompare
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare
section General
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {R : Type} [CommRing R] (α : RingAct G R)
theorem isEig_iff (τ : R →+* O) (x : LieG G) :
    IsEig G α τ x ↔ ∀ a : R, x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1 :=
  forall_congr' fun _ => Subtype.ext_iff
def eigEquiv (τ : R →+* O) : LieTau G α τ ≃ LieEig α τ :=
  Equiv.subtypeEquivRight (isEig_iff α τ)
def funEquiv (τ : R →+* O) : (LieTau G α τ → O) ≃ₗ[O] (LieEig α τ → O) :=
  LinearEquiv.funCongrLeft O O (eigEquiv α τ).symm
theorem map_map_restr (τ : R →+* O) (S : Submodule O (LieG G → O)) :
    (S.map (restr G α τ)).map (funEquiv α τ).toLinearMap = S.map (restrictEig α τ) := by
  rw [← Submodule.map_comp]
  rfl
theorem restrictEig_mem (τ : R →+* O) {f : LieG G → O} (hf : f ∈ omega G) :
    restrictEig α τ f ∈ omegaEig α τ := by
  refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
  · have := hf.1 x.1 y.1 (h ▸ z.1.2)
    show f z.1 = f x.1 + f y.1
    rw [← this]; congr 1; exact Subtype.ext h
  · have := hf.2 c x.1 (h ▸ z.1.2)
    show f z.1 = c * f x.1
    rw [← this]; congr 1; exact Subtype.ext h
theorem map_omTau_le (τ : R →+* O) :
    (omTau G α τ).map (funEquiv α τ).toLinearMap ≤ omegaEig α τ := by
  rw [omTau, map_map_restr]
  rintro _ ⟨f, hf, rfl⟩
  exact restrictEig_mem α τ hf
end General
section Local
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)
theorem lie_ext {x y : Lie G} (h : (lieEquiv G x).1 = (lieEquiv G y).1) : x = y :=
  (lieEquiv G).injective (Subtype.ext h)
def eigSub (τ : R →+* O) : Submodule O (Lie G) where
  carrier := {x | ∀ a : R, (lieEquiv G x).1 ≫ α.act a = (lieEquiv G (τ a • x)).1}
  add_mem' := fun {x y} hx hy a => by
    haveI := α.hom a
    rw [smul_add, lieEquiv_add, lieEquiv_add, ← hx a, ← hy a, MonObj.mul_comp]
  zero_mem' := fun a => by
    haveI := α.hom a
    have h : (lieEquiv G 0).1 = 1 := by
      have := lieEquiv_add (G := G) 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [smul_zero, h, MonObj.one_comp]
  smul_mem' := fun c x hx a => by
    rw [smul_comm, lieEquiv_smul, lieEquiv_smul c, ← hx a, Category.assoc]
def subEquiv (τ : R →+* O) : eigSub α τ ≃ LieEig α τ :=
  (lieEquiv G).subtypeEquiv fun x => forall_congr' fun a => by rw [lieEquiv_smul]
def ofDual (τ : R →+* O) : Module.Dual O (eigSub α τ) →ₗ[O] (LieEig α τ → O) where
  toFun F x := F ((subEquiv α τ).symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem ofDual_apply (τ : R →+* O) (F : Module.Dual O (eigSub α τ)) (x : eigSub α τ) :
    ofDual α τ F (subEquiv α τ x) = F x :=
  congrArg F ((subEquiv α τ).symm_apply_apply x)
theorem range_ofDual (τ : R →+* O) : LinearMap.range (ofDual α τ) = omegaEig α τ := by
  ext g
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
    · obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
      obtain ⟨y, rfl⟩ := (subEquiv α τ).surjective y
      obtain ⟨z, rfl⟩ := (subEquiv α τ).surjective z
      have : z = x + y := Subtype.ext (lie_ext (h.trans (lieEquiv_add x.1 y.1).symm))
      rw [ofDual_apply, ofDual_apply, ofDual_apply, this, map_add]
    · obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
      obtain ⟨z, rfl⟩ := (subEquiv α τ).surjective z
      have : z = c • x := Subtype.ext (lie_ext (h.trans (lieEquiv_smul c x.1).symm))
      rw [ofDual_apply, ofDual_apply, this, map_smul, smul_eq_mul]
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨⟨fun x => g (subEquiv α τ x), fun x y => h₁ _ _ _ (lieEquiv_add x.1 y.1)⟩,
      fun c x => h₂ _ _ _ (lieEquiv_smul c x.1)⟩, funext fun x => ?_⟩
    exact congrArg g ((subEquiv α τ).apply_symm_apply x)
end Local
section Valuation
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)
theorem exists_retraction {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {M : Type}
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (hN : ∀ (c : O) (x : M), c ≠ 0 → c • x ∈ N → x ∈ N) :
    ∃ r : M →ₗ[O] N, r ∘ₗ N.subtype = LinearMap.id := by
  have h1 : Submodule.torsion O (M ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
    exact (Submodule.Quotient.mk_eq_zero N).2 (hN _ x (nonZeroDivisors.coe_ne_zero c) hc)
  haveI : Module.Flat O (M ⧸ N) := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 h1
  haveI : Module.Free O (M ⧸ N) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hmem : ∀ x, (LinearMap.id - s ∘ₗ N.mkQ : M →ₗ[O] M) x ∈ N := fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this,
      sub_self]
  refine ⟨(LinearMap.id - s ∘ₗ N.mkQ).codRestrict N hmem, ?_⟩
  ext x
  simp [(Submodule.Quotient.mk_eq_zero N).2 x.2]
variable {O : Type} [CommRing O] [IsDomain O] [ValuationRing O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)
theorem eigSub_saturated (τ : R →+* O) (c : O) (x : Lie G) (hc : c ≠ 0)
    (hx : c • x ∈ eigSub α τ) : x ∈ eigSub α τ := by
  intro a
  obtain ⟨y, hy⟩ := (lieEquiv G).surjective (dAct α a (lieEquiv G x))
  have hy' : (lieEquiv G y).1 = (lieEquiv G x).1 ≫ α.act a := congrArg Subtype.val hy
  have h : c • y = c • τ a • x := by
    refine lie_ext ?_
    rw [smul_comm, ← hx a, lieEquiv_smul, lieEquiv_smul, hy', Category.assoc]
  have h' : y = τ a • x := LinearMap.ext fun m => mul_left_cancel₀ hc (LinearMap.congr_fun h m)
  rw [← hy', h']
variable [Smooth G.hom]
theorem exists_retraction_eigSub (τ : R →+* O) :
    ∃ r : Lie G →ₗ[O] eigSub α τ, r ∘ₗ (eigSub α τ).subtype = LinearMap.id := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  exact exists_retraction _ (eigSub_saturated α τ)
theorem map_omTau (τ : R →+* O) :
    (omTau G α τ).map (funEquiv α τ).toLinearMap = omegaEig α τ := by
  refine le_antisymm (map_omTau_le α τ) ?_
  rw [omTau, map_map_restr, ← range_ofDual]
  rintro _ ⟨F, rfl⟩
  obtain ⟨r, hr⟩ := exists_retraction_eigSub α τ
  refine ⟨cotangentBidualToTangentFunction G (F ∘ₗ r), range_cotangentBidualToTangentFunction.le ⟨_, rfl⟩, funext fun x => ?_⟩
  obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
  rw [ofDual_apply]
  exact (cotangentBidualToTangentFunction_apply (F ∘ₗ r) x.1).trans (congrArg F (LinearMap.congr_fun hr x))
def omEquiv (τ : R →+* O) : omTau G α τ ≃ₗ[O] omegaEig α τ :=
  (funEquiv α τ).ofSubmodules _ _ (map_omTau α τ)
def cokerEquiv (p : ℕ) (τ : R →+* O) :
    (omTau G α τ ⧸ (htTau G α p τ).comap (omTau G α τ).subtype) ≃ₗ[O]
      (omegaEig α τ ⧸ htEig α p τ) :=
  Submodule.Quotient.equiv _ _ (omEquiv α τ) (by
    ext f
    obtain ⟨f, rfl⟩ := (omEquiv α τ).surjective f
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_comap, htEig,
      Submodule.mem_comap, ← map_map_restr, Submodule.mem_map_equiv]
    exact Iff.of_eq (congrArg (· ∈ _) ((funEquiv α τ).symm_apply_apply f.1).symm))
end Valuation
section Places
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]
abbrev plId (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) : Ideal (PadicOrder p E) :=
  w.asIdeal.map (toPadic p E)
end Places
section Completion
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]
  {w : HeightOneSpectrum (𝓞 E)}
variable [Algebra ℤ_[p] (Ow w)]
end Completion
section Conj
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem conjInt_conjInt (a : 𝓞 E) : conjInt E (conjInt E a) = a := by
  ext
  simp [conjInt]
@[reducible] def conjStar (E : Type) [Field E] [NumberField E] [IsCMField E] :
    StarRing (𝓞 E) where
  star := conjInt E
  star_involutive := conjInt_conjInt
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b
variable [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = conjInt E a)
include hs
variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O] (hv : v.Integers O) (hp : v (p : C) < 1)
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
  (α : RingAct G (𝓞 E))
include hv hp
end Conj
section TorusAction
open GlobalTheory.SplitTorus GlobalTheory.SemiRigid
end TorusAction
end GlobalTheory.EigenLieCompare


