-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
-- name    : Development_AbelianVarietyTheory_Definitions_HermitianLattices_TraceFormBilinSeparatingLeftIff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:30.983499+00:00
-- url     : https://prove2.me/theorems/211b4a1d-5a3b-5c6b-93b7-1da40c4ced53
-- title:
--   Trace Form Bilin Separating Left Iff
-- statement:
--   Definitions and structural lemmas for Trace Form Bilin Separating Left Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/TraceFormBilinSeparatingLeftIff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IsLatticeEmb_extend_apply
import Theorems.Thm_GlobalTheory_exists_isLatticeEmb
import Theorems.Thm_GlobalTheory_trace_cc
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_eq_zero_of_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_single_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IsLatticeEmb.extend_apply
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
noncomputable section
namespace GlobalTheory
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.FD hiding cc_cc cc_sub cc_mul cc_one cc_zero cc_eq_zero
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem eq_zero_of_forall_trace_mul {K : Type} [Field K] [NumberField K] {t : K}
    (h : ∀ a : K, Algebra.trace ℚ K (a * t) = 0) : t = 0 :=
  (traceForm_nondegenerate ℚ K).1 t fun a => by rw [Algebra.traceForm_apply, mul_comm]; exact h a
theorem herm_single_single (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  rw [herm_single_right]; simp
theorem herm_injective {G G' : Matrix (Fin r) (Fin r) E} (h : ∀ x y, herm G x y = herm G' x y) :
    G = G' := by
  ext a b
  rw [← herm_single_single G, h, herm_single_single]
theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ G *ᵥ fun b => cc (y b) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
def IsConjAdj (B : LinearMap.BilinForm ℚ (Fin r → E)) : Prop :=
  ∀ (a : E) (x y : Fin r → E), B (a • x) y = B x (cc a • y)
theorem EFf_smul_eq_trace (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    EFf ξ0 G (a • x) y = Algebra.trace ℚ E (a * (-ξ0 * herm G x y)) := by
  rw [EFf, herm_smul_left, mul_left_comm]
theorem traceFormBilin_isConjAdj (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) : IsConjAdj (traceFormBilin ξ0 G) :=
  EFf_smul_left ξ0 G
theorem EFf_swap {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : EFf ξ0 G y x = -EFf ξ0 G x y := by
  rw [EFf, EFf, ← trace_cc, cc_mul, cc_neg, hξ, herm_conj G hG, ← map_neg]
  congr 1; ring
theorem EFf_self {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : EFf ξ0 G x x = 0 := by
  have := EFf_swap hξ hG x x
  linarith
theorem traceFormBilin_isAlt {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) : (traceFormBilin ξ0 G).IsAlt :=
  EFf_self hξ hG
theorem herm_eq_of_EFf_smul {s : ℕ} {ξ0 : E} (h0 : ξ0 ≠ 0) {G : Matrix (Fin r) (Fin r) E}
    {G' : Matrix (Fin s) (Fin s) E} {x y : Fin r → E} {x' y' : Fin s → E}
    (h : ∀ a : E, EFf ξ0 G (a • x) y = EFf ξ0 G' (a • x') y') : herm G x y = herm G' x' y' := by
  have : -ξ0 * herm G x y - -ξ0 * herm G' x' y' = 0 :=
    eq_zero_of_forall_trace_mul fun a => by
      rw [mul_sub, map_sub, ← EFf_smul_eq_trace, ← EFf_smul_eq_trace, h, sub_self]
  exact mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)
theorem traceFormBilin_injective {ξ0 : E} (h0 : ξ0 ≠ 0) :
    Function.Injective (traceFormBilin ξ0 : Matrix (Fin r) (Fin r) E → _) := fun G G' h =>
  herm_injective fun x y => herm_eq_of_EFf_smul h0 fun a => by
    rw [← traceFormBilin_apply, ← traceFormBilin_apply, h]
theorem traceFormBilin_isAlt_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    (G : Matrix (Fin r) (Fin r) E) : (traceFormBilin ξ0 G).IsAlt ↔ ∀ a b, cc (G a b) = G b a := by
  refine ⟨fun h a b => ?_, traceFormBilin_isAlt hξ⟩
  have : -ξ0 * G b a - -ξ0 * cc (G a b) = 0 :=
    eq_zero_of_forall_trace_mul fun t => by
      have h1 := h.neg_eq (t • Pi.single b 1) (Pi.single a 1)
      have h2 : EFf ξ0 G (Pi.single a 1) (t • Pi.single b 1) =
          -Algebra.trace ℚ E (t * (-ξ0 * cc (G a b))) := by
        rw [EFf, herm_smul_right, herm_single_single, ← trace_cc, ← map_neg]
        simp only [cc_mul, cc_neg, cc_cc, hξ]
        congr 1; ring
      rw [traceFormBilin_apply, traceFormBilin_apply, EFf_smul_eq_trace, herm_single_single, h2] at h1
      rw [mul_sub, map_sub, neg_inj.mp h1, sub_self]
  exact (mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)).symm
theorem forall_EFf_eq_zero_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x : Fin r → E) : (∀ y, EFf ξ0 G x y = 0) ↔ ∀ y, herm G x y = 0 := by
  refine ⟨fun h y => ?_, fun h y => by simp [EFf, h]⟩
  have : -ξ0 * herm G x y = 0 :=
    eq_zero_of_forall_trace_mul fun a => by rw [← EFf_smul_eq_trace, EFf_smul_left, h]
  exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr h0)
theorem traceFormBilin_separatingLeft_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).SeparatingLeft ↔ G.det ≠ 0 := by
  constructor
  · intro h hd
    obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    refine hv (h v ((forall_EFf_eq_zero_iff h0 G v).mpr fun y => ?_))
    rw [herm_eq_dotProduct, dotProduct_mulVec, hvG, zero_dotProduct]
  · intro hd v hv
    exact eq_zero_of_herm G hd v ((forall_EFf_eq_zero_iff h0 G v).mp hv)
theorem traceFormBilin_nondegenerate_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).Nondegenerate ↔ G.det ≠ 0 := by
  rw [← traceFormBilin_separatingLeft_iff h0]
  exact ⟨fun h => h.1, LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft⟩
def traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) : K :=
  ((Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)).symm f
theorem trace_mul_traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) (a : K) :
    Algebra.trace ℚ K (a * traceRep f) = f a := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _
def skewGram (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b =>
    (-ξ0)⁻¹ * traceRep (B.flip (Pi.single b 1) ∘ₗ LinearMap.single ℚ (fun _ : Fin r => E) a)
omit [IsCMField E] in

theorem trace_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) (B : LinearMap.BilinForm ℚ (Fin r → E))
    (a b : Fin r) (t : E) :
    Algebra.trace ℚ E (t * (-ξ0 * skewGram ξ0 B a b)) = B (Pi.single a t) (Pi.single b 1) := by
  rw [skewGram, Matrix.of_apply, mul_inv_cancel_left₀ (neg_ne_zero.mpr h0), trace_mul_traceRep]
  rfl
theorem IsConjAdj.ext {B B' : LinearMap.BilinForm ℚ (Fin r → E)} (h : IsConjAdj B)
    (h' : IsConjAdj B')
    (hh : ∀ a b t, B (Pi.single a t) (Pi.single b 1) = B' (Pi.single a t) (Pi.single b 1)) :
    B = B' := by
  have key : ∀ a b t u, B (Pi.single a t) (Pi.single b u) = B' (Pi.single a t) (Pi.single b u) := by
    intro a b t u
    have hu : (Pi.single b u : Fin r → E) = cc (cc u) • Pi.single b 1 := by
      rw [cc_cc, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hu, ← h, ← h', ← Pi.single_smul, hh]
  refine LinearMap.pi_ext fun a t => LinearMap.pi_ext fun b u => key a b t u
theorem traceFormBilin_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) : traceFormBilin ξ0 (skewGram ξ0 B) = B := by
  refine (traceFormBilin_isConjAdj _ _).ext hB fun a b t => ?_
  have ht : (Pi.single a t : Fin r → E) = t • Pi.single a 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [← trace_skewGram h0 B, traceFormBilin_apply, ht, EFf_smul_eq_trace, herm_single_single]
theorem skewGram_traceFormBilin {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    skewGram ξ0 (traceFormBilin ξ0 G) = G :=
  traceFormBilin_injective h0 (traceFormBilin_skewGram h0 (traceFormBilin_isConjAdj ξ0 G))
theorem skewGram_herm {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {B : LinearMap.BilinForm ℚ (Fin r → E)} (hB : IsConjAdj B) (halt : B.IsAlt) (a b : Fin r) :
    cc (skewGram ξ0 B a b) = skewGram ξ0 B b a :=
  (traceFormBilin_isAlt_iff h0 hξ _).mp (by rwa [traceFormBilin_skewGram h0 hB]) a b
def hermEquivSkew {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    {G : Matrix (Fin r) (Fin r) E // ∀ a b, cc (G a b) = G b a} ≃
      {B : LinearMap.BilinForm ℚ (Fin r → E) // IsConjAdj B ∧ B.IsAlt} where
  toFun G := ⟨traceFormBilin ξ0 G.1, traceFormBilin_isConjAdj _ _, traceFormBilin_isAlt hξ G.2⟩
  invFun B := ⟨skewGram ξ0 B.1, skewGram_herm h0 hξ B.2.1 B.2.2⟩
  left_inv G := Subtype.ext (skewGram_traceFormBilin h0 G.1)
  right_inv B := Subtype.ext (traceFormBilin_skewGram h0 B.2.1)
section Integral
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup M'] [Module (𝓞 E) M']
def IsIntConjAdj (E : Type) [Field E] [NumberField E] [IsCMField E] {M : Type} [AddCommGroup M]
    [Module (𝓞 E) M] (β : LinearMap.BilinForm ℤ M) : Prop :=
  ∀ (a : 𝓞 E) (x y : M), β (a • x) y = β x (IsCMField.ringOfIntegersComplexConj E a • y)
namespace IsLatticeEmb
variable {φ : M →ₗ[𝓞 E] (Fin r → E)}
def gram (h : IsLatticeEmb φ) (ξ0 : E) (β : LinearMap.BilinForm ℤ M) : Matrix (Fin r) (Fin r) E :=
  skewGram ξ0 (h.extend β)
end IsLatticeEmb
def latticeEF (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) : LinearMap.BilinForm ℤ Λ :=
  have key : ∀ x y : Λ, (((EFf ξ0 G x y).num : ℤ) : ℚ) = traceFormBilin ξ0 G x y := fun x y => by
    obtain ⟨k, hk⟩ := hint x x.2 y y.2
    rw [traceFormBilin_apply, hk, Rat.num_intCast]
  LinearMap.mk₂ ℤ (fun x y => (EFf ξ0 G x y).num)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        LinearMap.smul_apply, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        zsmul_eq_mul]))
section LatticeEF
variable {ξ0 : E} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k)
end LatticeEF
end Integral
section Datum
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {H : Host E}
theorem datum_exists_isLatticeEmb (D : Datum H) :
    ∃ φ : D.La →ₗ[𝓞 E] (Fin (D.p + D.q) → E), IsLatticeEmb φ := by
  have := D.fin
  have := D.proj
  exact exists_isLatticeEmb D.rank
def datumEmb (D : Datum H) : D.La →ₗ[𝓞 E] (Fin (D.p + D.q) → E) :=
  (datum_exists_isLatticeEmb D).choose
theorem datumEmb_isLatticeEmb (D : Datum H) : IsLatticeEmb (datumEmb D) :=
  (datum_exists_isLatticeEmb D).choose_spec
abbrev datumLat (D : Datum H) : Submodule (𝓞 E) (Fin (D.p + D.q) → E) :=
  LinearMap.range (datumEmb D)
def datumEquivLat (D : Datum H) : D.La ≃ₗ[𝓞 E] datumLat D :=
  LinearEquiv.ofInjective _ (datumEmb_isLatticeEmb D).1
@[simp] theorem coe_datumEquivLat (D : Datum H) (x : D.La) :
    (datumEquivLat D x : Fin (D.p + D.q) → E) = datumEmb D x := rfl
def datumGram (D : Datum H) (ξ0 : E) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) E :=
  (datumEmb_isLatticeEmb D).gram ξ0 D.EF
section
variable (D : Datum H) {ξ0 : E}
end
end Datum
namespace SkewModel
def ConjDual (E : Type) [Field E] [NumberField E] [IsCMField E] : Type := Module.Dual ℤ (𝓞 E)
namespace ConjDual
instance : AddCommGroup (ConjDual E) := inferInstanceAs (AddCommGroup (Module.Dual ℤ (𝓞 E)))
def val : ConjDual E ≃ₗ[ℤ] Module.Dual ℤ (𝓞 E) := (AddEquiv.refl _).toIntLinearEquiv
instance : SMul (𝓞 E) (ConjDual E) where
  smul a f := val.symm (val f ∘ₗ LinearMap.mulLeft ℤ (IsCMField.ringOfIntegersComplexConj E a))
@[simp] theorem val_smul (a : 𝓞 E) (f : ConjDual E) (x : 𝓞 E) :
    val (a • f) x = val f (IsCMField.ringOfIntegersComplexConj E a * x) := rfl
@[ext] theorem ext {f g : ConjDual E} (h : ∀ x, val f x = val g x) : f = g :=
  val.injective (LinearMap.ext h)
instance : Module (𝓞 E) (ConjDual E) where
  one_smul f := ext fun x => by simp
  mul_smul a b f := ext fun x => by simp only [val_smul, map_mul]; congr 1; ring
  smul_zero a := ext fun x => by simp
  smul_add a f g := ext fun x => by simp
  add_smul a b f := ext fun x => by simp [add_mul]
  zero_smul f := ext fun x => by simp
instance : Module.Finite ℤ (ConjDual E) := Module.Finite.equiv val.symm
instance : Module.Finite (𝓞 E) (ConjDual E) := Module.Finite.of_restrictScalars_finite ℤ _ _
instance : Module.IsTorsionFree (𝓞 E) (ConjDual E) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a f h
  refine or_iff_not_imp_left.mpr fun ha => ext fun x => ?_
  have ha' : IsCMField.ringOfIntegersComplexConj E a ≠ 0 := by simpa using ha
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ)
    (IsCMField.ringOfIntegersComplexConj E a)).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha')
  have h1 : val (a • f) (c * x) = 0 := by rw [h]; simp
  rw [val_smul, ← mul_assoc, ← hc, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
  simpa [hn] using h1
end ConjDual
def hypForm (E : Type) [Field E] [NumberField E] [IsCMField E] :
    LinearMap.BilinForm ℤ (𝓞 E × ConjDual E) :=
  LinearMap.mk₂ ℤ (fun u v => ConjDual.val v.2 u.1 - ConjDual.val u.2 v.1)
    (fun u u' v => by simp; ring) (fun n u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, LinearMap.smul_apply, smul_sub])
    (fun u v v' => by simp; ring) (fun n u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, LinearMap.smul_apply, smul_sub])
end SkewModel
example {ξ0 : E} (hξ : cc ξ0 = -ξ0) (d : ℚ) (hd : ξ0 ^ 2 = -algebraMap ℚ E d) :
    EFf ξ0 (1 : Matrix (Fin 1) (Fin 1) E) ![1] ![ξ0] = -(d * Module.finrank ℚ E) ∧
      EFf ξ0 (1 : Matrix (Fin 1) (Fin 1) E) ![ξ0] ![1] = d * Module.finrank ℚ E := by
  constructor
  · have : -ξ0 * (1 * -ξ0) = -algebraMap ℚ E d := by rw [← hd]; ring
    rw [EFf, herm_one, Matrix.cons_val_zero, Matrix.cons_val_zero, hξ, this, map_neg,
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm]
  · have : -ξ0 * (ξ0 * 1) = algebraMap ℚ E d := by rw [← neg_inj, ← hd]; ring
    rw [EFf, herm_one, Matrix.cons_val_zero, Matrix.cons_val_zero, cc_one, this,
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_comm]
example : ∃ (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)), ξ0 ≠ 0 ∧ cc ξ0 = -ξ0 ∧
    IsConjAdj B ∧ B.IsAlt ∧ B.Nondegenerate ∧ skewGram ξ0 B = 1 := by
  obtain ⟨ξ0, hξ, h0⟩ := exists_imag (E := E)
  refine ⟨ξ0, traceFormBilin ξ0 1, h0, hξ, traceFormBilin_isConjAdj _ _, traceFormBilin_isAlt hξ fun a b => ?_,
    (traceFormBilin_nondegenerate_iff h0 _).mpr (by simp), skewGram_traceFormBilin h0 _⟩
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]
example : ¬ (traceFormBilin (1 : E) (1 : Matrix (Fin 1) (Fin 1) E)).IsAlt := by
  intro h
  have h1 := h ![1]
  have : -(1 : E) * (1 * 1) = -algebraMap ℚ E 1 := by simp
  rw [traceFormBilin_apply, EFf, herm_one, Matrix.cons_val_zero, cc_one, this, map_neg,
    Algebra.trace_algebraMap] at h1
  have := Module.finrank_pos (R := ℚ) (M := E)
  simp at h1
  omega
example : ¬ IsConjAdj ((Algebra.traceForm ℚ E).compl₁₂ (LinearMap.proj (0 : Fin 1))
    (LinearMap.proj (φ := fun _ : Fin 1 => E) (0 : Fin 1))) := by
  intro h
  obtain ⟨ξ0, hξ, h0⟩ := exists_imag (E := E)
  have : ξ0 + ξ0 = 0 := eq_zero_of_forall_trace_mul fun a => by
    have h1 := h ξ0 ![a] ![1]
    simp only [LinearMap.compl₁₂_apply, LinearMap.proj_apply, Algebra.traceForm_apply,
      Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, hξ, mul_one, map_neg] at h1
    rw [mul_add, map_add]
    rw [mul_comm ξ0 a] at h1
    linarith
  exact h0 (by linear_combination this / 2)
end GlobalTheory


