-- Prove2me | solution 1 for AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/af3f7831-dcf8-533d-af60-883afc508bef

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NNReal

noncomputable section

namespace P2mSplitDictionary

section PiHom

variable {R : Type*} [CommSemiring R] {W : Type*} [Fintype W] [DecidableEq W]
  {B : W → Type*} [∀ w, CommRing (B w)] [∀ w, Algebra R (B w)]
  {C : Type*} [CommRing C] [IsDomain C] [Algebra R C]
  (χ : (Π w, B w) →ₐ[R] C)

theorem apply_single_one_eq_zero_or_one (w : W) :
    χ (Pi.single w 1) = 0 ∨ χ (Pi.single w 1) = 1 := by
  apply eq_zero_or_one_of_sq_eq_self
  rw [sq, ← map_mul, ← Pi.single_mul, mul_one]

theorem exists_apply_single_one_eq_one : ∃ w, χ (Pi.single w 1) = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ w, χ (Pi.single w 1) = 0 :=
    fun w => (apply_single_one_eq_zero_or_one χ w).resolve_right (h w)
  have hsum : (∑ w, (Pi.single w (1 : B w) : Π w, B w)) = 1 := by
    have := Finset.univ_sum_single (1 : Π w, B w)
    simpa using this
  have h1 := congrArg χ hsum
  rw [map_sum, map_one] at h1
  simp only [h0, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

theorem apply_single_one_eq_zero_of_ne {w₀ w : W} (h0 : χ (Pi.single w₀ 1) = 1) (hw : w ≠ w₀) :
    χ (Pi.single w 1) = 0 := by
  have hprod : (Pi.single w (1 : B w) : Π u, B u) * Pi.single w₀ 1 = 0 := by
    funext u
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hu : u = w
    · subst hu
      rw [Pi.single_eq_of_ne hw, mul_zero]
    · rw [Pi.single_eq_of_ne hu, zero_mul]
  have h := congrArg χ hprod
  rw [map_mul, h0, mul_one, map_zero] at h
  exact h

theorem apply_eq_apply_single {w₀ : W} (h0 : χ (Pi.single w₀ 1) = 1) (x : Π w, B w) :
    χ x = χ (Pi.single w₀ (x w₀)) := by
  have hx : (Pi.single w₀ (x w₀) : Π w, B w) = x * Pi.single w₀ 1 := by
    funext u
    rw [Pi.mul_apply]
    by_cases hu : u = w₀
    · subst hu
      simp
    · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, mul_zero]
  rw [hx, map_mul, h0, mul_one]

def factor (w₀ : W) (h0 : χ (Pi.single w₀ 1) = 1) : B w₀ →ₐ[R] C where
  toFun b := χ (Pi.single w₀ b)
  map_one' := h0
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' r := by
    have h : (algebraMap R (Π w, B w) r) w₀ = algebraMap R (B w₀) r := rfl
    rw [← h, ← apply_eq_apply_single χ h0, AlgHom.commutes]

@[scoped simp] theorem factor_apply (w₀ : W) (h0 : χ (Pi.single w₀ 1) = 1) (b : B w₀) :
    factor χ w₀ h0 b = χ (Pi.single w₀ b) := rfl

theorem apply_eq_factor {w₀ : W} (h0 : χ (Pi.single w₀ 1) = 1) (x : Π w, B w) :
    χ x = factor χ w₀ h0 (x w₀) := by
  rw [factor_apply, ← apply_eq_apply_single χ h0]

end PiHom

section Places

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

scoped instance instFintypeExtension : Fintype (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v

scoped instance instDecidableEqExtension : DecidableEq (v.Extension (𝓞 L)) := Classical.decEq _

theorem liesOver_of_extension (w : v.Extension (𝓞 L)) : w.1.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have h := congrArg HeightOneSpectrum.asIdeal w.2
  exact h.symm

def Φ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v)

theorem semiLocalHomeomorph_apply (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.semiLocalHomeomorph K L v x = Φ K L v x := rfl

theorem mem_semiLocalIntegers_iff (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), Φ K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_apply,
    AutomorphicForm.piIntegers, Set.mem_univ_pi]
  rfl

theorem semiLocalPlaceComponent_eq (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalPlaceComponent K L v w =
      Matrix.GeneralLinearGroup.map
        ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
          (Φ K L v).toAlgHom.toRingHom) := rfl

theorem algebraMap_mem_adicCompletionIntegers_iff (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (z : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) z ∈ w.1.adicCompletionIntegers L ↔
      z ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (w.adicCompletionSemialgHom K L z) ≤ 1 ↔ _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w z, hw, pow_one]

theorem valued_algebraMap (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (z : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) z) = Valued.v z := by
  change Valued.v (w.adicCompletionSemialgHom K L z) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w z, hw, pow_one]

variable (ι : Type) [Fintype ι]
  (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (ι → v.adicCompletion K))

def chi (i : ι) : (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) →ₐ[v.adicCompletion K] v.adicCompletion K :=
  (Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp
    (e.toAlgHom.comp (Φ K L v).symm.toAlgHom)

theorem chi_apply (i : ι) (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :
    chi K L v ι e i y = e ((Φ K L v).symm y) i := rfl

theorem apply_eq_chi (i : ι) (x : L ⊗[K] v.adicCompletion K) : e x i = chi K L v ι e i (Φ K L v x) := by
  rw [chi_apply, AlgEquiv.symm_apply_apply]

def place (i : ι) : v.Extension (𝓞 L) :=
  Classical.choose (exists_apply_single_one_eq_one (chi K L v ι e i))

theorem place_spec (i : ι) : chi K L v ι e i (Pi.single (place K L v ι e i) 1) = 1 :=
  Classical.choose_spec (exists_apply_single_one_eq_one (chi K L v ι e i))

def hom (i : ι) : (place K L v ι e i).1.adicCompletion L →ₐ[v.adicCompletion K] v.adicCompletion K :=
  factor (chi K L v ι e i) (place K L v ι e i) (place_spec K L v ι e i)

theorem chi_eq_hom (i : ι) (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :
    chi K L v ι e i y = hom K L v ι e i (y (place K L v ι e i)) :=
  apply_eq_factor (chi K L v ι e i) (place_spec K L v ι e i) y

theorem apply_eq_hom (i : ι) (x : L ⊗[K] v.adicCompletion K) :
    e x i = hom K L v ι e i (Φ K L v x (place K L v ι e i)) := by
  rw [apply_eq_chi, chi_eq_hom]

theorem hom_algebraMap (i : ι) (z : v.adicCompletion K) :
    hom K L v ι e i (algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L) z) = z :=
  (hom K L v ι e i).commutes z

theorem hom_injective (i : ι) : Function.Injective (hom K L v ι e i) :=
  (hom K L v ι e i).toRingHom.injective

theorem algebraMap_bijective (i : ι) :
    Function.Bijective (algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L)) := by
  refine ⟨(algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L)).injective, fun y => ?_⟩
  refine ⟨hom K L v ι e i y, hom_injective K L v ι e i ?_⟩
  rw [hom_algebraMap]

theorem hom_eq_iff (i : ι) (y : (place K L v ι e i).1.adicCompletion L) (z : v.adicCompletion K) :
    hom K L v ι e i y = z ↔ y = algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L) z := by
  constructor
  · rintro rfl
    apply hom_injective K L v ι e i
    rw [hom_algebraMap]
  · rintro rfl
    exact hom_algebraMap K L v ι e i z

theorem place_surjective : Function.Surjective (place K L v ι e) := by
  classical
  intro w₁
  by_contra hw
  push Not at hw

  set y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L := Pi.single w₁ 1 with hy
  have h0 : ∀ i, chi K L v ι e i y = 0 := by
    intro i
    rw [chi_eq_hom, hy, Pi.single_eq_of_ne (hw i), map_zero]
  have he : e ((Φ K L v).symm y) = 0 := by
    funext i
    exact h0 i
  have hy0 : y = 0 := by
    have h1 : (Φ K L v).symm y = 0 := by
      rw [← map_zero e] at he
      exact e.injective he
    have h2 := congrArg (Φ K L v) h1
    rwa [AlgEquiv.apply_symm_apply, map_zero] at h2
  have := congrFun hy0 w₁
  rw [hy, Pi.single_eq_same, Pi.zero_apply] at this
  exact one_ne_zero this

include e in

theorem finrank_eq_one (w : v.Extension (𝓞 L)) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  obtain ⟨i, rfl⟩ := place_surjective K L v ι e w
  let f : v.adicCompletion K ≃ₗ[v.adicCompletion K] (place K L v ι e i).1.adicCompletion L :=
    LinearEquiv.ofBijective (Algebra.linearMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L))
      (algebraMap_bijective K L v ι e i)
  rw [← f.finrank_eq, Module.finrank_self]

theorem place_bijective : Function.Bijective (place K L v ι e) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨place_surjective K L v ι e, ?_⟩
  have h1 : Fintype.card ι = Module.finrank (v.adicCompletion K) (ι → v.adicCompletion K) :=
    (Module.finrank_fintype_fun_eq_card (v.adicCompletion K)).symm
  have h2 : Module.finrank (v.adicCompletion K) (ι → v.adicCompletion K) =
      Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) := e.toLinearEquiv.finrank_eq.symm
  have h3 := HeightOneSpectrum.adicCompletion.finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion
    K L (𝓞 L) v
  haveI : ∀ w : v.Extension (𝓞 L), Module.Free (v.adicCompletion K) (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  have h4 : Module.finrank (v.adicCompletion K) (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) =
      ∑ w : v.Extension (𝓞 L), Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) :=
    Module.finrank_pi_fintype (v.adicCompletion K)
  rw [h1, h2, h3, h4]
  simp [finrank_eq_one K L v ι e]

def placeEquiv : ι ≃ v.Extension (𝓞 L) := Equiv.ofBijective _ (place_bijective K L v ι e)

@[scoped simp] theorem placeEquiv_apply (i : ι) : placeEquiv K L v ι e i = place K L v ι e i := rfl

theorem ramificationIdx_eq_one (i : ι) :
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) (place K L v ι e i).1).asIdeal
      (place K L v ι e i).1.asIdeal = 1 ∧
    v.asIdeal.inertiaDeg' (place K L v ι e i).1.asIdeal = 1 := by
  have h := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L (place K L v ι e i)
  rw [finrank_eq_one K L v ι e] at h
  have h2 : HeightOneSpectrum.under (𝓞 K) (place K L v ι e i).1 = v := (place K L v ι e i).2
  rw [h2]
  exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩

theorem mem_integers_iff (i : ι) (y : (place K L v ι e i).1.adicCompletion L) :
    y ∈ (place K L v ι e i).1.adicCompletionIntegers L ↔ hom K L v ι e i y ∈ v.adicCompletionIntegers K := by
  obtain ⟨z, hz⟩ := (algebraMap_bijective K L v ι e i).2 y
  rw [← hz, hom_algebraMap, algebraMap_mem_adicCompletionIntegers_iff K L v _ (ramificationIdx_eq_one K L v ι e i).1]

theorem toNNReal_congr {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal ha x = WithZeroMulInt.toNNReal hb x := by
  subst h; rfl

theorem absNorm_place_eq (i : ι) :
    Ideal.absNorm (place K L v ι e i).1.asIdeal = Ideal.absNorm v.asIdeal := by
  haveI := liesOver_of_extension K L v (place K L v ι e i)
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver (place K L v ι e i).1.asIdeal v.asIdeal v.isPrime v.ne_bot,
    (ramificationIdx_eq_one K L v ι e i).2, pow_one]

theorem norm_algebraMap_place (i : ι) (z : v.adicCompletion K) :
    ‖algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L) z‖ = ‖z‖ := by
  rw [NumberField.FinitePlace.norm_def v z,
    NumberField.FinitePlace.norm_def (place K L v ι e i).1
      (algebraMap (v.adicCompletion K) ((place K L v ι e i).1.adicCompletion L) z),
    valued_algebraMap K L v _ (ramificationIdx_eq_one K L v ι e i).1]
  congr 1
  apply toNNReal_congr
  rw [absNorm_place_eq]

theorem norm_hom (i : ι) (y : (place K L v ι e i).1.adicCompletion L) : ‖hom K L v ι e i y‖ = ‖y‖ := by
  obtain ⟨z, hz⟩ := (algebraMap_bijective K L v ι e i).2 y
  rw [← hz, hom_algebraMap, norm_algebraMap_place]

section Weights

variable {E F₁ F₂ : Type*} [CommRing E] [NormedField F₁] [NormedField F₂]
  (f₁ : E →+* F₁) (f₂ : E →+* F₂) (hnorm : ∀ x, ‖f₁ x‖ = ‖f₂ x‖)

include hnorm in

theorem weight_map_eq_weight_map (g : GL (Fin 2) E) :
    AutomorphicForm.LocalWeight.weight (Matrix.GeneralLinearGroup.map f₁ g) =
      AutomorphicForm.LocalWeight.weight (Matrix.GeneralLinearGroup.map f₂ g) := by
  unfold AutomorphicForm.LocalWeight.weight AdelicHeight.rowMaxNorm
  have hdet₁ : ((Matrix.GeneralLinearGroup.map f₁ g : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁).det =
      f₁ (g : Matrix (Fin 2) (Fin 2) E).det := by
    rw [RingHom.map_det]; rfl
  have hdet₂ : ((Matrix.GeneralLinearGroup.map f₂ g : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂).det =
      f₂ (g : Matrix (Fin 2) (Fin 2) E).det := by
    rw [RingHom.map_det]; rfl
  simp only [Matrix.GeneralLinearGroup.map_apply, hdet₁, hdet₂, hnorm]

end Weights

theorem partA (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ i : ι, e x i ∈ v.adicCompletionIntegers K := by
  rw [mem_semiLocalIntegers_iff]
  rw [← (placeEquiv K L v ι e).forall_congr_right]
  refine forall_congr' fun i => ?_
  rw [placeEquiv_apply, mem_integers_iff K L v ι e i, ← apply_eq_hom]

theorem weight_coord_eq (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (i : ι) :
    AutomorphicForm.LocalWeight.weight
        (Matrix.GeneralLinearGroup.map
          ((Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp e.toAlgHom).toRingHom g) =
      AutomorphicForm.LocalWeight.weight (AutomorphicForm.semiLocalPlaceComponent K L v (place K L v ι e i) g) := by
  rw [semiLocalPlaceComponent_eq]
  apply weight_map_eq_weight_map
  intro x
  change ‖e x i‖ = ‖Φ K L v x (place K L v ι e i)‖
  rw [apply_eq_hom, norm_hom]

theorem partB (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.semiLocalWeight K L v g =
      ∑ i : ι, AutomorphicForm.LocalWeight.weight
        (Matrix.GeneralLinearGroup.map
          ((Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp e.toAlgHom).toRingHom g) := by
  unfold AutomorphicForm.semiLocalWeight
  rw [finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_bijective (place K L v ι e) (place_bijective K L v ι e) _ _ fun i => ?_
  exact weight_coord_eq K L v ι e g i

end Places

end P2mSplitDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi.P2mSplitDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi.P2mSplitDictionary"

open NumberField IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι]
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (ι → v.adicCompletion K)) :
    (∀ x : L ⊗[K] v.adicCompletion K,
        x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ i : ι, e x i ∈ v.adicCompletionIntegers K) ∧
    (∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v g =
          ∑ i : ι, AutomorphicForm.LocalWeight.weight
            (Matrix.GeneralLinearGroup.map
              ((Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp
                e.toAlgHom).toRingHom g)) :=
  ⟨P2mSplitDictionary.partA K L v ι e, P2mSplitDictionary.partB K L v ι e⟩

end S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
end P2MW
export P2MW.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi (solution)
