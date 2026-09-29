-- Prove2me | solution 1 for AutomorphicForm.exists_extension_algEquiv_adicCompletion_of_isField_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8492eeae-b0a2-55e2-91f9-ee7a74631c3d

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace SigmaTensorFix

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {A : Type*} [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem repr_map_sigma {ι : Type*} (b : Module.Basis ι K A) (a : L ⊗[K] A) (i : ι) :
    (Algebra.TensorProduct.basis L b).repr (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) a) i =
      σ ((Algebra.TensorProduct.basis L b).repr a i) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, AlgEquiv.commutes]
  | add x y hx hy =>
      simp [map_add, hx, hy]

theorem map_sigma_eq_self_iff (hfix : ∀ x : L, σ x = x → x ∈ (algebraMap K L).range) (a : L ⊗[K] A) :
    Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) a = a ↔
      a ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  classical
  haveI : Module.Free K A := Module.Free.of_divisionRing K A
  set b := Module.Free.chooseBasis K A with hb
  set bL := Algebra.TensorProduct.basis L b with hbL
  constructor
  · intro h
    set c := bL.repr a with hc
    have hσc : ∀ i, σ (c i) = c i := by
      intro i
      rw [hc, ← repr_map_sigma σ b a i, h]
    have hk : ∀ i, ∃ k : K, algebraMap K L k = c i := fun i => by
      obtain ⟨k, hk⟩ := hfix _ (hσc i)
      exact ⟨k, hk⟩
    choose k hk using hk
    refine ⟨c.sum fun i _ => k i • b i, ?_⟩
    symm
    calc a = Finsupp.linearCombination L bL c := (bL.linearCombination_repr a).symm
      _ = c.sum (fun i x => x • bL i) := Finsupp.linearCombination_apply _ _
      _ = c.sum (fun i _ => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) (k i • b i)) := by
          refine Finsupp.sum_congr (fun i _ => ?_)
          rw [hbL, Algebra.TensorProduct.basis_apply, ← hk i, algebraMap_smul,
            Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]
      _ = (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) (c.sum fun i _ => k i • b i) := by
          rw [map_finsuppSum]
  · rintro ⟨a', rfl⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
    simp

end SigmaTensorFix

namespace SigmaTensorC2b

theorem nonempty_and_subsingleton_of_isField_pi {ι : Type*} (F : ι → Type*) [∀ i, Field (F i)]
    (h : IsField (∀ i, F i)) : Nonempty ι ∧ ∀ i j : ι, i = j := by
  classical
  constructor
  · by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  · intro i j
    by_contra hij
    letI := h.toField
    have hx : (Pi.single i (1 : F i) : ∀ k, F k) ≠ 0 := by
      intro h0
      have := congr_fun h0 i
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have hy : (Pi.single j (1 : F j) : ∀ k, F k) ≠ 0 := by
      intro h0
      have := congr_fun h0 j
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have hprod : (Pi.single i (1 : F i) : ∀ k, F k) * Pi.single j (1 : F j) = 0 := by
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_of_ne hij, mul_zero]
      · rw [Pi.single_eq_of_ne hk, zero_mul]
    exact (mul_ne_zero hx hy) hprod

theorem pow_finrank_eq_one {E F : Type*} [Field E] [Field F] [Algebra E F] (θ : F ≃ₐ[E] F) :
    θ ^ Module.finrank E F = 1 := by
  rcases Nat.eq_zero_or_pos (Module.finrank E F) with h0 | hpos
  · rw [h0, pow_zero]
  · haveI : FiniteDimensional E F := Module.finite_of_finrank_pos hpos
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers θ)) F = orderOf θ := by
      rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    rw [← h1]
    exact Dvd.intro_left _
      (Module.finrank_mul_finrank E (IntermediateField.fixedField (Subgroup.zpowers θ)) F)

theorem orderOf_eq_finrank {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    orderOf σ = Module.finrank K L := by
  have hdvd : orderOf σ ∣ Module.finrank K L := orderOf_dvd_of_pow_eq_one (pow_finrank_eq_one σ)
  rcases hdeg.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hσ
  · exact h

theorem mem_range_of_apply_eq {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) (x : L) (hx : σ x = x) :
    x ∈ (algebraMap K L).range := by
  have hp : orderOf σ = Module.finrank K L := orderOf_eq_finrank hdeg σ hσ
  set F₀ := IntermediateField.fixedField (Subgroup.zpowers σ) with hF₀
  have h1 : Module.finrank F₀ L = Module.finrank K L := by
    rw [hF₀, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hp]
  have h2 : Module.finrank K F₀ = 1 := by
    have h := Module.finrank_mul_finrank K F₀ L
    rw [h1] at h
    have hpos : 0 < Module.finrank K L := Nat.pos_of_ne_zero hdeg.ne_zero
    rcases Nat.eq_zero_or_pos (Module.finrank K F₀) with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd h (ne_of_lt hpos)
    · exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, one_mul])
  have hbot : F₀ = ⊥ := IntermediateField.finrank_eq_one_iff.mp h2
  have hxF : x ∈ F₀ := by
    rw [hF₀, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hx
    have := (Subgroup.zpowers_le.mpr hmem) hf
    rwa [MulAction.mem_stabilizer_iff] at this
  rw [hbot, IntermediateField.mem_bot] at hxF
  exact RingHom.mem_range.mpr hxF

open IsDedekindDomain.HeightOneSpectrum

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hA : IsField (L ⊗[K] v.adicCompletion K)) :
    ∃ (w : v.Extension (𝓞 L))
      (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),
      (∀ w' : v.Extension (𝓞 L), w' = w) ∧
      (∀ a : L ⊗[K] v.adicCompletion K,
          e (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ a) = θ (e a)) ∧
      (∀ x : L, e (x ⊗ₜ[K] 1) = algebraMap L (w.1.adicCompletion L) x) ∧
      orderOf θ = Module.finrank K L ∧
      (∀ y : w.1.adicCompletion L, θ y = y ↔
        y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Ideal.inertiaDeg' v.asIdeal w.1.asIdeal = Module.finrank K L := by
  classical

  have hF : IsField (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
    MulEquiv.isField hA (adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm.toMulEquiv
  obtain ⟨⟨w⟩, huniq⟩ :=
    nonempty_and_subsingleton_of_isField_pi (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) hF

  let e₀ : L ⊗[K] v.adicCompletion K →ₐ[v.adicCompletion K] w.1.adicCompletion L :=
    (Pi.evalAlgHom (v.adicCompletion K) (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (adicCompletion.baseChangeRight K L (𝓞 L) v)
  have he₀_apply : ∀ a, e₀ a = adicCompletion.baseChange K L (𝓞 L) v a w := fun a => rfl
  have hbij := adicCompletion.baseChange_bijective K L (𝓞 L) v
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro a b hab
      apply hbij.1
      funext w'
      obtain rfl := huniq w' w
      rw [he₀_apply, he₀_apply] at hab
      exact hab
    · intro y
      obtain ⟨z, hz⟩ := hbij.2 (Function.update 0 w y)
      refine ⟨z, ?_⟩
      rw [he₀_apply, hz, Function.update_self]
  let e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L :=
    AlgEquiv.ofBijective e₀ he₀
  have he_apply : ∀ a, e a = adicCompletion.baseChange K L (𝓞 L) v a w := fun a => rfl
  have he_tmul_one : ∀ x : L, e (x ⊗ₜ[K] 1) = algebraMap L (w.1.adicCompletion L) x := by
    intro x
    rw [he_apply, adicCompletion.baseChange_tmul_apply, map_one, mul_one]

  let S : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv)
      (fun c => by
        change Algebra.TensorProduct.map (σ : L →ₐ[K] L)
            ((AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) :
              v.adicCompletion K →ₐ[K] v.adicCompletion K) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl)
  have hS : ∀ a, S a = AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ a := fun a => rfl
  have hS_tmul : ∀ (x : L) (c : v.adicCompletion K), S (x ⊗ₜ[K] c) = σ x ⊗ₜ[K] c := by
    intro x c
    change Algebra.TensorProduct.map (σ : L →ₐ[K] L)
        ((AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) :
          v.adicCompletion K →ₐ[K] v.adicCompletion K) (x ⊗ₜ[K] c) = σ x ⊗ₜ[K] c
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hSk_tmul : ∀ (k : ℕ) (x : L) (c : v.adicCompletion K),
      (S ^ k) (x ⊗ₜ[K] c) = (σ ^ k) x ⊗ₜ[K] c := by
    intro k
    induction k with
    | zero => intro x c; rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
    | succ k ih =>
        intro x c
        rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hS_tmul, ih]

  let θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L := (e.symm.trans S).trans e
  have hθ : ∀ y, θ y = e (S (e.symm y)) := fun y => rfl
  have hθe : ∀ a, θ (e a) = e (S a) := fun a => by rw [hθ, AlgEquiv.symm_apply_apply]
  have hθk : ∀ (k : ℕ) (y : w.1.adicCompletion L), (θ ^ k) y = e ((S ^ k) (e.symm y)) := by
    intro k
    induction k with
    | zero =>
        intro y
        rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply]
    | succ k ih =>
        intro y
        rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, hθ,
          AlgEquiv.symm_apply_apply]
  have hinj : Function.Injective (algebraMap L (w.1.adicCompletion L)) := RingHom.injective _

  have key : ∀ k : ℕ, θ ^ k = 1 ↔ σ ^ k = 1 := by
    intro k
    constructor
    · intro h
      ext x
      apply hinj
      have h1 := congr_arg
        (fun f : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L => f (e (x ⊗ₜ[K] 1))) h
      simp only [AlgEquiv.one_apply] at h1
      rw [hθk, AlgEquiv.symm_apply_apply, hSk_tmul, he_tmul_one, he_tmul_one] at h1
      rw [AlgEquiv.one_apply]
      exact h1
    · intro h
      ext y
      rw [hθk, AlgEquiv.one_apply]
      have hSk1 : ∀ b : L ⊗[K] v.adicCompletion K, (S ^ k) b = b := by
        intro b
        induction b using TensorProduct.induction_on with
        | zero => rw [map_zero]
        | tmul x c => rw [hSk_tmul, h, AlgEquiv.one_apply]
        | add a b ha hb => rw [map_add, ha, hb]
      rw [hSk1, AlgEquiv.apply_symm_apply]
  have hord : orderOf θ = Module.finrank K L :=
    (orderOf_eq_orderOf_iff.mpr key).trans (orderOf_eq_finrank hdeg σ hσ)

  have hfixσ : ∀ x : L, σ x = x → x ∈ (algebraMap K L).range :=
    fun x hx => mem_range_of_apply_eq hdeg σ hσ x hx
  have hfixθ : ∀ y : w.1.adicCompletion L, θ y = y ↔
      y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) := by
    intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := e.surjective y
      rw [hθe] at hy
      have hSa : S a = a := e.injective hy
      rw [hS] at hSa
      obtain ⟨c, hc⟩ := (SigmaTensorFix.map_sigma_eq_self_iff σ hfixσ a).mp hSa
      refine ⟨c, ?_⟩
      rw [← hc]
      exact (e.commutes c).symm
    · rintro ⟨c, rfl⟩
      exact θ.commutes c

  have hfr : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L :=
    e.toLinearEquiv.finrank_eq.symm.trans (TensorProduct.finrank_rightAlgebra L)
  have hinert : Ideal.inertiaDeg' v.asIdeal w.1.asIdeal = Module.finrank K L := by
    have h := adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
    have he1 : Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1 := by
      have := hv w.1 w.2
      rwa [w.2] at this
    rw [hfr, he1, one_mul] at h
    exact h
  exact ⟨w, e, θ, fun w' => huniq w' w, fun a => by rw [← hS, hθe], he_tmul_one, hord, hfixθ, hfr,
    hinert⟩

end SigmaTensorC2b

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hA : IsField (L ⊗[K] v.adicCompletion K)) :
    ∃ (w : v.Extension (𝓞 L))
      (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),
      (∀ w' : v.Extension (𝓞 L), w' = w) ∧
      (∀ a : L ⊗[K] v.adicCompletion K, e (sigmaTensor K L (v.adicCompletion K) σ a) = θ (e a)) ∧
      (∀ x : L, e (x ⊗ₜ[K] 1) = algebraMap L (w.1.adicCompletion L) x) ∧
      orderOf θ = Module.finrank K L ∧
      (∀ y : w.1.adicCompletion L, θ y = y ↔
        y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Ideal.inertiaDeg' v.asIdeal w.1.asIdeal = Module.finrank K L :=
  SigmaTensorC2b.main K L hdeg σ hσ v hv hA

end S_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor
end P2MW
export P2MW.S_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor (solution)
