-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_nonempty_allowedGen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T16:40:42.609541+00:00
-- url     : https://prove2.me/submissions/21b3a2b3-0bb7-4117-b8cd-fc7ed2a08df8

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_sHilbertPairing

section
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- `𝔪 R = R` for `𝔪 ≠ 0`: a power `𝔪^h = (a)` is principal, and `a⁻¹ ∈ R`. -/
theorem map_self_eq_top (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  classical
  have h𝔪' : 𝔪 ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔪
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hpow : 𝔪 ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem h𝔪' h
  have hprin : (𝔪 ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hpow]
    have : (⟨𝔪 ^ h, hpow⟩ : (Ideal (𝓞 F))⁰) = (⟨𝔪, h𝔪'⟩ : (Ideal (𝓞 F))⁰) ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
    exact (pow_ne_zero h h𝔪) ha
  have hamem : a ∈ 𝔪 := by
    have : a ∈ 𝔪 ^ h := by rw [ha]; exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hpos.ne' this
  -- `a⁻¹` is an `S`-integer
  have hinv : ((a : F))⁻¹ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hav : a ∉ v.asIdeal := by
      intro hav
      apply hv
      change 𝔪 ≤ v.asIdeal
      have : 𝔪 ^ h ≤ v.asIdeal := by
        rw [ha, Ideal.span_le, Set.singleton_subset_iff]; exact hav
      exact v.isPrime.le_of_pow_le this
    rw [map_inv₀]
    have : v.valuation F (a : F) = 1 := by
      rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact hav
    rw [this, inv_one]
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) a * ⟨_, hinv⟩ := by
    apply Subtype.ext
    change (1 : F) = (a : F) * (a : F)⁻¹
    rw [mul_inv_cancel₀]
    exact_mod_cast ha0
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hamem)

/-- An ideal all of whose prime divisors contain `𝔪` becomes the unit ideal in `R`. -/
theorem map_eq_top_of_primes (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (J : Ideal (𝓞 F))
    (hprimes : ∀ Q : Ideal (𝓞 F), Q.IsPrime → J ≤ Q → 𝔪 ≤ Q) :
    J.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
  have hQ : (M.comap (algebraMap (𝓞 F) (SInt 𝔪))).IsPrime := Ideal.comap_isPrime _ M
  have hJQ : J ≤ M.comap (algebraMap (𝓞 F) (SInt 𝔪)) := Ideal.map_le_iff_le_comap.1 hJM
  have h𝔪Q := hprimes _ hQ hJQ
  have : 𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M :=
    Ideal.map_le_iff_le_comap.2 h𝔪Q
  rw [map_self_eq_top 𝔪 h𝔪, top_le_iff] at this
  exact hM.ne_top this

end C0R

/-- **C0-P.** Once `S` contains the primes of small norm, `R = 𝓞_S` is a PID. -/
theorem exists_cutoff_isPrincipal_map (F : Type*) [Field F] [NumberField F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ I : Ideal (𝓞 F), (I.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrincipal := by
  classical
  let rep : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ :=
    fun C => Function.surjInv ClassGroup.mk0_surjective C
  have hrep : ∀ C, ClassGroup.mk0 (rep C) = C := fun C =>
    Function.surjInv_eq ClassGroup.mk0_surjective C
  refine ⟨Finset.univ.sup fun C => Ideal.absNorm (rep C : Ideal (𝓞 F)), ?_⟩
  intro 𝔪 h𝔪 hsmall I
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot]; exact bot_isPrincipal
  have hI' : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set J := rep (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ with hJdef
  have hJ0 : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have hIJ : (I * J).IsPrincipal := by
    have hmem : I * (J : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ := mul_mem hI' J.2
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨I * J, hmem⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ * J := rfl
    rw [this, map_mul, hJdef, hrep, mul_inv_cancel]
  have hJtop : (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
    apply C0R.map_eq_top_of_primes 𝔪 h𝔪 _
    intro Q hQ hJQ
    have hQ0 : Q ≠ ⊥ := fun h => hJ0 (le_bot_iff.1 (h ▸ hJQ))
    apply hsmall Q hQ hQ0
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hJQ
    have hJn : Ideal.absNorm (J : Ideal (𝓞 F)) ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors J
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hJn) hdvd)
      (Finset.le_sup (f := fun C => Ideal.absNorm (rep C : Ideal (𝓞 F))) (Finset.mem_univ _))
  obtain ⟨a, ha⟩ := hIJ.principal
  rw [Ideal.submodule_span_eq] at ha
  refine ⟨⟨algebraMap (𝓞 F) (SInt 𝔪) a, ?_⟩⟩
  rw [Ideal.submodule_span_eq]
  calc I.map (algebraMap (𝓞 F) (SInt 𝔪))
      = I.map (algebraMap (𝓞 F) (SInt 𝔪)) * (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hJtop, Ideal.mul_top]
    _ = (I * J).map (algebraMap (𝓞 F) (SInt 𝔪)) := (Ideal.map_mul _ _ _).symm
    _ = _ := by rw [ha, Ideal.map_span, Set.image_singleton]

end ArtinPrimitiveRoots
end

section
/-!
# C0-L: an isotropic complement of a Lagrangian, for an alternating form

Over a field `K`, let `B` be an alternating bilinear form on a finite-dimensional space `V`, and
`E` an isotropic subspace with `E^⊥ ≤ E ⊔ ker B`. Then some isotropic `W` has `E ⊔ W = ⊤`.
-/

namespace ArtinPrimitiveRoots

open Module LinearMap

namespace C0R

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- One extension step: a transversal isotropic `W` either already spans with `E'`, or extends. -/
theorem step (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (E' : Submodule K V)
    (hker : LinearMap.ker B ≤ E') (hEE : B.orthogonal E' = E')
    (W : Submodule K V) (hWi : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) (hWE : W ⊓ E' = ⊥) :
    E' ⊔ W = ⊤ ∨ ∃ W' : Submodule K V, (∀ x ∈ W', ∀ y ∈ W', B x y = 0) ∧ W' ⊓ E' = ⊥ ∧
      finrank K ↥(E' ⊔ W) < finrank K ↥(E' ⊔ W') := by
  have hrefl : B.IsRefl := hB.isRefl
  by_cases h : B.orthogonal W ≤ E' ⊔ W
  · left
    -- dimension count
    have d1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) W
    have hWk : W ⊓ LinearMap.ker B = ⊥ :=
      eq_bot_iff.2 (le_trans (inf_le_inf_left _ hker) hWE.le)
    rw [show (W ⊓ B.ker : Submodule K V) = W ⊓ LinearMap.ker B from rfl, hWk, finrank_bot] at d1
    have d2 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) (E' ⊔ W)
    have hk2 : ((E' ⊔ W) ⊓ B.ker : Submodule K V) = LinearMap.ker B :=
      inf_eq_right.2 (le_trans hker le_sup_left)
    rw [hk2] at d2
    have d0 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) E'
    have hk0 : (E' ⊓ B.ker : Submodule K V) = LinearMap.ker B := inf_eq_right.2 hker
    rw [hk0, hEE] at d0
    have d3 : E' ⊓ B.orthogonal W ≤ B.orthogonal (E' ⊔ W) := by
      intro z hz
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hn
      have h1 : B a z = 0 := by
        have h1' : z ∈ B.orthogonal E' := by rw [hEE]; exact hz.1
        exact (LinearMap.BilinForm.mem_orthogonal_iff.1 h1') a ha
      have h2 : B b z = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hz.2) b hb
      change B (a + b) z = 0
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    have d3' := Submodule.finrank_mono d3
    have d4 := Submodule.finrank_sup_add_finrank_inf_eq E' (B.orthogonal W)
    have d5 := Submodule.finrank_mono (sup_le le_sup_left h : E' ⊔ B.orthogonal W ≤ E' ⊔ W)
    have d6 := Submodule.finrank_sup_add_finrank_inf_eq E' W
    rw [inf_comm, hWE, finrank_bot] at d6
    have hle := Submodule.finrank_le (E' ⊔ W)
    apply Submodule.eq_top_of_finrank_eq
    omega
  · right
    obtain ⟨y, hyW, hy⟩ := Set.not_subset.1 h
    have hyo : ∀ n ∈ W, B n y = 0 := fun n hn =>
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hyW) n hn
    have hyo' : ∀ n ∈ W, B y n = 0 := fun n hn => hrefl _ _ (hyo n hn)
    refine ⟨W ⊔ K ∙ y, ?_, ?_, ?_⟩
    · intro x hx x' hx'
      obtain ⟨w1, hw1, z1, hz1, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨w2, hw2, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz1
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hz2
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hWi w1 hw1 w2 hw2, hyo w1 hw1, hyo' w2 hw2, hB.self_eq_zero y]
      ring
    · rw [eq_bot_iff]
      intro z ⟨hz1, hz2⟩
      obtain ⟨w1, hw1, z1, hz1', rfl⟩ := Submodule.mem_sup.1 hz1
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz1'
      by_cases ha : a = 0
      · subst ha
        rw [zero_smul, add_zero] at hz2 ⊢
        have : w1 ∈ W ⊓ E' := ⟨hw1, hz2⟩
        rwa [hWE] at this
      · exfalso
        apply hy
        have : y = a⁻¹ • (w1 + a • y) - a⁻¹ • w1 := by
          rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_left hz2))
          (Submodule.smul_mem _ _ (Submodule.mem_sup_right hw1))
    · apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne (sup_le_sup_left le_sup_left _) fun heq => hy ?_
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))

theorem exists_isotropic_sup_eq_top_field (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (E : Submodule K V) (hiso : E ≤ B.orthogonal E)
    (hlag : B.orthogonal E ≤ E ⊔ LinearMap.ker B) :
    ∃ W : Submodule K V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) ∧ E ⊔ W = ⊤ := by
  have hrefl : B.IsRefl := hB.isRefl
  set E' := E ⊔ LinearMap.ker B with hE'
  have hk : ∀ k ∈ LinearMap.ker B, ∀ y, B k y = 0 := fun k hkB y => by
    rw [LinearMap.mem_ker.1 hkB]; rfl
  have hk' : ∀ k ∈ LinearMap.ker B, ∀ y, B y k = 0 := fun k hkB y => hrefl _ _ (hk k hkB y)
  have hEiso : ∀ x ∈ E, ∀ y ∈ E, B x y = 0 := fun x hx y hy =>
    (LinearMap.BilinForm.mem_orthogonal_iff.1 (hiso hy)) x hx
  have hE'iso : ∀ x ∈ E', ∀ y ∈ E', B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hy
    simp only [map_add, LinearMap.add_apply, hEiso a ha c hc, hk b hb, hk' d hd]
    simp
  have hEE : B.orthogonal E' = E' := by
    apply le_antisymm
    · intro z hz
      apply hlag
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz ⊢
      exact fun n hn => hz n (Submodule.mem_sup_left hn)
    · intro z hz
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      exact fun n hn => hE'iso n hn z hz
  have hker : LinearMap.ker B ≤ E' := le_sup_right
  -- induction on the codimension of `E' ⊔ W`
  have main : ∀ d : ℕ, ∀ W : Submodule K V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) → W ⊓ E' = ⊥ →
      finrank K V - finrank K ↥(E' ⊔ W) = d →
      ∃ W' : Submodule K V, (∀ x ∈ W', ∀ y ∈ W', B x y = 0) ∧ E' ⊔ W' = ⊤ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro W hWi hWE hd
      rcases step B hB E' hker hEE W hWi hWE with h | ⟨W', hW'i, hW'E, hlt⟩
      · exact ⟨W, hWi, h⟩
      · have hle := Submodule.finrank_le (E' ⊔ W')
        exact ih _ (by omega) W' hW'i hW'E rfl
  obtain ⟨W, hWi, hW⟩ := main _ ⊥ (by simp) (by simp) rfl
  refine ⟨W ⊔ LinearMap.ker B, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hy
    simp only [map_add, LinearMap.add_apply, hWi a ha c hc, hk b hb, hk' d hd]
    simp
  · rw [eq_top_iff, ← hW, hE']
    exact sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
      (le_sup_of_le_right le_sup_left)

end C0R

/-- **C0-L.** A Lagrangian complement for an alternating form over `ZMod ℓ`. -/
theorem exists_isotropic_sup_eq_top {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod ℓ) V] [FiniteDimensional (ZMod ℓ) V] (B : LinearMap.BilinForm (ZMod ℓ) V)
    (hB : B.IsAlt) (E : Submodule (ZMod ℓ) V) (hiso : E ≤ B.orthogonal E)
    (hlag : B.orthogonal E ≤ E ⊔ LinearMap.ker B) :
    ∃ W : Submodule (ZMod ℓ) V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) ∧ E ⊔ W = ⊤ :=
  C0R.exists_isotropic_sup_eq_top_field B hB E hiso hlag

end ArtinPrimitiveRoots
end

section
/-!
# From an alternating pairing on a group to an isotropic complement of `U`

Group-theoretic form of the linear algebra used for Lemma 3.2: `H : G →* G →* M` with
`M` of exponent `ℓ` (embedded in `ZMod ℓ`), alternating, `U` isotropic and `U^⊥ ⊆ U · rad H`,
and `G / rad H` finite. Then there is an isotropic "`B`" (`Good`) with `G = B · U`, stable under
`ℓ`-th powers.
-/

namespace ArtinPrimitiveRoots

set_option linter.style.haveILetI false

namespace C0R

variable {G : Type*} [CommGroup G] {M : Type*} [CommGroup M]

theorem pair_skew (H : G →* G →* M) (halt : ∀ x, H x x = 1) (x y : G) : H x y * H y x = 1 := by
  have h := halt (x * y)
  rw [mul_comm]
  simpa only [map_mul, MonoidHom.mul_apply, halt x, halt y, one_mul, mul_one] using h

theorem pair_eq_one_symm (H : G →* G →* M) (halt : ∀ x, H x x = 1) {x y : G} (h : H x y = 1) :
    H y x = 1 := by
  have := pair_skew H halt x y
  rwa [h, one_mul] at this

/-- The pairing on `G ⧸ rad H`. -/
def pairQ (H : G →* G →* M) (halt : ∀ x, H x x = 1) :
    (G ⧸ H.ker) →* (G ⧸ H.ker) →* M :=
  QuotientGroup.lift H.ker
    { toFun := fun x => QuotientGroup.lift H.ker (H x) (fun y hy => by
        rw [MonoidHom.mem_ker] at hy ⊢
        exact pair_eq_one_symm H halt (by rw [hy]; rfl))
      map_one' := by
        ext q
        simp
      map_mul' := fun a b => by
        ext q
        simp }
    (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      ext q
      simp [hx])

theorem core_addSubgroup {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod ℓ) V] [Finite V] (B0 : V →+ V →+ ZMod ℓ) (halt : ∀ v, B0 v v = 0)
    (E : AddSubgroup V) (hiso : ∀ e ∈ E, ∀ e' ∈ E, B0 e e' = 0)
    (hlag : ∀ v, (∀ e ∈ E, B0 e v = 0) → v ∈ E) :
    ∃ W : AddSubgroup V, (∀ x ∈ W, ∀ y ∈ W, B0 x y = 0) ∧ ∀ v, ∃ e ∈ E, ∃ w ∈ W, e + w = v := by
  haveI : FiniteDimensional (ZMod ℓ) V := Module.Finite.of_finite
  let B : LinearMap.BilinForm (ZMod ℓ) V :=
    LinearMap.mk₂ (ZMod ℓ) (fun v w => B0 v w) (fun a b w => by simp [map_add])
      (fun c v w => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul,
          AddMonoidHom.nsmul_apply, nsmul_eq_mul, smul_eq_mul])
      (fun v a b => map_add _ _ _)
      (fun c v w => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul,
          smul_eq_mul])
  have hB : ∀ v w, B v w = B0 v w := fun _ _ => rfl
  let E' : Submodule (ZMod ℓ) V := AddSubgroup.toZModSubmodule ℓ E
  have hE' : ∀ v, v ∈ E' ↔ v ∈ E := fun _ => Iff.rfl
  have hBalt : B.IsAlt := fun v => by rw [hB]; exact halt v
  have hEiso : E' ≤ B.orthogonal E' := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    change B n v = 0
    rw [hB]; exact hiso n hn v hv
  have hElag : B.orthogonal E' ≤ E' ⊔ LinearMap.ker B := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
    exact Submodule.mem_sup_left (hlag v fun e he => by have := hv e he; rwa [← hB])
  obtain ⟨W, hWi, hW⟩ := ArtinPrimitiveRoots.exists_isotropic_sup_eq_top B hBalt E' hEiso hElag
  refine ⟨W.toAddSubgroup, fun x hx y hy => by rw [← hB]; exact hWi x hx y hy, fun v => ?_⟩
  have : v ∈ E' ⊔ W := by rw [hW]; trivial
  obtain ⟨e, he, w, hw, hew⟩ := Submodule.mem_sup.1 this
  exact ⟨e, he, w, hw, hew⟩

theorem exists_good {ℓ : ℕ} [Fact ℓ.Prime] (φ : Additive M →+ ZMod ℓ)
    (hφ : Function.Injective φ) (hM : ∀ m : M, m ^ ℓ = 1)
    (H : G →* G →* M) (U : Subgroup G) (halt : ∀ x, H x x = 1)
    (hiso : ∀ u ∈ U, ∀ u' ∈ U, H u u' = 1)
    (hlag : ∀ x, (∀ u ∈ U, H x u = 1) → ∃ u ∈ U, H (x * u⁻¹) = 1)
    (hfin : Finite (G ⧸ H.ker)) :
    ∃ Good : G → Prop, (∀ x y, Good x → Good y → H x y = 1) ∧
      (∀ x, ∃ u ∈ U, Good (x * u)) ∧ (∀ x z, Good x → Good (x * z ^ ℓ)) := by
  have hφ1 : ∀ m : M, φ (Additive.ofMul m) = 0 → m = 1 := fun m hm => by
    have : φ (Additive.ofMul m) = φ (Additive.ofMul 1) := by rw [hm]; exact (map_zero φ).symm
    exact Additive.ofMul.injective (hφ this)
  have hpowker : ∀ z : G, z ^ ℓ ∈ H.ker := fun z => by
    rw [MonoidHom.mem_ker]
    ext y
    simp [hM]
  have hqpow : ∀ q : (G ⧸ H.ker), q ^ ℓ = 1 := fun q => by
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hpowker z
  have hℓV : ∀ v : Additive (G ⧸ H.ker), ℓ • v = 0 := fun v => by
    change Additive.ofMul (v.toMul ^ ℓ) = Additive.ofMul 1
    rw [hqpow]
  haveI : Finite (Additive (G ⧸ H.ker)) := inferInstanceAs (Finite (G ⧸ H.ker))
  let Hq := pairQ H halt
  let B0 : Additive (G ⧸ H.ker) →+ Additive (G ⧸ H.ker) →+ ZMod ℓ :=
    AddMonoidHom.mk' (fun v => AddMonoidHom.mk'
      (fun w => φ (Additive.ofMul (Hq v.toMul w.toMul))) (fun a b => by
        rw [← map_add]; congr 1
        change Additive.ofMul (Hq v.toMul (a.toMul * b.toMul)) = _
        rw [map_mul]; rfl)) (fun a b => by
        refine AddMonoidHom.ext fun w => ?_
        change φ (Additive.ofMul (Hq (a.toMul * b.toMul) w.toMul)) =
          φ (Additive.ofMul (Hq a.toMul w.toMul)) + φ (Additive.ofMul (Hq b.toMul w.toMul))
        rw [← map_add, map_mul, MonoidHom.mul_apply]; rfl)
  have hBapp : ∀ x y : G, B0 (Additive.ofMul (x : (G ⧸ H.ker))) (Additive.ofMul (y : (G ⧸ H.ker))) =
      φ (Additive.ofMul (H x y)) := fun x y => rfl
  have hall : ∀ v : Additive (G ⧸ H.ker), ∃ x : G, Additive.ofMul (x : (G ⧸ H.ker)) = v :=
    fun v => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective v.toMul
      exact ⟨x, by rw [hx]; rfl⟩
  let E : AddSubgroup (Additive (G ⧸ H.ker)) :=
    Subgroup.toAddSubgroup (U.map (QuotientGroup.mk' H.ker))
  have hmemE : ∀ v, v ∈ E ↔ ∃ u ∈ U, Additive.ofMul (u : (G ⧸ H.ker)) = v := fun v => by
    change v.toMul ∈ U.map (QuotientGroup.mk' H.ker) ↔ _
    rw [Subgroup.mem_map]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, by
        change Additive.ofMul ((QuotientGroup.mk' H.ker) u) = v; rw [h]; rfl⟩,
      fun ⟨u, hu, h⟩ => ⟨u, hu, by rw [← h]; rfl⟩⟩
  have hBalt : ∀ v, B0 v v = 0 := fun v => by
    obtain ⟨x, rfl⟩ := hall v
    rw [hBapp, halt]; exact map_zero φ
  have hEiso : ∀ e ∈ E, ∀ e' ∈ E, B0 e e' = 0 := by
    intro e he e' he'
    obtain ⟨u, hu, rfl⟩ := (hmemE e).1 he
    obtain ⟨u', hu', rfl⟩ := (hmemE e').1 he'
    rw [hBapp, hiso u hu u' hu']; exact map_zero φ
  have hElag : ∀ v, (∀ e ∈ E, B0 e v = 0) → v ∈ E := by
    intro v hv
    obtain ⟨x, rfl⟩ := hall v
    have hx : ∀ u ∈ U, H x u = 1 := fun u hu => by
      have := hv (Additive.ofMul (u : (G ⧸ H.ker))) ((hmemE _).2 ⟨u, hu, rfl⟩)
      rw [hBapp] at this
      exact pair_eq_one_symm H halt (hφ1 _ this)
    obtain ⟨u, hu, hxu⟩ := hlag x hx
    rw [hmemE]
    refine ⟨u, hu, ?_⟩
    congr 1
    rw [QuotientGroup.eq, mul_comm]
    exact MonoidHom.mem_ker.2 hxu
  letI : Module (ZMod ℓ) (Additive (G ⧸ H.ker)) := AddCommGroup.zmodModule hℓV
  obtain ⟨W, hWi, hW⟩ := core_addSubgroup B0 hBalt E hEiso hElag
  refine ⟨fun x => Additive.ofMul (x : (G ⧸ H.ker)) ∈ W, ?_, ?_, ?_⟩
  · intro x y hx hy
    have := hWi _ hx _ hy
    rw [hBapp] at this
    exact hφ1 _ this
  · intro x
    obtain ⟨e, he, w, hw, hew⟩ := hW (Additive.ofMul (x : (G ⧸ H.ker)))
    obtain ⟨u, hu, rfl⟩ := (hmemE e).1 he
    refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
    have : w = Additive.ofMul ((x * u⁻¹ : G) : (G ⧸ H.ker)) := by
      rw [← sub_eq_of_eq_add' hew.symm, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← div_eq_mul_inv, ofMul_div]
    show Additive.ofMul ((x * u⁻¹ : G) : (G ⧸ H.ker)) ∈ W
    rw [← this]; exact hw
  · intro x z hx
    have : ((x * z ^ ℓ : G) : (G ⧸ H.ker)) = (x : (G ⧸ H.ker)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hqpow, mul_one]
    change Additive.ofMul ((x * z ^ ℓ : G) : (G ⧸ H.ker)) ∈ W
    rw [this]; exact hx

end C0R

end ArtinPrimitiveRoots
end

section
/-!
# Glue: allowed generators from the `S`-Hilbert pairings for `ℓ = 2, 3`

For a fixed field and modulus (any universe): if `R` is a PID and the sextic residue symbols are
controlled by alternating pairings `H₂, H₃` as in C0-H, then `AllowedGen ι 𝔪` is nonempty.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option linter.style.haveILetI false

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- The content of C0-H for one field, one modulus and one `ℓ`: an alternating pairing
`H : Fˣ × Fˣ → μ_ℓ` (classically `H_S = ∏_{v ∈ S} (·,·)_{ℓ,v}`) for which the `S`-units are
isotropic, their orthogonal is the `S`-units modulo the radical, the radical has finite index, and
reciprocity of the `ℓ`-th residue symbols holds for prime generators with trivial pairing. -/
def HPackage (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (ℓ : ℕ) : Prop :=
  ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
    (∀ x, H x x = 1) ∧
    (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
    (∀ x, (∀ u ∈ (placesOf 𝔪).unit F, H x u = 1) →
      ∃ u ∈ (placesOf 𝔪).unit F, H (x * u⁻¹) = 1) ∧
    Finite (Fˣ ⧸ H.ker) ∧
    ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' → P ≠ P' →
      ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
        Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
        Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) → H x x' = 1 →
          sexticResidueSymbol ι 𝔪 P p' ^ (6 / ℓ) = sexticResidueSymbol ι 𝔪 P' p ^ (6 / ℓ)

theorem cube_sq_eq {a b : ℂ} (h3 : a ^ 3 = b ^ 3) (h2 : a ^ 2 = b ^ 2) : a = b := by
  by_cases ha : a = 0
  · subst ha
    have : b ^ 2 = 0 := by rw [← h2]; ring
    exact (pow_eq_zero_iff two_ne_zero).1 this |>.symm
  · have hb : b ^ 2 ≠ 0 := by rw [← h2]; exact pow_ne_zero 2 ha
    have hb' : b ≠ 0 := fun h => hb (by rw [h]; ring)
    have e1 : a = a ^ 3 / a ^ 2 := by field_simp
    have e2 : b = b ^ 3 / b ^ 2 := by field_simp
    rw [e1, e2, h3, h2]

omit [NumberField F] in
theorem exists_phi {ℓ : ℕ} [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ φ : Additive (rootsOfUnity ℓ F) →+ ZMod ℓ, Function.Injective φ := by
  have hu := hζ.isUnit_unit (NeZero.ne ℓ)
  let e1 : rootsOfUnity ℓ F ≃* Subgroup.zpowers (hζ.isUnit (NeZero.ne ℓ)).unit :=
    MulEquiv.subgroupCongr hu.zpowers_eq.symm
  exact ⟨hu.zmodEquivZPowers.symm.toAddMonoidHom.comp (MulEquiv.toAdditive e1).toAddMonoidHom,
    hu.zmodEquivZPowers.symm.injective.comp (MulEquiv.toAdditive e1).injective⟩

/-- Extending a prime-generator system multiplicatively gives allowed generators. -/
theorem allowedGen_of_prime_system (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (pg : Ideal (𝓞 F) → SInt 𝔪)
    (hspan : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
      Ideal.span {pg P} = P.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hrec : ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P →
      IsExterior 𝔪 P' → P ≠ P' →
        sexticResidueSymbol ι 𝔪 P (pg P') = sexticResidueSymbol ι 𝔪 P' (pg P)) :
    Nonempty (AllowedGen ι 𝔪) := by
  classical
  let gen : Ideal (𝓞 F) → SInt 𝔪 := fun I => ((normalizedFactors I).map pg).prod
  have hfac : ∀ I, IsExterior 𝔪 I → ∀ P ∈ normalizedFactors I, P.IsPrime ∧ IsExterior 𝔪 P := by
    intro I hI P hP
    have hprime := prime_of_normalized_factor P hP
    refine ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, ?_⟩
    have hle : I ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
    rw [eq_top_iff, ← hI.2]
    exact sup_le_sup_right hle _
  have hgenP : ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → gen P = pg P := by
    intro P hP hP0
    have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
    simp only [gen, normalizedFactors_irreducible hirr, normalize_eq, Multiset.map_singleton,
      Multiset.prod_singleton]
  refine ⟨{ gen := gen, span_gen := ?_, gen_mul := ?_, reciprocity := ?_ }⟩
  · intro I hI
    have hI0 : I ≠ ⊥ := hI.1
    calc Ideal.span {gen I}
        = ((normalizedFactors I).map fun P => Ideal.span {pg P}).prod := by
          have := Ideal.multiset_prod_span_singleton ((normalizedFactors I).map pg)
          rw [Multiset.map_map] at this
          exact this.symm
      _ = ((normalizedFactors I).map fun P => P.map (algebraMap (𝓞 F) (SInt 𝔪))).prod := by
          congr 1
          apply Multiset.map_congr rfl
          intro P hP
          exact hspan P (hfac I hI P hP).1 (hfac I hI P hP).2
      _ = (normalizedFactors I).prod.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
          rw [← Ideal.mapHom_apply, map_multiset_prod]
          rfl
      _ = I.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
          rw [Ideal.prod_normalizedFactors_eq_self hI0]
  · intro I J hI hJ
    refine ⟨1, ?_⟩
    have hI0 : I ≠ 0 := hI.1
    have hJ0 : J ≠ 0 := hJ.1
    have : gen (I * J) = gen I * gen J := by
      simp only [gen, normalizedFactors_mul hI0 hJ0, Multiset.map_add, Multiset.prod_add]
    rw [this]
    simp
  · intro P P' hP hP' hE hE' hne
    rw [hgenP P' hP' hE'.1, hgenP P hP hE.1]
    exact hrec P P' hP hP' hE hE' hne

/-- **Glue.** PID plus the two pairing packages give allowed generators. -/
theorem nonempty_allowedGen_of_packages (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (hPID : ∀ I : Ideal (𝓞 F), (I.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrincipal)
    (φ₂ : Additive (rootsOfUnity 2 F) →+ ZMod 2) (hφ₂ : Function.Injective φ₂)
    (φ₃ : Additive (rootsOfUnity 3 F) →+ ZMod 3) (hφ₃ : Function.Injective φ₃)
    (pkg₂ : HPackage ι 𝔪 2) (pkg₃ : HPackage ι 𝔪 3) : Nonempty (AllowedGen ι 𝔪) := by
  classical
  obtain ⟨H₂, alt₂, iso₂, lag₂, fin₂, rec₂⟩ := pkg₂
  obtain ⟨H₃, alt₃, iso₃, lag₃, fin₃, rec₃⟩ := pkg₃
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : ∀ (ℓ : ℕ) (m : rootsOfUnity ℓ F), m ^ ℓ = 1 := fun ℓ m =>
    Subtype.ext ((mem_rootsOfUnity _ _).1 m.2)
  obtain ⟨G₂, gi₂, gc₂, gp₂⟩ :=
    exists_good φ₂ hφ₂ (hM 2) H₂ ((placesOf 𝔪).unit F) alt₂ iso₂ lag₂ fin₂
  obtain ⟨G₃, gi₃, gc₃, gp₃⟩ :=
    exists_good φ₃ hφ₃ (hM 3) H₃ ((placesOf 𝔪).unit F) alt₃ iso₃ lag₃ fin₃
  have key : ∀ P : Ideal (𝓞 F), ∃ p : SInt 𝔪, ∃ x : Fˣ, P.IsPrime → IsExterior 𝔪 P →
      ((x : F) = p ∧ Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧ G₂ x ∧ G₃ x) := by
    intro P
    by_cases hP : P.IsPrime ∧ IsExterior 𝔪 P
    swap
    · exact ⟨1, 1, fun h1 h2 => absurd ⟨h1, h2⟩ hP⟩
    obtain ⟨g, hg⟩ := (hPID P).principal
    have hg0 : (g : F) ≠ 0 := by
      intro h0
      have hg0' : g = 0 := Subtype.ext h0
      rw [hg0', Submodule.span_singleton_eq_bot.2 rfl] at hg
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.2.1
      have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ (⊥ : Submodule (SInt 𝔪) (SInt 𝔪)) := by
        rw [← hg]; exact Ideal.mem_map_of_mem _ ha
      rw [Submodule.mem_bot] at this
      apply ha0
      have h' : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = 0 := by rw [this]; rfl
      exact (map_eq_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective _ _)).1 h'
    set x := Units.mk0 (g : F) hg0 with hx
    obtain ⟨u₂, hu₂, h₂⟩ := gc₂ x
    obtain ⟨u₃, hu₃, h₃⟩ := gc₃ x
    have hu : u₂ ^ 3 * u₃ ^ 4 ∈ (placesOf 𝔪).unit F :=
      mul_mem (pow_mem hu₂ 3) (pow_mem hu₃ 4)
    refine ⟨g * ((Set.unitEquivUnitsInteger (placesOf 𝔪) F ⟨_, hu⟩ : (SInt 𝔪)ˣ) : SInt 𝔪),
      x * (u₂ ^ 3 * u₃ ^ 4), fun _ _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · simp [x]
    · rw [Ideal.span_singleton_mul_right_unit (Units.isUnit _), hg]
    · have := gp₂ (x * u₂) (u₂ * u₃ ^ 2) h₂
      have e : x * (u₂ ^ 3 * u₃ ^ 4) = x * u₂ * (u₂ * u₃ ^ 2) ^ 2 := by
        simp only [pow_succ, pow_zero, one_mul]
        ac_rfl
      rw [e]; exact this
    · have := gp₃ (x * u₃) (u₂ * u₃) h₃
      have e : x * (u₂ ^ 3 * u₃ ^ 4) = x * u₃ * (u₂ * u₃) ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]
        ac_rfl
      rw [e]; exact this
  choose pg px hpx using key
  apply allowedGen_of_prime_system ι 𝔪 pg (fun P hP hE => (hpx P hP hE).2.1)
  intro P P' hP hP' hE hE' hne
  have h2 := rec₂ P P' hP hP' hE hE' hne (pg P) (pg P') (px P) (px P') (hpx P hP hE).1
    (hpx P' hP' hE').1 (hpx P hP hE).2.1 (hpx P' hP' hE').2.1
    (gi₂ _ _ (hpx P hP hE).2.2.1 (hpx P' hP' hE').2.2.1)
  have h3 := rec₃ P P' hP hP' hE hE' hne (pg P) (pg P') (px P) (px P') (hpx P hP hE).1
    (hpx P' hP' hE').1 (hpx P hP hE).2.1 (hpx P' hP' hE').2.1
    (gi₃ _ _ (hpx P hP hE).2.2.2 (hpx P' hP' hE').2.2.2)
  exact cube_sq_eq (by simpa using h2) (by simpa using h3)

end C0R

end ArtinPrimitiveRoots
end

section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_le_iff (f : R ≃+* S) {I J : Ideal R} : I.map f ≤ J.map f ↔ I ≤ J := by
  constructor
  · intro h x hx
    have : f x ∈ J.map f := h ((mem_map_equiv f I _).2 (by simpa using hx))
    simpa using (mem_map_equiv f J _).1 this
  · intro h y hy
    exact (mem_map_equiv f J y).2 (h ((mem_map_equiv f I y).1 hy))

theorem map_equiv_injective (f : R ≃+* S) {I J : Ideal R} (h : I.map f = J.map f) : I = J :=
  le_antisymm ((map_equiv_le_iff f).1 h.le) ((map_equiv_le_iff f).1 h.ge)

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

theorem map_map_sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    (I.map (algebraMap (𝓞 F) (SInt 𝔪))).map (sIntEquiv e 𝔪) =
      (I.map (RingOfIntegers.mapRingEquiv e)).map
        (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)))) := by
  show Ideal.map ((sIntEquiv e 𝔪 : SInt 𝔪 →+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.map (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map ((RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')))
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

theorem isExterior_map (e : F ≃+* F') {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) (I.map (RingOfIntegers.mapRingEquiv e)) := by
  refine ⟨fun h0 => h.1 ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0
  · rw [← Ideal.map_sup, h.2, Ideal.map_top]

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

theorem sexticResidueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F))
    (h6 : P ⊔ Ideal.span {6} = ⊤) (x : SInt 𝔪) :
    sexticResidueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (P.map (RingOfIntegers.mapRingEquiv e)) (sIntEquiv e 𝔪 x) =
      sexticResidueSymbol ι 𝔪 P x := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  set eS := sIntEquiv e 𝔪
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set f' := algebraMap (𝓞 F') (SInt (𝔪.map eO))
  set Q := P.map f
  have hQ' : (P.map eO).map f' = Q.map eS := (map_map_sIntEquiv e 𝔪 P).symm
  have hmem : ∀ y : SInt 𝔪, eS y ∈ (P.map eO).map f' ↔ y ∈ Q := fun y => by
    rw [hQ', mem_map_equiv, RingEquiv.symm_apply_apply]
  have hN : Ideal.absNorm (P.map eO) = Ideal.absNorm P := absNorm_map_equiv e P
  unfold sexticResidueSymbol
  simp only [Ideal.Quotient.eq_zero_iff_mem]
  by_cases hx : x ∈ Q
  · rw [if_pos hx, if_pos ((hmem x).2 hx)]
  rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h)), hN]
  set k := (Ideal.absNorm P - 1) / 6
  -- `6 ∉ Q`
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h6m
    apply hx
    have : Q = ⊤ := by
      rw [eq_top_iff, ← Ideal.map_top f, ← h6, Ideal.map_sup]
      refine sup_le le_rfl ?_
      rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.span_le,
        Set.singleton_subset_iff]
      exact h6m
    rw [this]; trivial
  have hC : ∀ ζ : 𝓞 F, (ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k) ↔
      ((eO ζ) ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' (eO ζ)) =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k) := by
    intro ζ
    apply and_congr
    · rw [← map_pow, ← map_one eO]
      exact eO.injective.eq_iff.symm
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq, ← map_pow eS,
        show f' (eO ζ) = eS (f ζ) from rfl, ← map_sub, hmem]
  have huniq : ∀ ζ₁ ζ₂ : 𝓞 F, (ζ₁ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₁) = Ideal.Quotient.mk Q x ^ k) →
      (ζ₂ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₂) = Ideal.Quotient.mk Q x ^ k) → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2
    have hsub : f ζ₁ - f ζ₂ ∈ Q := by
      rw [← Ideal.Quotient.eq, h1.2, h2.2]
    have := eq_of_pow_six Q h6Q (by rw [← map_pow, h1.1, map_one])
      (by rw [← map_pow, h2.1, map_one]) hsub
    have h' : ((f ζ₁ : SInt 𝔪) : F) = ((f ζ₂ : SInt 𝔪) : F) := by rw [this]
    exact RingOfIntegers.ext h'
  by_cases h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k
  · have h' : ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k :=
      ⟨eO h.choose, (hC _).1 h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    have hspec : eO (eO.symm h'.choose) = h'.choose := eO.apply_symm_apply _
    have hC' := (hC (eO.symm h'.choose)).2 (by rw [hspec]; exact h'.choose_spec)
    have := huniq _ _ hC' h.choose_spec
    rw [← this]
    simp [eO]
  · have h' : ¬ ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k := by
      rintro ⟨ζ', hζ'⟩
      apply h
      refine ⟨eO.symm ζ', (hC _).2 ?_⟩
      rw [eO.apply_symm_apply]; exact hζ'
    rw [dif_neg h, dif_neg h']

/-! ### `AllowedGen` transports -/

theorem nonempty_allowedGen_of_equiv (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (g' : AllowedGen (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    Nonempty (AllowedGen ι 𝔪) := by
  set eO := RingOfIntegers.mapRingEquiv e
  refine ⟨⟨fun I => (sIntEquiv e 𝔪).symm (g'.gen (I.map eO)), ?_, ?_, ?_⟩⟩
  · intro I hI
    have h := g'.span_gen (I.map eO) (isExterior_map e hI)
    apply map_equiv_injective (sIntEquiv e 𝔪)
    rw [map_map_sIntEquiv, ← h, Ideal.map_span, Set.image_singleton, RingEquiv.apply_symm_apply]
  · intro I J hI hJ
    obtain ⟨ε', hε'⟩ := g'.gen_mul (I.map eO) (J.map eO) (isExterior_map e hI)
      (isExterior_map e hJ)
    let u' : (SInt (𝔪.map eO))ˣ := Set.unitEquivUnitsInteger _ F' ε'
    let ε : SUnit 𝔪 := (Set.unitEquivUnitsInteger _ F).symm
      (Units.map ((sIntEquiv e 𝔪).symm : SInt (𝔪.map eO) →* SInt 𝔪) u')
    refine ⟨ε, ?_⟩
    have hε : (((ε : Fˣ)) : F) = e.symm (((ε' : F'ˣ)) : F') := rfl
    have hmul : (I * J).map eO = I.map eO * J.map eO := Ideal.map_mul _ _ _
    rw [hmul]
    change e.symm ((g'.gen (I.map eO * J.map eO) : F')) = (((ε : Fˣ)) : F) ^ 6 *
      e.symm ((g'.gen (I.map eO)) : F') * e.symm ((g'.gen (J.map eO)) : F')
    rw [hε, hε', map_mul, map_mul, map_pow]
  · intro P P' hP hP' hE hE' hne
    have hPm : (P.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    have hP'm : (P'.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    have hne' : P.map eO ≠ P'.map eO := fun h => hne (map_equiv_injective eO h)
    have r := g'.reciprocity _ _ hPm hP'm (isExterior_map e hE) (isExterior_map e hE') hne'
    have t1 := sexticResidueSymbol_transport e ι 𝔪 P (h6 P hP hE)
      ((sIntEquiv e 𝔪).symm (g'.gen (P'.map eO)))
    have t2 := sexticResidueSymbol_transport e ι 𝔪 P' (h6 P' hP' hE')
      ((sIntEquiv e 𝔪).symm (g'.gen (P.map eO)))
    simp only [RingEquiv.apply_symm_apply] at t1 t2
    rw [← t1, ← t2]
    exact r

/-- `SmallPrimesDvd` transports. -/
theorem smallPrimesDvd_map (e : F ≃+* F') {N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪) :
    SmallPrimesDvd N₀ (𝔪.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro P' hP' hP'0 hN
  set P := P'.map eO.symm
  have hPP : P.map eO = P' := by
    have := map_equiv_symm_map eO.symm P'
    rwa [RingEquiv.symm_symm] at this
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
  have hP0 : P ≠ ⊥ := fun h0 => hP'0 (by rw [← hPP, h0, Ideal.map_bot])
  have hNP : Ideal.absNorm P ≤ N₀ := by rw [← absNorm_map_equiv e P, hPP]; exact hN
  rw [← hPP]
  exact (map_equiv_le_iff eO).2 (h P hP hP0 hNP)

end C0R

end ArtinPrimitiveRoots
end

section
/-!
# C0: `exists_cutoff_nonempty_allowedGen` from C0-P, C0-L (proved) and C0-H (hypothesis)
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

/-- **C0-H** (the cut left open): for `F ⊇ μ₁₂` (universe 0) and `ℓ ∈ {2, 3}`, once `S` contains
the small primes there is an alternating pairing `H : Fˣ × Fˣ → μ_ℓ(F)` (classically the `S`-part
`H_S(x, y) = ∏_{v ∈ S} (x, y)_{ℓ, v}` of the `ℓ`-th Hilbert symbol) such that: the `S`-units are
isotropic; anything orthogonal to all `S`-units is an `S`-unit modulo the radical (`E^⊥ ⊆ E + rad`,
i.e. `U_S` is Lagrangian); the radical has finite index; and for prime generators `p, p'` of
distinct exterior primes with `H(p, p') = 1` the `ℓ`-th power residue symbols agree,
`χ_P(p')^{6/ℓ} = χ_{P'}(p)^{6/ℓ}` (Hilbert reciprocity + tame symbols). -/
def CutH : Prop :=
  ∀ (n : ℕ), 0 < n → 12 ∣ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (ℓ : ℕ), (ℓ = 2 ∨ ℓ = 3) →
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
        (∀ x, H x x = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
        (∀ x, (∀ u ∈ (placesOf 𝔪).unit F, H x u = 1) →
          ∃ u ∈ (placesOf 𝔪).unit F, H (x * u⁻¹) = 1) ∧
        Finite (Fˣ ⧸ H.ker) ∧
        ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) → H x x' = 1 →
              sexticResidueSymbol ι 𝔪 P p' ^ (6 / ℓ) = sexticResidueSymbol ι 𝔪 P' p ^ (6 / ℓ)

set_option linter.style.haveILetI false

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

theorem smallPrimesDvd_mono {N N₁ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₁ 𝔪)
    (hle : N ≤ N₁) : SmallPrimesDvd N 𝔪 :=
  fun P hP h0 hN => h P hP h0 (le_trans hN hle)

theorem sup_span_six_eq_top {N₀ : ℕ} {𝔪 P : Ideal (𝓞 F)}
    (hN : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≤ N₀) (hs : SmallPrimesDvd N₀ 𝔪)
    (hP : P.IsPrime) (hE : IsExterior 𝔪 P) : P ⊔ Ideal.span {6} = ⊤ := by
  by_contra h
  have hmax : P.IsMaximal := hP.isMaximal hE.1
  have hle : Ideal.span {(6 : 𝓞 F)} ≤ P := by
    have := hmax.eq_of_le h le_sup_left
    rw [this]; exact le_sup_right
  have h60 : (6 : 𝓞 F) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp at this
  have hn0 : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h60
  have hNP : Ideal.absNorm P ≤ N₀ :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Ideal.absNorm_dvd_absNorm_of_le hle)) hN
  have h𝔪 := hs P hP hE.1 hNP
  apply hP.ne_top
  rw [← hE.2, sup_eq_left.2 h𝔪]

end C0R

/-- **C0** from **C0-H** (C0-P and C0-L are proved). The stub's statement, with C0-H as a
hypothesis. -/
theorem chk_exists_cutoff_nonempty_allowedGen_of_cutH (hH : CutH) (n : ℕ) (hn0 : 0 < n)
    (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Nonempty (AllowedGen ι 𝔪) := by
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero ((n : ℚ)) := ⟨by exact_mod_cast hn0.ne'⟩
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let e : F ≃+* CyclotomicField n ℚ :=
    (IsCyclotomicExtension.algEquiv {n} ℚ F (CyclotomicField n ℚ)).toRingEquiv
  let ι₀ : CyclotomicField n ℚ →+* ℂ := ι.comp (e.symm : CyclotomicField n ℚ →+* F)
  obtain ⟨N₂, hN₂⟩ := hH n hn0 hn (CyclotomicField n ℚ) ι₀ 2 (Or.inl rfl)
  obtain ⟨N₃, hN₃⟩ := hH n hn0 hn (CyclotomicField n ℚ) ι₀ 3 (Or.inr rfl)
  obtain ⟨NP, hNP⟩ := exists_cutoff_isPrincipal_map (CyclotomicField n ℚ)
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  have hprim : ∀ ℓ : ℕ, ℓ ∣ n → ∃ z : CyclotomicField n ℚ, IsPrimitiveRoot z ℓ := by
    intro ℓ hℓ
    have hne : n / ℓ ≠ 0 := by
      intro h0
      rcases Nat.div_eq_zero_iff.1 h0 with h | h
      · subst h; simp at hℓ; omega
      · exact absurd (Nat.le_of_dvd hn0 hℓ) (not_le.2 h)
    have := hζ.pow_of_dvd hne (Nat.div_dvd_of_dvd hℓ)
    rw [Nat.div_div_self hℓ hn0.ne'] at this
    exact ⟨_, this⟩
  obtain ⟨z₂, hz₂⟩ := hprim 2 (dvd_trans (by norm_num) hn)
  obtain ⟨z₃, hz₃⟩ := hprim 3 (dvd_trans (by norm_num) hn)
  obtain ⟨φ₂, hφ₂⟩ := C0R.exists_phi hz₂
  obtain ⟨φ₃, hφ₃⟩ := C0R.exists_phi hz₃
  refine ⟨max (max N₂ N₃) (max NP (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}))),
    fun 𝔪 h𝔪 hsmall => ?_⟩
  set 𝔪₀ := 𝔪.map (RingOfIntegers.mapRingEquiv e)
  have h𝔪₀ : 𝔪₀ ≠ ⊥ := fun h0 =>
    h𝔪 ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0)
  have hs₀ := C0R.smallPrimesDvd_map e hsmall
  have g₀ := C0R.nonempty_allowedGen_of_packages ι₀ 𝔪₀
    (hNP 𝔪₀ h𝔪₀ (C0R.smallPrimesDvd_mono hs₀ (by omega))) φ₂ hφ₂ φ₃ hφ₃
    (hN₂ 𝔪₀ h𝔪₀ (C0R.smallPrimesDvd_mono hs₀ (by omega)))
    (hN₃ 𝔪₀ h𝔪₀ (C0R.smallPrimesDvd_mono hs₀ (by omega)))
  obtain ⟨g₀⟩ := g₀
  exact C0R.nonempty_allowedGen_of_equiv e ι 𝔪
    (fun P hP hE => C0R.sup_span_six_eq_top (N₀ := max (max N₂ N₃)
      (max NP (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})))) (by omega) hsmall hP hE) g₀

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Nonempty (AllowedGen ι 𝔪) :=
  chk_exists_cutoff_nonempty_allowedGen_of_cutH exists_cutoff_exists_sHilbertPairing n hn0 hn F ι
end
