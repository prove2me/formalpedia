-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_twoAffineLineCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3512d285-9b03-59b6-8525-20b34d59891b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
example : True := trivial

noncomputable section
namespace P1E85
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance] MvPolynomial.gradedAlgebra

variable (S : Type u) [CommRing S]

abbrev 𝒜 : ℕ → Submodule S (MvPolynomial (Fin 2) S) := MvPolynomial.homogeneousSubmodule (Fin 2) S

theorem X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) S) ∈ 𝒜 S 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X S i)

theorem C_mem (s : S) : (MvPolynomial.C s : MvPolynomial (Fin 2) S) ∈ 𝒜 S 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ s)

theorem X_mul_X_mem : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) S) ∈ 𝒜 S 2 :=
  SetLike.mul_mem_graded (X_mem S 0) (X_mem S 1)

noncomputable def ψ : S →+* ↥(𝒜 S 0) where
  toFun s := ⟨MvPolynomial.C s, C_mem S s⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem ψ_bijective : Function.Bijective (ψ S) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    exact MvPolynomial.C_injective _ _ this
  · rintro ⟨p, hp⟩
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp
    refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
    change MvPolynomial.C (MvPolynomial.coeff 0 p) = p
    by_cases h0 : p = 0
    · subst h0; simp
    · exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (hp.totalDegree h0)).symm

theorem adjoin_X_eq_top : Algebra.adjoin (↥(𝒜 S 0)) (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S)) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun p => ?_
  induction p using MvPolynomial.induction_on with
  | C s =>
    have : (MvPolynomial.C s : MvPolynomial (Fin 2) S) = algebraMap (↥(𝒜 S 0)) (MvPolynomial (Fin 2) S) (ψ S s) := rfl
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

scoped instance finiteType_𝒜0 : Algebra.FiniteType (↥(𝒜 S 0)) (MvPolynomial (Fin 2) S) := by
  classical
  exact ⟨⟨(Finset.univ : Finset (Fin 2)).image MvPolynomial.X, by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact adjoin_X_eq_top S⟩⟩

section Charts
variable (S : Type u) [CommRing S]
open HomogeneousLocalization

abbrev X0 : MvPolynomial (Fin 2) S := MvPolynomial.X 0
abbrev X1 : MvPolynomial (Fin 2) S := MvPolynomial.X 1

theorem mem_one_smul {p : MvPolynomial (Fin 2) S} (h : p ∈ 𝒜 S 1) : p ∈ 𝒜 S (1 • 1) := by simpa using h

def t₀ : Away (𝒜 S) (X0 S) := Away.mk (𝒜 S) (X_mem S 0) 1 (X1 S) (mem_one_smul S (X_mem S 1))

def t₁ : Away (𝒜 S) (X1 S) := Away.mk (𝒜 S) (X_mem S 1) 1 (X0 S) (mem_one_smul S (X_mem S 0))

@[scoped simp] theorem val_t₀ : (t₀ S).val = Localization.mk (X1 S) (⟨X0 S ^ 1, 1, rfl⟩ : Submonoid.powers (X0 S)) :=
  Away.val_mk _ _ _ _ _
@[scoped simp] theorem val_t₁ : (t₁ S).val = Localization.mk (X0 S) (⟨X1 S ^ 1, 1, rfl⟩ : Submonoid.powers (X1 S)) :=
  Away.val_mk _ _ _ _ _

def b₀ : Polynomial S →+* Away (𝒜 S) (X0 S) :=
  Polynomial.eval₂RingHom ((fromZeroRingHom (𝒜 S) _).comp (ψ S)) (t₀ S)

def b₁ : Polynomial S →+* Away (𝒜 S) (X1 S) :=
  Polynomial.eval₂RingHom ((fromZeroRingHom (𝒜 S) _).comp (ψ S)) (t₁ S)

@[scoped simp] theorem b₀_C (s : S) : b₀ S (Polynomial.C s) = fromZeroRingHom (𝒜 S) _ (ψ S s) := by simp [b₀]
@[scoped simp] theorem b₀_X : b₀ S Polynomial.X = t₀ S := by simp [b₀]
@[scoped simp] theorem b₁_C (s : S) : b₁ S (Polynomial.C s) = fromZeroRingHom (𝒜 S) _ (ψ S s) := by simp [b₁]
@[scoped simp] theorem b₁_X : b₁ S Polynomial.X = t₁ S := by simp [b₁]

theorem val_fromZeroRingHom_ψ (x : Submonoid (MvPolynomial (Fin 2) S)) (s : S) :
    (fromZeroRingHom (𝒜 S) x (ψ S s)).val = algebraMap (MvPolynomial (Fin 2) S) (Localization x) (MvPolynomial.C s) := by
  rw [← Localization.mk_one_eq_algebraMap]; rfl

def d₀ : MvPolynomial (Fin 2) S →+* Polynomial S := (MvPolynomial.aeval ![(1 : Polynomial S), Polynomial.X]).toRingHom

def d₁ : MvPolynomial (Fin 2) S →+* Polynomial S := (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial S)]).toRingHom

@[scoped simp] theorem d₀_X0 : d₀ S (X0 S) = 1 := by simp [d₀]
@[scoped simp] theorem d₀_X1 : d₀ S (X1 S) = Polynomial.X := by simp [d₀]
@[scoped simp] theorem d₀_C (s : S) : d₀ S (MvPolynomial.C s) = Polynomial.C s := by simp [d₀]
@[scoped simp] theorem d₁_X0 : d₁ S (X0 S) = Polynomial.X := by simp [d₁]
@[scoped simp] theorem d₁_X1 : d₁ S (X1 S) = 1 := by simp [d₁]
@[scoped simp] theorem d₁_C (s : S) : d₁ S (MvPolynomial.C s) = Polynomial.C s := by simp [d₁]

def e₀ : Away (𝒜 S) (X0 S) →+* Polynomial S :=
  (Localization.awayLift (d₀ S) (X0 S) (by rw [d₀_X0]; exact isUnit_one)).comp
    (algebraMap (Away (𝒜 S) (X0 S)) (Localization.Away (X0 S)))

def e₁ : Away (𝒜 S) (X1 S) →+* Polynomial S :=
  (Localization.awayLift (d₁ S) (X1 S) (by rw [d₁_X1]; exact isUnit_one)).comp
    (algebraMap (Away (𝒜 S) (X1 S)) (Localization.Away (X1 S)))

theorem e₀_b₀ : (e₀ S).comp (b₀ S) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro s
    simp only [RingHom.comp_apply, b₀_C, RingHom.id_apply, e₀, HomogeneousLocalization.algebraMap_apply,
      val_fromZeroRingHom_ψ]
    erw [IsLocalization.Away.lift_eq]
    exact d₀_C S s
  · simp only [RingHom.comp_apply, b₀_X, RingHom.id_apply, e₀, HomogeneousLocalization.algebraMap_apply, val_t₀]
    rw [Localization.awayLift_mk (d₀ S) (X0 S) (X1 S) 1 (by rw [d₀_X0, one_mul]) 1]
    simp

theorem e₁_b₁ : (e₁ S).comp (b₁ S) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro s
    simp only [RingHom.comp_apply, b₁_C, RingHom.id_apply, e₁, HomogeneousLocalization.algebraMap_apply,
      val_fromZeroRingHom_ψ]
    erw [IsLocalization.Away.lift_eq]
    exact d₁_C S s
  · simp only [RingHom.comp_apply, b₁_X, RingHom.id_apply, e₁, HomogeneousLocalization.algebraMap_apply, val_t₁]
    rw [Localization.awayLift_mk (d₁ S) (X1 S) (X0 S) 1 (by rw [d₁_X1, one_mul]) 1]
    simp

end Charts

section Equivs
variable (S : Type u) [CommRing S]
open HomogeneousLocalization

theorem b₀_injective : Function.Injective (b₀ S) := by
  intro a b h
  have := congrArg (e₀ S) h
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, e₀_b₀, RingHom.id_apply, RingHom.id_apply] at this

theorem b₁_injective : Function.Injective (b₁ S) := by
  intro a b h
  have := congrArg (e₁ S) h
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, e₁_b₁, RingHom.id_apply, RingHom.id_apply] at this

def rangeSub (f : MvPolynomial (Fin 2) S) (b : Polynomial S →+* Away (𝒜 S) f)
    (hb : ∀ s, b (Polynomial.C s) = fromZeroRingHom (𝒜 S) _ (ψ S s)) : Subalgebra (↥(𝒜 S 0)) (Away (𝒜 S) f) :=
  { b.range with
    algebraMap_mem' := fun a => by
      obtain ⟨s, rfl⟩ := (ψ_bijective S).2 a
      exact ⟨Polynomial.C s, by rw [hb]; rfl⟩ }

theorem mem_rangeSub {f : MvPolynomial (Fin 2) S} {b : Polynomial S →+* Away (𝒜 S) f} {hb} {y : Away (𝒜 S) f} :
    y ∈ rangeSub S f b hb ↔ y ∈ b.range := Iff.rfl

theorem surjective_of_gens {f : MvPolynomial (Fin 2) S} (hf : f ∈ 𝒜 S 1) (b : Polynomial S →+* Away (𝒜 S) f)
    (hb : ∀ s, b (Polynomial.C s) = fromZeroRingHom (𝒜 S) _ (ψ S s))
    (hgen : ∀ (a : ℕ) (ai : Fin 2 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1),
      Away.mk (𝒜 S) hf a (∏ i, MvPolynomial.X i ^ ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ X_mem S i) ∈ b.range) :
    Function.Surjective b := by
  have htop := Away.adjoin_mk_prod_pow_eq_top (𝒜 := 𝒜 S) hf (Fin 2) MvPolynomial.X (adjoin_X_eq_top S) (fun _ => 1) (X_mem S)
  have hle : Algebra.adjoin (↥(𝒜 S 0)) { x | ∃ (a : ℕ) (ai : Fin 2 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) (_ : ∀ i, ai i ≤ 1),
      Away.mk (𝒜 S) hf a (∏ i, MvPolynomial.X i ^ ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ X_mem S i) = x } ≤
      rangeSub S f b hb := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨a, ai, hai, -, rfl⟩
    exact hgen a ai hai
  intro y
  have hy : y ∈ (⊤ : Subalgebra (↥(𝒜 S 0)) (Away (𝒜 S) f)) := Algebra.mem_top
  rw [← htop] at hy
  exact (mem_rangeSub S).mp (hle hy)

theorem val_b₀_X_pow (n : ℕ) : (b₀ S (Polynomial.X ^ n)).val =
    Localization.mk (X1 S ^ n) (⟨X0 S ^ n, n, rfl⟩ : Submonoid.powers (X0 S)) := by
  rw [map_pow, b₀_X, val_pow, val_t₀, Localization.mk_pow]
  congr 1
  exact Subtype.ext (by simp [SubmonoidClass.coe_pow])

theorem val_b₁_X_pow (n : ℕ) : (b₁ S (Polynomial.X ^ n)).val =
    Localization.mk (X0 S ^ n) (⟨X1 S ^ n, n, rfl⟩ : Submonoid.powers (X1 S)) := by
  rw [map_pow, b₁_X, val_pow, val_t₁, Localization.mk_pow]
  congr 1
  exact Subtype.ext (by simp [SubmonoidClass.coe_pow])

theorem b₀_surjective : Function.Surjective (b₀ S) := by
  refine surjective_of_gens S (X_mem S 0) (b₀ S) (b₀_C S) fun a ai hai => ⟨Polynomial.X ^ ai 1, ?_⟩
  apply val_injective
  rw [val_b₀_X_pow, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Fin.prod_univ_two]
  simp only [smul_eq_mul, mul_one, Fin.sum_univ_two] at hai
  change X0 S ^ a * X1 S ^ ai 1 = X0 S ^ ai 1 * (MvPolynomial.X 0 ^ ai 0 * MvPolynomial.X 1 ^ ai 1)
  rw [← hai]; ring

theorem b₁_surjective : Function.Surjective (b₁ S) := by
  refine surjective_of_gens S (X_mem S 1) (b₁ S) (b₁_C S) fun a ai hai => ⟨Polynomial.X ^ ai 0, ?_⟩
  apply val_injective
  rw [val_b₁_X_pow, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Fin.prod_univ_two]
  simp only [smul_eq_mul, mul_one, Fin.sum_univ_two] at hai
  change X1 S ^ a * X0 S ^ ai 0 = X1 S ^ ai 0 * (MvPolynomial.X 0 ^ ai 0 * MvPolynomial.X 1 ^ ai 1)
  rw [← hai]; ring

def B₀ : Polynomial S ≃+* Away (𝒜 S) (X0 S) := RingEquiv.ofBijective (b₀ S) ⟨b₀_injective S, b₀_surjective S⟩

def B₁ : Polynomial S ≃+* Away (𝒜 S) (X1 S) := RingEquiv.ofBijective (b₁ S) ⟨b₁_injective S, b₁_surjective S⟩

@[scoped simp] theorem B₀_apply (p : Polynomial S) : B₀ S p = b₀ S p := rfl
@[scoped simp] theorem B₁_apply (p : Polynomial S) : B₁ S p = b₁ S p := rfl

theorem B₀_symm_eq_e₀ : (B₀ S).symm.toRingHom = e₀ S := by
  apply RingHom.ext; intro y
  obtain ⟨p, rfl⟩ := b₀_surjective S y
  change (B₀ S).symm (B₀ S p) = e₀ S (b₀ S p)
  rw [RingEquiv.symm_apply_apply, ← RingHom.comp_apply, e₀_b₀, RingHom.id_apply]

theorem B₁_symm_eq_e₁ : (B₁ S).symm.toRingHom = e₁ S := by
  apply RingHom.ext; intro y
  obtain ⟨p, rfl⟩ := b₁_surjective S y
  change (B₁ S).symm (B₁ S p) = e₁ S (b₁ S p)
  rw [RingEquiv.symm_apply_apply, ← RingHom.comp_apply, e₁_b₁, RingHom.id_apply]

end Equivs

section Overlap
variable (S : Type u) [CommRing S]
open HomogeneousLocalization

abbrev X01 : MvPolynomial (Fin 2) S := X0 S * X1 S

theorem hx01 : X01 S = X0 S * X1 S := rfl
theorem hx10 : X01 S = X1 S * X0 S := mul_comm _ _

def m₀ : Away (𝒜 S) (X0 S) →+* Away (𝒜 S) (X01 S) := awayMap (𝒜 S) (X_mem S 1) (hx01 S)
def m₁ : Away (𝒜 S) (X1 S) →+* Away (𝒜 S) (X01 S) := awayMap (𝒜 S) (X_mem S 0) (hx10 S)

theorem isLocalization_m₀ :
    letI := (m₀ S).toAlgebra
    IsLocalization.Away (t₀ S) (Away (𝒜 S) (X01 S)) := by
  have h := Away.isLocalization_mul (𝒜 := 𝒜 S) (X_mem S 0) (X_mem S 1) (hx01 S) one_ne_zero
  have ht : Away.isLocalizationElem (𝒜 := 𝒜 S) (X_mem S 0) (X_mem S 1) = t₀ S := by
    apply val_injective; simp [Away.val_mk, t₀]
  rw [ht] at h
  exact h

def B₀₁ : LaurentPolynomial S ≃+* Away (𝒜 S) (X01 S) :=
  letI := (m₀ S).toAlgebra
  haveI := isLocalization_m₀ S
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (Polynomial.X : Polynomial S))
    (T := Submonoid.powers (t₀ S)) (LaurentPolynomial S) (Away (𝒜 S) (X01 S)) (B₀ S)
    (by rw [Submonoid.map_powers]; simp)

theorem B₀₁_toLaurent (p : Polynomial S) : B₀₁ S (Polynomial.toLaurent p) = m₀ S (B₀ S p) := by
  letI := (m₀ S).toAlgebra
  haveI := isLocalization_m₀ S
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ p

theorem B₀₁_comp_toLaurent : (B₀₁ S).toRingHom.comp (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S) =
    (m₀ S).comp (B₀ S).toRingHom := RingHom.ext (B₀₁_toLaurent S)

theorem m₀_fromZero (s : S) : m₀ S (fromZeroRingHom (𝒜 S) _ (ψ S s)) = fromZeroRingHom (𝒜 S) _ (ψ S s) :=
  awayMap_fromZeroRingHom ..
theorem m₁_fromZero (s : S) : m₁ S (fromZeroRingHom (𝒜 S) _ (ψ S s)) = fromZeroRingHom (𝒜 S) _ (ψ S s) :=
  awayMap_fromZeroRingHom ..

theorem m₀_t₀_mul_m₁_t₁ : m₀ S (t₀ S) * m₁ S (t₁ S) = 1 := by
  apply val_injective
  rw [val_mul, val_one, m₀, m₁, t₀, t₁, awayMap_mk, awayMap_mk, Away.val_mk, Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one]
  ring

theorem B₀₁_comp_toLaurentInv :
    (B₀₁ S).toRingHom.comp (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) = (m₁ S).comp (B₁ S).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro s
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Polynomial.toLaurent_C]
    change B₀₁ S (LaurentPolynomial.invert (LaurentPolynomial.C s)) = m₁ S (B₁ S (Polynomial.C s))
    rw [show LaurentPolynomial.invert (LaurentPolynomial.C s) = LaurentPolynomial.C s by simp, ← Polynomial.toLaurent_C,
      B₀₁_toLaurent, B₀_apply, B₁_apply, b₀_C, b₁_C, m₀_fromZero, m₁_fromZero]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Polynomial.toLaurent_X]
    change B₀₁ S (LaurentPolynomial.invert (LaurentPolynomial.T 1)) = m₁ S (B₁ S Polynomial.X)
    rw [LaurentPolynomial.invert_T, B₁_apply, b₁_X]

    have h1 : B₀₁ S (LaurentPolynomial.T 1) = m₀ S (t₀ S) := by
      rw [← Polynomial.toLaurent_X, B₀₁_toLaurent, B₀_apply, b₀_X]
    have h2 : B₀₁ S (LaurentPolynomial.T (-1)) * B₀₁ S (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, ← LaurentPolynomial.T_add]; simp
    rw [h1] at h2
    have h3 := m₀_t₀_mul_m₁_t₁ S
    calc B₀₁ S (LaurentPolynomial.T (-1)) = B₀₁ S (LaurentPolynomial.T (-1)) * (m₀ S (t₀ S) * m₁ S (t₁ S)) := by
          rw [h3, mul_one]
      _ = m₁ S (t₁ S) := by rw [← mul_assoc, h2, one_mul]

end Overlap

section SchemeLevel
variable (S : Type u) [CommRing S]
open HomogeneousLocalization

def j₀ : Spec (CommRingCat.of (Away (𝒜 S) (X0 S))) ⟶ Proj (𝒜 S) := Proj.awayι (𝒜 S) (X0 S) (X_mem S 0) one_pos
def j₁ : Spec (CommRingCat.of (Away (𝒜 S) (X1 S))) ⟶ Proj (𝒜 S) := Proj.awayι (𝒜 S) (X1 S) (X_mem S 1) one_pos
def j₀₁ : Spec (CommRingCat.of (Away (𝒜 S) (X01 S))) ⟶ Proj (𝒜 S) := Proj.awayι (𝒜 S) (X01 S) (X_mul_X_mem S) two_pos

scoped instance : IsOpenImmersion (j₀ S) := by unfold j₀; infer_instance
scoped instance : IsOpenImmersion (j₁ S) := by unfold j₁; infer_instance

theorem m₀_j₀ : Spec.map (CommRingCat.ofHom (m₀ S)) ≫ j₀ S = j₀₁ S := Proj.SpecMap_awayMap_awayι ..
theorem m₁_j₁ : Spec.map (CommRingCat.ofHom (m₁ S)) ≫ j₁ S = j₀₁ S := Proj.SpecMap_awayMap_awayι ..

def specIso {R T : Type u} [CommRing R] [CommRing T] (e : R ≃+* T) : Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from RingHom.ext e.apply_symm_apply,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show e.symm.toRingHom.comp e.toRingHom = RingHom.id _ from RingHom.ext e.symm_apply_apply,
      CommRingCat.ofHom_id, Spec.map_id]

def c₀ : Spec (CommRingCat.of (Polynomial S)) ≅ Spec (CommRingCat.of (Away (𝒜 S) (X0 S))) := specIso (B₀ S).symm
def c₁ : Spec (CommRingCat.of (Polynomial S)) ≅ Spec (CommRingCat.of (Away (𝒜 S) (X1 S))) := specIso (B₁ S).symm
def c₀₁ : Spec (CommRingCat.of (LaurentPolynomial S)) ≅ Spec (CommRingCat.of (Away (𝒜 S) (X01 S))) := specIso (B₀₁ S).symm

theorem c₀_hom : (c₀ S).hom = Spec.map (CommRingCat.ofHom (B₀ S).symm.toRingHom) := rfl
theorem c₁_hom : (c₁ S).hom = Spec.map (CommRingCat.ofHom (B₁ S).symm.toRingHom) := rfl
theorem c₀₁_hom : (c₀₁ S).hom = Spec.map (CommRingCat.ofHom (B₀₁ S).symm.toRingHom) := rfl

def i₀ : Spec (CommRingCat.of (Polynomial S)) ⟶ Proj (𝒜 S) := (c₀ S).hom ≫ j₀ S
def i₁ : Spec (CommRingCat.of (Polynomial S)) ⟶ Proj (𝒜 S) := (c₁ S).hom ≫ j₁ S

scoped instance : IsOpenImmersion (i₀ S) := by unfold i₀; infer_instance
scoped instance : IsOpenImmersion (i₁ S) := by unfold i₁; infer_instance

def p : Proj (𝒜 S) ⟶ Spec (CommRingCat.of S) := Proj.toSpecZero (𝒜 S) ≫ Spec.map (CommRingCat.ofHom (ψ S))

scoped instance isIso_specMap_ψ : IsIso (Spec.map (CommRingCat.ofHom (ψ S))) := by
  change IsIso (Spec.map (RingEquiv.ofBijective (ψ S) (ψ_bijective S)).toCommRingCatIso.hom)
  infer_instance

scoped instance isProper_p : IsProper (p S) := by unfold p; infer_instance

theorem toLaurent_B₀symm : CommRingCat.ofHom (B₀ S).symm.toRingHom ≫
    CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S) =
      CommRingCat.ofHom (m₀ S) ≫ CommRingCat.ofHom (B₀₁ S).symm.toRingHom := by
  apply CommRingCat.hom_ext; apply RingHom.ext; intro y
  obtain ⟨q, rfl⟩ := (B₀ S).surjective y
  change Polynomial.toLaurent ((B₀ S).symm (B₀ S q)) = (B₀₁ S).symm (m₀ S (B₀ S q))
  rw [RingEquiv.symm_apply_apply, ← B₀₁_toLaurent, RingEquiv.symm_apply_apply]

theorem toLaurentInv_B₁symm : CommRingCat.ofHom (B₁ S).symm.toRingHom ≫
    CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) =
      CommRingCat.ofHom (m₁ S) ≫ CommRingCat.ofHom (B₀₁ S).symm.toRingHom := by
  apply CommRingCat.hom_ext; apply RingHom.ext; intro y
  obtain ⟨q, rfl⟩ := (B₁ S).surjective y
  have := congrArg (fun φ => φ q) (B₀₁_comp_toLaurentInv S)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
  change (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp Polynomial.toLaurent) ((B₁ S).symm (B₁ S q)) =
    (B₀₁ S).symm (m₁ S (B₁ S q))
  rw [RingEquiv.symm_apply_apply, ← this]
  change _ = (B₀₁ S).symm ((B₀₁ S) _)
  rw [RingEquiv.symm_apply_apply]; rfl

theorem glue : Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ i₀ S =
    Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ i₁ S := by
  rw [i₀, i₁, c₀_hom, c₁_hom, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, toLaurent_B₀symm, toLaurentInv_B₁symm,
    Spec.map_comp_assoc, Spec.map_comp_assoc, m₀_j₀, m₁_j₁]

theorem toL_c₀ : Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ (c₀ S).hom =
    (c₀₁ S).hom ≫ Spec.map (CommRingCat.ofHom (m₀ S)) := by
  rw [c₀_hom, c₀₁_hom, ← Spec.map_comp, ← Spec.map_comp, toLaurent_B₀symm]

theorem toLinv_c₁ : Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ (c₁ S).hom =
    (c₀₁ S).hom ≫ Spec.map (CommRingCat.ofHom (m₁ S)) := by
  rw [c₁_hom, c₀₁_hom, ← Spec.map_comp, ← Spec.map_comp, toLaurentInv_B₁symm]

theorem isPullback_m : IsPullback (Spec.map (CommRingCat.ofHom (m₀ S))) (Spec.map (CommRingCat.ofHom (m₁ S))) (j₀ S) (j₁ S) := by
  refine IsPullback.of_iso_pullback ⟨by rw [m₀_j₀, m₁_j₁]⟩
    (Proj.pullbackAwayιIso (𝒜 S) (X_mem S 0) one_pos (X_mem S 1) one_pos (hx01 S)).symm ?_ ?_
  · exact Proj.pullbackAwayιIso_inv_fst ..
  · exact Proj.pullbackAwayιIso_inv_snd (hx := hx01 S) ..

theorem isPullback_i : IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))
    (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) (i₀ S) (i₁ S) := by
  refine IsPullback.of_iso (isPullback_m S) (c₀₁ S).symm (c₀ S).symm (c₁ S).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← toL_c₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← toLinv_c₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, i₀]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, i₁]

theorem i₀_p : i₀ S ≫ p S = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  rw [i₀, p, c₀_hom, Category.assoc, j₀, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext; apply RingHom.ext; intro s
  change (B₀ S).symm (fromZeroRingHom (𝒜 S) _ (ψ S s)) = algebraMap S (Polynomial S) s
  rw [← b₀_C, ← B₀_apply, RingEquiv.symm_apply_apply]
  rfl

theorem i₁_p : i₁ S ≫ p S = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  rw [i₁, p, c₁_hom, Category.assoc, j₁, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext; apply RingHom.ext; intro s
  change (B₁ S).symm (fromZeroRingHom (𝒜 S) _ (ψ S s)) = algebraMap S (Polynomial S) s
  rw [← b₁_C, ← B₁_apply, RingEquiv.symm_apply_apply]
  rfl

theorem cover : Set.range (i₀ S).base ∪ Set.range (i₁ S).base = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have htop := Proj.iSup_basicOpen_eq_top' (𝒜 S) (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S)
    (fun i => ⟨1, X_mem S i⟩) (adjoin_X_eq_top S)
  have hx : x ∈ (⨆ i, Proj.basicOpen (𝒜 S) (MvPolynomial.X i) : (Proj (𝒜 S)).Opens) := by rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · left
    change x ∈ Proj.basicOpen (𝒜 S) (X0 S) at hi
    rw [← Proj.opensRange_awayι (𝒜 S) (X0 S) (X_mem S 0) one_pos] at hi
    obtain ⟨y, rfl⟩ := hi
    refine ⟨(c₀ S).inv.base y, ?_⟩
    rw [i₀, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (c₀ S).hom, Iso.inv_hom_id]; rfl
  · right
    change x ∈ Proj.basicOpen (𝒜 S) (X1 S) at hi
    rw [← Proj.opensRange_awayι (𝒜 S) (X1 S) (X_mem S 1) one_pos] at hi
    obtain ⟨y, rfl⟩ := hi
    refine ⟨(c₁ S).inv.base y, ?_⟩
    rw [i₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (c₁ S).hom, Iso.inv_hom_id]; rfl

end SchemeLevel

section Integral
variable (S : Type u) [CommRing S]
open HomogeneousLocalization

theorem toLaurent_eq_algebraMap : (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S) =
    algebraMap (Polynomial S) (LaurentPolynomial S) :=
  RingHom.ext fun f => (LaurentPolynomial.algebraMap_eq_toLaurent f).symm

scoped instance isOpenImmersion_toLaurent :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) := by
  rw [toLaurent_eq_algebraMap]
  exact IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial S)

scoped instance isOpenImmersion_toLaurentInv :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom)) := by
    change IsIso (specIso (LaurentPolynomial.invert (R := S)).toRingEquiv).hom
    infer_instance
  infer_instance

def ch : Bool → (Spec (CommRingCat.of (Polynomial S)) ⟶ Proj (𝒜 S))
  | false => i₀ S
  | true => i₁ S

scoped instance isOpenImmersion_ch (b : Bool) : IsOpenImmersion (ch S b) := by
  cases b
  · exact inferInstanceAs (IsOpenImmersion (i₀ S))
  · exact inferInstanceAs (IsOpenImmersion (i₁ S))

theorem isIntegral [IsDomain S] : IsIntegral (Proj (𝒜 S)) := by

  let 𝒰 : (Proj (𝒜 S)).OpenCover :=
    Scheme.Cover.mkOfCovers Bool (fun _ => Spec (CommRingCat.of (Polynomial S))) (ch S)
      (fun x => by
        rcases (Set.eq_univ_iff_forall.mp (cover S) x) with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨false, y, hy⟩
        · exact ⟨true, y, hy⟩)
  haveI : ∀ b, IsReduced (𝒰.X b) := fun b => inferInstanceAs (IsReduced (Spec (CommRingCat.of (Polynomial S))))
  have hred : IsReduced (Proj (𝒜 S)) := IsReduced.of_openCover _ 𝒰

  haveI : IrreducibleSpace ↥(Spec (CommRingCat.of (Polynomial S))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Polynomial S)))
  haveI : IrreducibleSpace ↥(Spec (CommRingCat.of (LaurentPolynomial S))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (LaurentPolynomial S)))
  have h0 : IsIrreducible (Set.range (i₀ S).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (i₀ S).base.hom.continuous.continuousOn

  set g := Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) with hg
  have hgopen : IsOpen (Set.range g.base) := g.isOpenEmbedding.isOpen_range
  have hgne : (Set.range g.base).Nonempty := Set.range_nonempty _
  have hgdense : Dense (Set.range g.base) := hgopen.dense hgne
  have hcl : closure (Set.range (i₀ S).base) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← cover S, Set.union_subset_iff]
    refine ⟨subset_closure, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ closure (Set.range g.base) := hgdense y
    have h1 : (i₁ S).base y ∈ closure ((i₁ S).base '' Set.range g.base) :=
      map_mem_closure (i₁ S).base.hom.continuous hy fun _ h => Set.mem_image_of_mem _ h
    refine closure_mono ?_ h1
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue S]
  have hirr : IrreducibleSpace ↥(Proj (𝒜 S)) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hcl]
    exact h0.closure
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, hred⟩

end Integral

theorem main (S : Type u) [CommRing S] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of S)) (i₀ i₁ : Spec (CommRingCat.of (Polynomial S)) ⟶ P),
      IsProper p ∧ IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      i₀ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      i₁ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ i₁ ∧
      IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))
        (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) i₀ i₁ ∧
      (IsDomain S → IsIntegral P) :=
  ⟨Proj (𝒜 S), p S, i₀ S, i₁ S, isProper_p S, inferInstance, inferInstance, i₀_p S, i₁_p S, cover S, glue S,
    isPullback_i S, fun h => @isIntegral S _ h⟩

end P1E85
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover.P1E85"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover.P1E85"

theorem solution (S : Type u) [CommRing S] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of S)) (i₀ i₁ : Spec (CommRingCat.of (Polynomial S)) ⟶ P),
      IsProper p ∧ IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      i₀ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      i₁ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) ≫ i₁ ∧
      IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))
        (Spec.map (CommRingCat.ofHom (((LaurentPolynomial.invert (R := S)).toRingEquiv.toRingHom).comp
          (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)))) i₀ i₁ ∧
      (IsDomain S → IsIntegral P) :=
  P1E85.main S

end S_AlgebraicGeometry_exists_isProper_twoAffineLineCover
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover (solution)
