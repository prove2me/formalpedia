-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:48.029999+00:00
-- url     : https://prove2.me/theorems/f2f155e8-ba31-43d0-876c-68045c7a3031
-- title:
--   Nonempty Ray Data Of Ne Zero
-- statement:
--   Definitions and structural lemmas for Nonempty Ray Data Of Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem
open NumberField IsDedekindDomain
namespace RayCl
variable {K : Type} [Field K] [NumberField K]
def primeTo (K : Type) [Field K] [NumberField K] (M : ℕ) : Submonoid (Ideal (𝓞 K)) where
  carrier := {I | IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ I ≠ ⊥}
  mul_mem' := fun {I J} hI hJ => ⟨hI.1.mul_left hJ.1, mul_ne_zero hI.2 hJ.2⟩
  one_mem' := ⟨isCoprime_one_left, one_ne_zero⟩
theorem one_mul_mem {R : Type} [CommRing R] {A : Ideal R} {a b : R} (ha : a - 1 ∈ A) (hb : b - 1 ∈ A) : a * b - 1 ∈ A := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [e]
  exact A.add_mem (A.mul_mem_right b ha) hb
def rayCon (K : Type) [Field K] [NumberField K] (M : ℕ) : Con (primeTo K M) where
  r I J := ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ b - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧
      Ideal.span {a} * I.1 = Ideal.span {b} * J.1
  iseqv := ⟨fun I => ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp, rfl⟩,
    fun ⟨a, b, ha, hb, ha', hb', h⟩ => ⟨b, a, hb, ha, hb', ha', h.symm⟩,
    fun ⟨a, b, ha, hb, ha', hb', h⟩ ⟨c, d, hc, hd, hc', hd', h'⟩ =>
      ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, one_mul_mem ha' hc', one_mul_mem hb' hd', by
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
          mul_right_comm, h, mul_right_comm, mul_assoc, h', mul_assoc]⟩⟩
  mul' := fun ⟨a, b, ha, hb, ha', hb', h⟩ ⟨c, d, hc, hd, hc', hd', h'⟩ =>
      ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, one_mul_mem ha' hc', one_mul_mem hb' hd', by
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
          Submonoid.coe_mul, Submonoid.coe_mul, mul_mul_mul_comm, h, h', mul_mul_mul_comm]⟩
theorem exists_beta {M : ℕ} {α : 𝓞 K} (h : IsCoprime (Ideal.span {α}) (Ideal.span {(M : 𝓞 K)})) :
    ∃ β : 𝓞 K, β ≠ 0 ∧ β * α - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  by_cases hβ : β = 0
  · subst hβ
    refine ⟨1, one_ne_zero, ?_⟩
    have hj1 : j = 1 := by simpa using hij
    rw [Ideal.eq_top_of_isUnit_mem _ hj (by rw [hj1]; exact isUnit_one)]
    exact Submodule.mem_top
  · refine ⟨β, hβ, ?_⟩
    have e : β * α - 1 = -j := by rw [← hij]; ring
    rw [e]
    exact neg_mem hj
def icl {M : ℕ} (I : primeTo K M) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.2⟩
theorem exists_compl {M : ℕ} (I : primeTo K M) : ∃ L : primeTo K M, ∀ J : primeTo K M, icl J = icl I →
    ∃ α : 𝓞 K, J.1 * L.1 = Ideal.span {α} := by
  have hle : primeTo K M ≤ nonZeroDivisors (Ideal (𝓞 K)) := fun J hJ => mem_nonZeroDivisors_of_ne_zero hJ.2
  let φ : primeTo K M →* ClassGroup (𝓞 K) := ClassGroup.mk0.comp (Submonoid.inclusion hle)
  have hφ : ∀ J, φ J = icl J := fun J => rfl
  refine ⟨I ^ (Fintype.card (ClassGroup (𝓞 K)) - 1), fun J hJ => ?_⟩
  have h1 : φ (J * I ^ (Fintype.card (ClassGroup (𝓞 K)) - 1)) = 1 := by
    rw [map_mul, map_pow, hφ J, hJ, ← hφ I, ← pow_succ', Nat.sub_add_cancel Fintype.card_pos,
      pow_card_eq_one]
  rw [hφ, icl, ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨⟨α, hα⟩⟩ := h1
  exact ⟨α, hα⟩
theorem finite_quot {M : ℕ} (hM : M ≠ 0) : Finite (rayCon K M).Quotient := by
  classical
  have hMne : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM
  have : Finite (𝓞 K ⧸ Ideal.span {(M : 𝓞 K)}) :=
    (Ideal.absNorm_ne_zero_iff _).mp (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hL : ∀ c : ClassGroup (𝓞 K), ∃ L : primeTo K M, ∀ J : primeTo K M, icl J = c →
      ∃ α : 𝓞 K, J.1 * L.1 = Ideal.span {α} := by
    intro c
    by_cases hc : ∃ I : primeTo K M, icl I = c
    · obtain ⟨I, rfl⟩ := hc
      exact exists_compl I
    · exact ⟨1, fun J hJ => (hc ⟨J, hJ⟩).elim⟩
  choose L hL using hL
  have hα : ∀ J : primeTo K M, ∃ α : 𝓞 K, J.1 * (L (icl J)).1 = Ideal.span {α} :=
    fun J => hL _ J rfl
  choose α hα using hα
  have hne : ∀ J : primeTo K M, α J ≠ 0 := by
    intro J h0
    have hb : Ideal.span {α J} ≠ ⊥ := by
      rw [← hα J]
      exact mul_ne_zero J.2.2 (L (icl J)).2.2
    exact hb (Ideal.span_singleton_eq_bot.mpr h0)
  let f : primeTo K M → ClassGroup (𝓞 K) × (𝓞 K ⧸ Ideal.span {(M : 𝓞 K)}) :=
    fun J => (icl J, Ideal.Quotient.mk _ (α J))
  have key : ∀ J₁ J₂ : primeTo K M, f J₁ = f J₂ → rayCon K M J₁ J₂ := by
    intro J₁ J₂ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨hc, hm⟩ := h
    have h₁ := hα J₁
    have h₂ := hα J₂
    rw [hc] at h₁
    have hcop : IsCoprime (Ideal.span {α J₁}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [← h₁]
      exact J₁.2.1.mul_left (L (icl J₂)).2.1
    obtain ⟨β, hβ, hβα⟩ := exists_beta hcop
    refine ⟨β * α J₂, β * α J₁, mul_ne_zero hβ (hne J₂), mul_ne_zero hβ (hne J₁), ?_, hβα, ?_⟩
    · have e : β * α J₂ - 1 = (β * α J₁ - 1) - β * (α J₁ - α J₂) := by ring
      rw [e]
      exact sub_mem hβα (Ideal.mul_mem_left _ _ (Ideal.Quotient.eq.mp hm))
    · apply mul_right_cancel₀ (b := (L (icl J₂)).1) (L (icl J₂)).2.2
      rw [mul_assoc, h₁, mul_assoc, h₂, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton,
        show β * α J₂ * α J₁ = β * α J₁ * α J₂ by ring]
  refine Finite.of_injective (fun q : (rayCon K M).Quotient => f (Quotient.out q)) fun q₁ q₂ h => ?_
  rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
  exact Quotient.sound (key _ _ h)
theorem exists_inv {M : ℕ} (q : (rayCon K M).Quotient) : IsUnit q := by
  obtain ⟨I, rfl⟩ := (rayCon K M).mk'_surjective q
  obtain ⟨L, hL⟩ := exists_compl I
  obtain ⟨α, hα⟩ := hL I rfl
  have hcop : IsCoprime (Ideal.span {α}) (Ideal.span {(M : 𝓞 K)}) := by
    rw [← hα]
    exact I.2.1.mul_left L.2.1
  obtain ⟨β, hβ, hβα⟩ := exists_beta hcop
  have hβcop : IsCoprime (Ideal.span {β}) (Ideal.span {(M : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨β * α, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self β), 1 - β * α, ?_, by ring⟩
    have hn := neg_mem hβα
    rwa [neg_sub] at hn
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact mul_ne_zero I.2.2 L.2.2 (by rw [hα]; exact Ideal.span_singleton_eq_bot.mpr rfl)
  let L' : primeTo K M := L * ⟨Ideal.span {β}, hβcop, by rwa [Ne, Ideal.span_singleton_eq_bot]⟩
  refine isUnit_iff_exists_inv.mpr ⟨(rayCon K M).mk' L', ?_⟩
  rw [← map_mul, ← map_one (rayCon K M).mk']
  refine (Con.eq _).mpr ⟨1, β * α, one_ne_zero, mul_ne_zero hβ hα0, by simp, hβα, ?_⟩
  simp only [L', Submonoid.coe_mul, Submonoid.coe_one]
  rw [Ideal.span_singleton_one, Ideal.top_mul, mul_one, ← mul_assoc, hα,
    Ideal.span_singleton_mul_span_singleton, mul_comm α β]
theorem ne_bot_of_cop {M : ℕ} (hM : 2 ≤ M) {I : Ideal (𝓞 K)} (h : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  have htop : Ideal.span {(M : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_add, Ideal.add_eq_sup, bot_sup_eq, Ideal.one_eq_top] at h
    exact h
  have h1 := congrArg Ideal.absNorm htop
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top, ← map_natCast (algebraMap ℤ (𝓞 K)) M,
    Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
  rcases Nat.pow_eq_one.mp h1 with h2 | h2
  · omega
  · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h2
open Classical in

def rcl (M : ℕ) (I : Ideal (𝓞 K)) : (rayCon K M).Quotient :=
  if h : I ∈ primeTo K M then (rayCon K M).mk' ⟨I, h⟩ else 1
theorem rcl_of {M : ℕ} {I : Ideal (𝓞 K)} (h : I ∈ primeTo K M) : rcl M I = (rayCon K M).mk' ⟨I, h⟩ := by
  rw [rcl, dif_pos h]
theorem rcl_mul {M : ℕ} {I J : Ideal (𝓞 K)} (h1 : I ∈ primeTo K M) (h2 : J ∈ primeTo K M) :
    rcl M (I * J) = rcl M I * rcl M J := by
  rw [rcl_of (mul_mem h1 h2), rcl_of h1, rcl_of h2, ← map_mul]
  rfl
end RayCl
def RayGroup (K : Type) [Field K] [NumberField K] (M : ℕ) : Type := (RayCl.rayCon K M).Quotient
instance (K : Type) [Field K] [NumberField K] (M : ℕ) : CommGroup (RayGroup K M) :=
  @commGroupOfIsUnit (RayCl.rayCon K M).Quotient _ RayCl.exists_inv
instance (K : Type) [Field K] [NumberField K] (M : ℕ) [NeZero M] : Finite (RayGroup K M) :=
  RayCl.finite_quot (NeZero.ne M)
structure RayData (K : Type) [Field K] [NumberField K] (M : ℕ) where

  G : Type
  [grp : CommGroup G]
  [fin : Fintype G]

  cls : Ideal (𝓞 K) → G
  cls_mul : ∀ I J, IsCoprime I (Ideal.span {(M : 𝓞 K)}) → IsCoprime J (Ideal.span {(M : 𝓞 K)}) →
    ∀ (_hI : I ≠ ⊥ := by
        first
          | assumption | exact top_ne_bot | exact one_ne_zero
          | exact GlobalTheory.Mem.RayCl.ne_bot_of_cop (by assumption) (by assumption))
      (_hJ : J ≠ ⊥ := by
        first
          | assumption | exact top_ne_bot | exact one_ne_zero
          | exact GlobalTheory.Mem.RayCl.ne_bot_of_cop (by assumption) (by assumption)),
      cls (I * J) = cls I * cls J
  cls_surj : ∀ c, ∃ I, IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ I ≠ ⊥ ∧ cls I = c
  cls_eq : ∀ I J, IsCoprime I (Ideal.span {(M : 𝓞 K)}) → IsCoprime J (Ideal.span {(M : 𝓞 K)}) → I ≠ ⊥ → J ≠ ⊥ →
    (cls I = cls J ↔ ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ b - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧
      Ideal.span {a} * I = Ideal.span {b} * J)
attribute [instance] RayData.grp RayData.fin
def rayData (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : M ≠ 0) : RayData K M where
  G := RayGroup K M
  fin := @Fintype.ofFinite _ (RayCl.finite_quot hM)
  cls := RayCl.rcl M
  cls_mul _ _ hI hJ hI' hJ' := RayCl.rcl_mul ⟨hI, hI'⟩ ⟨hJ, hJ'⟩
  cls_surj c := by
    obtain ⟨I, rfl⟩ := (RayCl.rayCon K M).mk'_surjective c
    exact ⟨I.1, I.2.1, I.2.2, RayCl.rcl_of I.2⟩
  cls_eq I J hI hJ hI' hJ' := by
    rw [RayCl.rcl_of (show I ∈ RayCl.primeTo K M from ⟨hI, hI'⟩),
      RayCl.rcl_of (show J ∈ RayCl.primeTo K M from ⟨hJ, hJ'⟩)]
    exact Con.eq _
namespace RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
def cnt (c : D.G) (n : ℕ) : ℂ :=
  (Nat.card {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} : ℕ)
def coef (χ : D.G →* ℂˣ) (n : ℕ) : ℂ := ∑ c : D.G, (χ c : ℂ) * D.cnt c n
def Pr (_D : RayData K M) : Type := {v : HeightOneSpectrum (𝓞 K) // IsCoprime v.asIdeal (Ideal.span {(M : 𝓞 K)})}
theorem cls_one : D.cls 1 = 1 := by
  have h := D.cls_mul 1 1 isCoprime_one_left isCoprime_one_left one_ne_zero one_ne_zero
  rw [one_mul] at h
  exact mul_left_cancel (a := D.cls 1) (by rw [mul_one]; exact h.symm)
theorem cls_eq_one_iff {I : Ideal (𝓞 K)} (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI' : I ≠ ⊥) :
    D.cls I = 1 ↔ ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ b - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧
      Ideal.span {a} * I = Ideal.span {b} := by
  rw [← D.cls_one, D.cls_eq I 1 hI isCoprime_one_left hI' one_ne_zero]
  simp only [mul_one]
theorem cls_span {a : 𝓞 K} (ha : a ≠ 0) (h : a - 1 ∈ Ideal.span {(M : 𝓞 K)}) : D.cls (Ideal.span {a}) = 1 := by
  have hcop : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨a, Ideal.mem_span_singleton_self a, 1 - a, ?_, by ring⟩
    have hn := neg_mem h
    rwa [neg_sub] at hn
  refine (D.cls_eq_one_iff hcop (by rwa [Ne, Ideal.span_singleton_eq_bot])).mpr
    ⟨1, a, one_ne_zero, ha, by simp, h, ?_⟩
  rw [Ideal.span_singleton_one, Ideal.top_mul]
def clsHom : RayCl.primeTo K M →* D.G where
  toFun I := D.cls I.1
  map_one' := D.cls_one
  map_mul' I J := D.cls_mul I.1 J.1 I.2.1 J.2.1 I.2.2 J.2.2
theorem clsHom_surjective : Function.Surjective D.clsHom := by
  intro c
  obtain ⟨I, hI, hI', rfl⟩ := D.cls_surj c
  exact ⟨⟨I, hI, hI'⟩, rfl⟩
theorem ker_clsHom : Con.ker D.clsHom = RayCl.rayCon K M := by
  ext I J
  rw [Con.ker_rel]
  exact D.cls_eq I.1 J.1 I.2.1 J.2.1 I.2.2 J.2.2
def equivRayGroup : RayGroup K M ≃* D.G :=
  MulEquiv.ofBijective ((RayCl.rayCon K M).lift D.clsHom D.ker_clsHom.ge)
    ⟨fun x y h => by
      obtain ⟨I, rfl⟩ := (RayCl.rayCon K M).mk'_surjective x
      obtain ⟨J, rfl⟩ := (RayCl.rayCon K M).mk'_surjective y
      exact (Con.eq _).2 (D.ker_clsHom.le (show Con.ker D.clsHom I J from h)),
     Con.lift_surjective_of_surjective _ D.clsHom_surjective⟩
theorem card_eq_classNumber (D : RayData K 1) : Fintype.card D.G = classNumber K := by
  classical
  have htop : Ideal.span {((1 : ℕ) : 𝓞 K)} = ⊤ := by
    rw [Nat.cast_one, Ideal.span_singleton_one]
  have hcop : ∀ I : Ideal (𝓞 K), IsCoprime I (Ideal.span {((1 : ℕ) : 𝓞 K)}) := fun I => by
    rw [htop, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hmod : ∀ x : 𝓞 K, x ∈ Ideal.span {((1 : ℕ) : 𝓞 K)} := fun x => by
    rw [htop]
    exact Submodule.mem_top
  have heq : ∀ (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥),
      D.cls I = D.cls J ↔ ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ =
        ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ := by
    intro I J hI hJ
    rw [D.cls_eq I J (hcop I) (hcop J) hI hJ, ClassGroup.mk0_eq_mk0_iff]
    constructor
    · rintro ⟨a, b, ha, hb, -, -, h⟩
      exact ⟨a, b, ha, hb, h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, ha, hb, hmod _, hmod _, h⟩
  choose r hr using D.cls_surj
  let f : D.G → ClassGroup (𝓞 K) := fun c =>
    ClassGroup.mk0 ⟨r c, mem_nonZeroDivisors_of_ne_zero (hr c).2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      rw [← (hr c).2.2, ← (hr c').2.2]
      exact (heq _ _ (hr c).2.1 (hr c').2.1).mpr h
    · intro x
      obtain ⟨⟨J, hJ⟩, rfl⟩ := ClassGroup.mk0_surjective x
      have hJ' : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
      exact ⟨D.cls J, (heq _ _ (hr _).2.1 hJ').mp (hr _).2.2⟩
  rw [NumberField.classNumber]
  exact Fintype.card_of_bijective hf
theorem cls_two_ne_one (D : RayData ℚ 5) : D.cls (Ideal.span {2}) ≠ 1 := by
  have hcop : IsCoprime (Ideal.span {(2 : 𝓞 ℚ)}) (Ideal.span {((5 : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨2 * (-2), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2),
      ((5 : ℕ) : 𝓞 ℚ) * 1, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
    push_cast
    ring
  have h2 : Ideal.span {(2 : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  intro h
  obtain ⟨a, b, -, -, ha1, hb1, hab⟩ := (D.cls_eq_one_iff hcop h2).mp h
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton] at hab
  have hab' := hab.map Rat.ringOfIntegersEquiv
  rw [map_mul, map_ofNat] at hab'
  have ha5 : (5 : ℤ) ∣ Rat.ringOfIntegersEquiv a - 1 := by
    have hd := map_dvd Rat.ringOfIntegersEquiv (Ideal.mem_span_singleton.mp ha1)
    rw [map_natCast, map_sub, map_one] at hd
    exact_mod_cast hd
  have hb5 : (5 : ℤ) ∣ Rat.ringOfIntegersEquiv b - 1 := by
    have hd := map_dvd Rat.ringOfIntegersEquiv (Ideal.mem_span_singleton.mp hb1)
    rw [map_natCast, map_sub, map_one] at hd
    exact_mod_cast hd
  rcases Int.associated_iff.mp hab' with h' | h' <;> omega
end RayData
example : Nontrivial (rayData ℚ 5 (by norm_num)).G := ⟨_, _, RayData.cls_two_ne_one _⟩
example (K : Type) [Field K] [NumberField K] : Fintype.card (rayData K 1 one_ne_zero).G = classNumber K :=
  RayData.card_eq_classNumber _
example : (rayData ℚ 5 (by norm_num)).cls (Ideal.span {6}) = 1 :=
  RayData.cls_span _ (by norm_num) (Ideal.mem_span_singleton.2 ⟨1, by push_cast; norm_num⟩)
end GlobalTheory.Mem
end


