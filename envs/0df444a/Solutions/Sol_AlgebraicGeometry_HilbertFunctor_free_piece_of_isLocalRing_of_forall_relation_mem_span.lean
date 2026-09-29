-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cd9754df-81d1-5a04-9a40-66665c0fa398

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzLocalLift

variable {n : ℕ}

section Pieces

variable {A : Type} [CommRing A]

theorem finite_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Finite A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem free_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Free A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) q d : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

private noncomputable def _root_.GotzLocalLift.proj (A : Type) [CommRing A] (d : ℕ) :
    MvPolynomial (Fin (n + 1)) A →ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) A d)
    ((homogeneousComponent d : MvPolynomial (Fin (n + 1)) A →ₗ[A] MvPolynomial (Fin (n + 1)) A))
    (fun p => homogeneousComponent_mem d p)

p2m_export "GotzLocalLift" "proj"
@[scoped simp] theorem proj_apply_coe (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    (proj A d p : MvPolynomial (Fin (n + 1)) A) = homogeneousComponent d p := rfl

theorem proj_of_mem (d : ℕ) (p : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    proj A d (p : MvPolynomial (Fin (n + 1)) A) = p := by
  apply Subtype.ext
  rw [proj_apply_coe, homogeneousComponent_of_mem p.2, if_pos rfl]

theorem homogeneousComponent_mul_add {F : MvPolynomial (Fin (n + 1)) A} {m : ℕ} (hF : F.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    homogeneousComponent (m + d) (a * F) = homogeneousComponent d a * F := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
    (a := a) (show F ∈ homogeneousSubmodule (Fin (n + 1)) A m from hF) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem homogeneousComponent_mul_of_lt {F : MvPolynomial (Fin (n + 1)) A} {m : ℕ} (hF : F.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) A) {e : ℕ} (he : e < m) :
    homogeneousComponent e (a * F) = 0 := by
  classical
  have := DirectSum.coe_decompose_mul_of_right_mem (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
    (a := a) e (show F ∈ homogeneousSubmodule (Fin (n + 1)) A m from hF)
  rw [decompose_eq, if_neg (not_le.mpr he)] at this
  exact this

theorem map_homogeneousComponent {B : Type} [CommRing B] (f : A →+* B) (d : ℕ)
    (p : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map f (homogeneousComponent d p) = homogeneousComponent d (MvPolynomial.map f p) := by
  ext s
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

end Pieces

section SpanF

variable {A : Type} [CommRing A] {g m : ℕ}
  (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)

theorem mem_span_iff (u : MvPolynomial (Fin (n + 1)) A) :
    u ∈ Ideal.span (Set.range F) ↔ ∃ a : Fin g → MvPolynomial (Fin (n + 1)) A, ∑ i, a i * F i = u :=
  Ideal.mem_span_range_iff_exists_fun

theorem sum_mul_mem (a : Fin g → MvPolynomial (Fin (n + 1)) A) :
    ∑ i, a i * F i ∈ Ideal.span (Set.range F) :=
  (mem_span_iff F _).mpr ⟨a, rfl⟩

include hF

theorem homogeneousComponent_sum_mul_add (a : Fin g → MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    homogeneousComponent (m + d) (∑ i, a i * F i) = ∑ i, homogeneousComponent d (a i) * F i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => homogeneousComponent_mul_add (hF i) (a i) d

theorem homogeneousComponent_sum_mul_of_lt (a : Fin g → MvPolynomial (Fin (n + 1)) A) {e : ℕ} (he : e < m) :
    homogeneousComponent e (∑ i, a i * F i) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => homogeneousComponent_mul_of_lt (hF i) (a i) he

theorem isHomogeneous_sum_mul (a : Fin g → MvPolynomial (Fin (n + 1)) A) (d : ℕ)
    (ha : ∀ i, (a i).IsHomogeneous d) : (∑ i, a i * F i).IsHomogeneous (m + d) := by
  rw [Nat.add_comm m d]
  exact IsHomogeneous.sum _ _ _ fun i _ => (ha i).mul (hF i)

theorem exists_eq_sum_of_mem (u : MvPolynomial (Fin (n + 1)) A) (hu : u ∈ Ideal.span (Set.range F)) (d : ℕ)
    (hud : u.IsHomogeneous (m + d)) :
    ∃ a : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, (a i).IsHomogeneous d) ∧ ∑ i, a i * F i = u := by
  obtain ⟨a, rfl⟩ := (mem_span_iff F _).mp hu
  refine ⟨fun i => homogeneousComponent d (a i), fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [← homogeneousComponent_sum_mul_add F hF,
    homogeneousComponent_of_mem (show ∑ i, a i * F i ∈ homogeneousSubmodule (Fin (n + 1)) A (m + d) from hud),
    if_pos rfl]

theorem eq_zero_of_mem_of_lt (u : MvPolynomial (Fin (n + 1)) A) (hu : u ∈ Ideal.span (Set.range F)) {e : ℕ}
    (he : e < m) (hue : u.IsHomogeneous e) : u = 0 := by
  obtain ⟨a, rfl⟩ := (mem_span_iff F _).mp hu
  have := homogeneousComponent_sum_mul_of_lt F hF a he
  rwa [homogeneousComponent_of_mem (show ∑ i, a i * F i ∈ homogeneousSubmodule (Fin (n + 1)) A e from hue),
    if_pos rfl] at this

theorem homogeneousComponent_mem_span {u : MvPolynomial (Fin (n + 1)) A} (hu : u ∈ Ideal.span (Set.range F))
    (e : ℕ) : homogeneousComponent e u ∈ Ideal.span (Set.range F) := by
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) A) (Set.range F)
    (by rintro _ ⟨i, rfl⟩; exact ⟨m, hF i⟩)
  have := H e hu
  rwa [decompose_eq] at this

end SpanF

section Local

variable {A : Type} [CommRing A] [IsLocalRing A]

def InM (p : MvPolynomial (Fin (n + 1)) A) : Prop := ∀ s, coeff s p ∈ IsLocalRing.maximalIdeal A

theorem inM_iff_map_eq_zero (p : MvPolynomial (Fin (n + 1)) A) :
    InM p ↔ MvPolynomial.map (IsLocalRing.residue A) p = 0 := by
  simp only [InM, MvPolynomial.ext_iff, coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff]

theorem inM_iff_mem_smul_top (p : MvPolynomial (Fin (n + 1)) A) :
    InM p ↔ p ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (MvPolynomial (Fin (n + 1)) A)) := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, MvPolynomial.algebraMap_eq, MvPolynomial.mem_map_C_iff]
  rfl

theorem InM.zero : InM (0 : MvPolynomial (Fin (n + 1)) A) := fun s => by simp

theorem InM.add {p q : MvPolynomial (Fin (n + 1)) A} (hp : InM p) (hq : InM q) : InM (p + q) := by
  rw [inM_iff_map_eq_zero] at *
  simp [hp, hq]

theorem InM.sub {p q : MvPolynomial (Fin (n + 1)) A} (hp : InM p) (hq : InM q) : InM (p - q) := by
  rw [inM_iff_map_eq_zero] at *
  simp [hp, hq]

theorem InM.mul_left {p : MvPolynomial (Fin (n + 1)) A} (q : MvPolynomial (Fin (n + 1)) A) (hp : InM p) :
    InM (q * p) := by
  rw [inM_iff_map_eq_zero] at *
  simp [hp]

theorem InM.smul {p : MvPolynomial (Fin (n + 1)) A} (a : A) (hp : InM p) : InM (a • p) := by
  rw [smul_eq_C_mul]; exact hp.mul_left _

theorem inM_smul_of_mem {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) (p : MvPolynomial (Fin (n + 1)) A) :
    InM (a • p) := fun s => by
  rw [coeff_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ ha

theorem InM.sum {ι : Type} (s : Finset ι) {p : ι → MvPolynomial (Fin (n + 1)) A} (hp : ∀ i ∈ s, InM (p i)) :
    InM (∑ i ∈ s, p i) := by
  simp only [inM_iff_map_eq_zero, map_sum] at *
  exact Finset.sum_eq_zero hp

theorem InM.homogeneousComponent {p : MvPolynomial (Fin (n + 1)) A} (hp : InM p) (d : ℕ) :
    InM (homogeneousComponent d p) := fun s => by
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact hp s
  · exact Submodule.zero_mem _

theorem inM_of_mem_smul (N : Submodule A (MvPolynomial (Fin (n + 1)) A)) {p : MvPolynomial (Fin (n + 1)) A}
    (hp : p ∈ IsLocalRing.maximalIdeal A • N) : InM p :=
  Submodule.smul_induction_on hp (fun _ ha q _ => inM_smul_of_mem ha q) (fun _ _ => InM.add)

theorem mem_smul_top_of_inM {e : ℕ} (p : ↥(homogeneousSubmodule (Fin (n + 1)) A e))
    (hp : InM (p : MvPolynomial (Fin (n + 1)) A)) :
    p ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A e)) := by
  have h1 := (inM_iff_mem_smul_top _).mp hp
  have h2 : proj A e (p : MvPolynomial (Fin (n + 1)) A) ∈
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (MvPolynomial (Fin (n + 1)) A))).map (proj A e) :=
    Submodule.mem_map_of_mem h1
  rw [Submodule.map_smul'', proj_of_mem] at h2
  exact Submodule.smul_mono le_rfl le_top h2

theorem inM_of_mem_smul_top {e : ℕ} (p : ↥(homogeneousSubmodule (Fin (n + 1)) A e))
    (hp : p ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A e))) :
    InM (p : MvPolynomial (Fin (n + 1)) A) := by
  have h2 := Submodule.mem_map_of_mem (f := (homogeneousSubmodule (Fin (n + 1)) A e).subtype) hp
  rw [Submodule.map_smul''] at h2
  exact inM_of_mem_smul _ h2

theorem one_tmul_eq_zero_iff {V : Type} [AddCommGroup V] [Module A V] (v : V) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] v = 0 ↔ v ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A V) := by
  rw [← Submodule.Quotient.mk_eq_zero (IsLocalRing.maximalIdeal A • (⊤ : Submodule A V)),
    ← (TensorProduct.quotTensorEquivQuotSMul V (IsLocalRing.maximalIdeal A)).symm.map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  exact Iff.rfl

variable {g m : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) A)

def Lifts (d : ℕ) : Prop :=
  ∀ a : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, (a i).IsHomogeneous d) → InM (∑ i, a i * F i) →
    ∃ μ : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, InM (μ i)) ∧ ∑ i, a i * F i = ∑ i, μ i * F i

theorem exists_eq_sum_of_mem_smul {y : MvPolynomial (Fin (n + 1)) A}
    (hy : y ∈ IsLocalRing.maximalIdeal A • (Ideal.span (Set.range F)).restrictScalars A) :
    ∃ μ : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, InM (μ i)) ∧ y = ∑ i, μ i * F i := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha w hw
    obtain ⟨b, rfl⟩ := (mem_span_iff F w).mp hw
    refine ⟨fun i => a • b i, fun i => inM_smul_of_mem ha _, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc a (b i) (F i)).symm
  · rintro x y ⟨μ, hμ, rfl⟩ ⟨ν, hν, rfl⟩
    refine ⟨fun i => μ i + ν i, fun i => (hμ i).add (hν i), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_mul _ _ _).symm

variable (hF : ∀ i, (F i).IsHomogeneous m)
include hF

theorem lifts_of_projective (d : ℕ) (hproj : Module.Projective A (piece (Ideal.span (Set.range F)) (m + d))) :
    Lifts F d := by
  intro a ha hInM
  set I := Ideal.span (Set.range F) with hI
  let N := ↥(homogeneousSubmodule (Fin (n + 1)) A (m + d))
  let K : Submodule A N := Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype
    (I.restrictScalars A)

  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id) (Submodule.mkQ_surjective K)
  have hs' : ∀ z, K.mkQ (s z) = z := fun z => LinearMap.congr_fun hs z
  have hr_mem : ∀ x : N, (LinearMap.id - s ∘ₗ K.mkQ : N →ₗ[A] N) x ∈ K := by
    intro x
    have h : K.mkQ ((LinearMap.id - s ∘ₗ K.mkQ : N →ₗ[A] N) x) = 0 := by
      rw [LinearMap.sub_apply, map_sub, LinearMap.comp_apply, hs', LinearMap.id_apply, sub_self]
    exact (Submodule.Quotient.mk_eq_zero K).mp h
  let r : N →ₗ[A] K := LinearMap.codRestrict K (LinearMap.id - s ∘ₗ K.mkQ : N →ₗ[A] N) hr_mem

  set y := ∑ i, a i * F i with hy
  have hyh : y ∈ homogeneousSubmodule (Fin (n + 1)) A (m + d) := isHomogeneous_sum_mul F hF a d ha
  have hyI : y ∈ I := sum_mul_mem F a
  let yN : N := ⟨y, hyh⟩
  have hyK : yN ∈ K := by
    change ((yN : N) : MvPolynomial (Fin (n + 1)) A) ∈ I
    exact hyI
  have hyN : yN ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) := mem_smul_top_of_inM yN hInM

  have hryN : (r yN : N) = yN := by
    change (LinearMap.id - s ∘ₗ K.mkQ : N →ₗ[A] N) yN = yN
    have : K.mkQ yN = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hyK
    rw [LinearMap.sub_apply, LinearMap.comp_apply, this, map_zero, LinearMap.id_apply, sub_zero]
  have h1 : r yN ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A K) := by
    have := Submodule.mem_map_of_mem (f := r) hyN
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this

  have h2 : y ∈ IsLocalRing.maximalIdeal A • I.restrictScalars A := by
    have := Submodule.mem_map_of_mem (f := (homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype ∘ₗ K.subtype) h1
    rw [Submodule.map_smul''] at this
    have hle : (⊤ : Submodule A K).map ((homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype ∘ₗ K.subtype) ≤
        I.restrictScalars A := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    have hyeq : ((homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype ∘ₗ K.subtype) (r yN) = y := by
      change ((r yN : N) : MvPolynomial (Fin (n + 1)) A) = y
      rw [hryN]
    rw [hyeq] at this
    exact Submodule.smul_mono le_rfl hle this
  obtain ⟨μ, hμ, hμeq⟩ := exists_eq_sum_of_mem_smul F h2
  exact ⟨μ, hμ, hμeq⟩

omit hF in

theorem lifts_of_forall_relation (h0 : Lifts F 0) (h1 : Lifts F 1)
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A)),
      (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A))
        {l : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A) |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧
          ∑ i, l i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0})
    (d : ℕ) : Lifts F d := by
  classical
  intro a ha hInM
  set ρ : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A) :=
    MvPolynomial.map (IsLocalRing.residue A) with hρ
  set S : Set (Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A)) :=
    {l | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * ρ (F i) = 0} with hS

  have hsyz : ∑ i, ρ (a i) * ρ (F i) = 0 := by
    have := (inM_iff_map_eq_zero _).mp hInM
    simpa [map_sum, map_mul] using this
  have hc := hrel d (fun i => ρ (a i)) (fun i => (ha i).map _) hsyz
  rw [Submodule.mem_span_iff_exists_finset_subset] at hc
  obtain ⟨cf, t, ht, -, hsum⟩ := hc

  have hlift : ∀ l ∈ S, ∃ L : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, ρ (L i) = l i) ∧ ∑ i, L i * F i = 0 := by
    rintro l ⟨⟨d', hd', hl⟩, hl0⟩
    have hex : ∀ i, ∃ Li : MvPolynomial (Fin (n + 1)) A, ρ Li = l i ∧ Li.IsHomogeneous d' := fun i => by
      obtain ⟨q, hq⟩ := MvPolynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective (l i)
      refine ⟨homogeneousComponent d' q, ?_, homogeneousComponent_isHomogeneous _ _⟩
      rw [hρ, map_homogeneousComponent, hq,
        homogeneousComponent_of_mem (show l i ∈ homogeneousSubmodule _ _ d' from hl i), if_pos rfl]
    choose L hLρ hLh using hex
    have hInM' : InM (∑ i, L i * F i) := by
      rw [inM_iff_map_eq_zero, ← hρ, map_sum]
      simpa [map_mul, hLρ] using hl0
    have hLd : Lifts F d' := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd' with rfl | rfl
      · exact h0
      · exact h1
    obtain ⟨μ, hμ, hμeq⟩ := hLd L hLh hInM'
    refine ⟨fun i => L i - μ i, fun i => ?_, ?_⟩
    · rw [map_sub, hLρ, (inM_iff_map_eq_zero _).mp (hμ i), sub_zero]
    · simp only [sub_mul, Finset.sum_sub_distrib, hμeq, sub_self]
  choose! L hLρ hL0 using hlift

  have hcf : ∀ l, ∃ C' : MvPolynomial (Fin (n + 1)) A, ρ C' = cf l := fun l =>
    MvPolynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective _
  choose Cf hCf using hcf
  refine ⟨fun i => a i - ∑ l ∈ t, Cf l * L l i, fun i => ?_, ?_⟩
  ·
    rw [inM_iff_map_eq_zero, ← hρ, map_sub, map_sum]
    have hi := congrFun hsum i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [← hi]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_mul, hCf, hLρ l (ht hl)]
  ·
    have hzero : ∑ i, (∑ l ∈ t, Cf l * L l i) * F i = 0 := by
      calc ∑ i, (∑ l ∈ t, Cf l * L l i) * F i = ∑ i, ∑ l ∈ t, Cf l * L l i * F i :=
              Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
        _ = ∑ l ∈ t, ∑ i, Cf l * L l i * F i := Finset.sum_comm
        _ = ∑ l ∈ t, Cf l * ∑ i, L l i * F i := by
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
        _ = 0 := Finset.sum_eq_zero fun l hl => by rw [hL0 l (ht hl), mul_zero]
    have : ∑ i, (a i - ∑ l ∈ t, Cf l * L l i) * F i = ∑ i, a i * F i - ∑ i, (∑ l ∈ t, Cf l * L l i) * F i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => sub_mul _ _ _
    rw [this, hzero, sub_zero]

noncomputable def presMap (d : ℕ) :
    (Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d)) →ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A (m + d)) :=
  LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) A (m + d))
    (∑ i : Fin g, LinearMap.mulRight A (F i) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) A d).subtype ∘ₗ
      LinearMap.proj i)
    (fun a => by
      have : (∑ i : Fin g, LinearMap.mulRight A (F i) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) A d).subtype ∘ₗ
          LinearMap.proj i) a = ∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i := by
        simp [LinearMap.sum_apply]
      rw [this]
      exact isHomogeneous_sum_mul F hF (fun i => (a i : MvPolynomial (Fin (n + 1)) A)) d (fun i => (a i).2))

omit [IsLocalRing A] in
theorem presMap_apply_coe (d : ℕ) (a : Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    (presMap F hF d a : MvPolynomial (Fin (n + 1)) A) = ∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i := by
  simp [presMap, LinearMap.sum_apply]

omit [IsLocalRing A] in
theorem range_presMap (d : ℕ) :
    LinearMap.range (presMap F hF d) =
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype
        ((Ideal.span (Set.range F)).restrictScalars A) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change (presMap F hF d a : MvPolynomial (Fin (n + 1)) A) ∈ Ideal.span (Set.range F)
    rw [presMap_apply_coe]
    exact sum_mul_mem F _
  · intro hx
    change (x : MvPolynomial (Fin (n + 1)) A) ∈ Ideal.span (Set.range F) at hx
    obtain ⟨a, ha, hax⟩ := exists_eq_sum_of_mem F hF x hx d x.2
    refine ⟨fun i => ⟨a i, ha i⟩, Subtype.ext ?_⟩
    rw [presMap_apply_coe]
    exact hax

theorem free_piece_add (d : ℕ) (hL : Lifts F d) : Module.Free A (piece (Ideal.span (Set.range F)) (m + d)) := by
  classical
  haveI := finite_homogeneousSubmodule (n := n) A d
  haveI := finite_homogeneousSubmodule (n := n) A (m + d)
  haveI := free_homogeneousSubmodule (n := n) A (m + d)
  set f := presMap F hF d with hf
  have hker : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField A)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField A)) := by
    intro z hz
    obtain ⟨a, rfl⟩ := TensorProduct.mk_surjective A (Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d))
      (IsLocalRing.ResidueField A) IsLocalRing.residue_surjective z
    change f.baseChange (IsLocalRing.ResidueField A) ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a) = 0 at hz
    rw [LinearMap.baseChange_tmul] at hz

    have h1 := (one_tmul_eq_zero_iff _).mp hz
    have h2 : InM (∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i) := by
      rw [← presMap_apply_coe F hF d a]
      exact inM_of_mem_smul_top _ h1
    obtain ⟨μ, hμ, hμeq⟩ := hL (fun i => (a i : MvPolynomial (Fin (n + 1)) A)) (fun i => (a i).2) h2

    let a' : Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d) := fun i =>
      ⟨homogeneousComponent d (μ i), homogeneousComponent_mem d (μ i)⟩
    have ha' : f a' = f a := by
      apply Subtype.ext
      rw [hf, presMap_apply_coe, presMap_apply_coe]
      change ∑ i, homogeneousComponent d (μ i) * F i = ∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i
      rw [← homogeneousComponent_sum_mul_add F hF μ d, ← hμeq,
        homogeneousComponent_of_mem (isHomogeneous_sum_mul F hF _ d fun i => (a i).2), if_pos rfl]
    have hker' : a - a' ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, ha', sub_self]
    have ha'mem : a' ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d))) := by
      rw [← Finset.univ_sum_single a']
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : a' i ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :=
        mem_smul_top_of_inM (a' i) ((hμ i).homogeneousComponent d)
      have := Submodule.mem_map_of_mem (f := LinearMap.single A (fun _ : Fin g => ↥(homogeneousSubmodule (Fin (n + 1)) A d)) i) hi
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have hzero : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] a' = 0 := (one_tmul_eq_zero_iff _).mpr ha'mem
    refine ⟨(1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ⟨a - a', hker'⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_sub, hzero, sub_zero]
    rfl
  have hfree := Module.free_quotient_range_of_ker_baseChange_residueField_le f hker
  rw [range_presMap F hF d] at hfree
  exact hfree

omit [IsLocalRing A] hF in

theorem free_piece_of_lt (hF : ∀ i, (F i).IsHomogeneous m) {e : ℕ} (he : e < m) :
    Module.Free A (piece (Ideal.span (Set.range F)) e) := by
  haveI := free_homogeneousSubmodule (n := n) A e
  have hbot : Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype
      ((Ideal.span (Set.range F)).restrictScalars A) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    exact eq_zero_of_mem_of_lt F hF x hx he x.2
  change Module.Free A (↥(homogeneousSubmodule (Fin (n + 1)) A e) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype ((Ideal.span (Set.range F)).restrictScalars A))
  rw [hbot]
  exact Module.Free.of_equiv (Submodule.quotEquivOfEqBot _ rfl).symm

end Local

end GotzLocalLift
p2m_reactivate "P2MW.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span.GotzLocalLift"

open GotzLocalLift in
theorem solution
    (n m g : ℕ) (A : Type) [CommRing A] [IsLocalRing A]
    (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)
    (h₀ : Module.Projective A (piece (Ideal.span (Set.range F)) m))
    (h₁ : Module.Projective A (piece (Ideal.span (Set.range F)) (m + 1)))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A)),
      (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A))
        {l : Fin g → MvPolynomial (Fin (n + 1)) (IsLocalRing.ResidueField A) |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧
          ∑ i, l i * MvPolynomial.map (IsLocalRing.residue A) (F i) = 0}) :
    ∀ e, Module.Free A (piece (Ideal.span (Set.range F)) e) := by
  have h0 : Lifts F 0 := lifts_of_projective F hF 0 h₀
  have h1 : Lifts F 1 := lifts_of_projective F hF 1 h₁
  have hL : ∀ d, Lifts F d := lifts_of_forall_relation F h0 h1 hrel
  intro e
  by_cases he : e < m
  · exact free_piece_of_lt F hF he
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp he)
    exact free_piece_add F hF d (hL d)

end S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span (solution)
