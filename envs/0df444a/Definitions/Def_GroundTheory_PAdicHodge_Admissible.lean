-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_Admissible
-- name    : GroundTheory_PAdicHodge_Admissible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:18.99352+00:00
-- url     : https://prove2.me/theorems/d6d53cca-bbad-49ab-bd0d-21337a15a059
-- title:
--   Admissible
-- statement:
--   Definitions and structural lemmas for Admissible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open TensorProduct Module
section Defs
variable (G F B : Type*) [Group G] [Field F] [CommRing B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B]
abbrev invariantRing : Subalgebra F B := FixedPoints.subalgebra F B G
variable {G F B} in
theorem mem_invariantRing {b : B} : b ∈ invariantRing G F B ↔ ∀ g : G, g • b = b := Iff.rfl
structure IsRegular [IsDomain B] : Prop where

  image_fixedPoints :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    algebraMap B (FractionRing B) '' MulAction.fixedPoints G B =
      MulAction.fixedPoints G (FractionRing B)

  isUnit_of_mem_span : ∀ b : B, b ≠ 0 → (∀ g : G, g • b ∈ Submodule.span F {b}) → IsUnit b
variable {G F} {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
noncomputable abbrev baseChangeRep : Representation F G (B ⊗[F] V) :=
  (Representation.ofDistribMulAction F G B).tprod ρ
theorem baseChangeRep_tmul (g : G) (b : B) (v : V) :
    baseChangeRep B ρ g (b ⊗ₜ v) = (g • b) ⊗ₜ ρ g v := rfl
theorem baseChangeRep_smul (g : G) (b : B) (x : B ⊗[F] V) :
    baseChangeRep B ρ g (b • x) = (g • b) • baseChangeRep B ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.smul_tmul', baseChangeRep_tmul, baseChangeRep_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, smul_mul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
theorem invariantRing_smul_eq (e : invariantRing G F B) (x : B ⊗[F] V) :
    e • x = (e : B) • x :=
  (algebraMap_smul B e x).symm
def DB : Submodule (invariantRing G F B) (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' e x hx g := by
    rw [invariantRing_smul_eq, baseChangeRep_smul, hx g, (mem_invariantRing.1 e.2) g]
theorem mem_DB {x : B ⊗[F] V} : x ∈ DB B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x := Iff.rfl
noncomputable def comparison : B ⊗[invariantRing G F B] DB B ρ →ₗ[B] B ⊗[F] V :=
  (DB B ρ).subtype.liftBaseChange B
theorem comparison_tmul (b : B) (d : DB B ρ) :
    comparison B ρ (b ⊗ₜ d) = b • (d : B ⊗[F] V) := rfl
def IsAdmissible : Prop := finrank (invariantRing G F B) (DB B ρ) = finrank F V
theorem repr_baseChangeRep {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι F V) (g : G)
    (x : B ⊗[F] V) (k : ι) :
    (Algebra.TensorProduct.basis B v).repr (baseChangeRep B ρ g x) k =
      ∑ i, algebraMap F B (LinearMap.toMatrix v v (ρ g) k i) *
        (g • (Algebra.TensorProduct.basis B v).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w =>
    rw [baseChangeRep_tmul]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, smul_mul', smul_algebraMap]
    rw [← LinearMap.toMatrix_mulVec_repr v v (ρ g) w]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy, smul_add, mul_add, Finset.sum_add_distrib]
end Defs
namespace IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
theorem isField : IsField (invariantRing G F B) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := fun {e} he => by
    have he' : (e : B) ≠ 0 := fun h0 => he (Subtype.ext h0)
    have hfix := mem_invariantRing.1 e.2
    obtain ⟨u, hu⟩ := h.isUnit_of_mem_span (e : B) he' fun g => by
      rw [hfix g]; exact Submodule.mem_span_singleton_self _
    have hinv : ∀ g : G, g • (↑u⁻¹ : B) = ↑u⁻¹ := by
      intro g
      have h1 : (e : B) * (g • (↑u⁻¹ : B)) = 1 := by
        have := congrArg (g • ·) u.mul_inv
        simp only [smul_mul', smul_one] at this
        rwa [hu, hfix g] at this
      calc g • (↑u⁻¹ : B) = (↑u⁻¹ * (e : B)) * g • ↑u⁻¹ := by rw [← hu, u.inv_mul, one_mul]
        _ = ↑u⁻¹ := by rw [mul_assoc, h1, mul_one]
    refine ⟨⟨(↑u⁻¹ : B), mem_invariantRing.2 hinv⟩, Subtype.ext ?_⟩
    change (e : B) * ↑u⁻¹ = 1
    rw [← hu, u.mul_inv]
noncomputable abbrev field : Field (invariantRing G F B) where
  toCommRing := inferInstance
  __ := h.isField.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl
theorem exists_eq_mul {c₀ c : B} (hc₀ : c₀ ≠ 0)
    (hg : ∀ g : G, (g • c₀) * c = c₀ * (g • c)) :
    ∃ e ∈ invariantRing G F B, c = e * c₀ := by
  letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
      algebraMap B (FractionRing B) (g • b) := fun g b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  have hc₀' : algebraMap B (FractionRing B) c₀ ≠ 0 := (map_ne_zero_iff _ hinj).2 hc₀
  have hx : algebraMap B (FractionRing B) c / algebraMap B (FractionRing B) c₀ ∈
      MulAction.fixedPoints G (FractionRing B) := by
    intro g
    have hgc₀ : g • c₀ ≠ 0 := by
      intro h0
      apply hc₀
      simpa using congrArg (g⁻¹ • ·) h0
    have hgc₀' : algebraMap B (FractionRing B) (g • c₀) ≠ 0 := (map_ne_zero_iff _ hinj).2 hgc₀
    rw [smul_div₀', hmap, hmap, div_eq_div_iff hgc₀' hc₀', ← map_mul, ← map_mul]
    congr 1
    linear_combination -(hg g)
  have himg : algebraMap B (FractionRing B) '' MulAction.fixedPoints G B =
      MulAction.fixedPoints G (FractionRing B) := h.image_fixedPoints
  rw [← himg] at hx
  obtain ⟨e, he, hxe⟩ := hx
  refine ⟨e, he, hinj ?_⟩
  rw [map_mul, hxe, div_mul_cancel₀ _ hc₀']
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
theorem linearIndependent {ι : Type*} {d : ι → DB B ρ}
    (hd : LinearIndependent (invariantRing G F B) d) :
    LinearIndependent B (fun i => (d i : B ⊗[F] V)) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hci₀⟩ := hne
  have hgsum : ∀ g : G, ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V) = 0 := by
    intro g
    have := congrArg (baseChangeRep B ρ g) hc
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [baseChangeRep_smul, (mem_DB B ρ).1 (d i).2 g]
  have hrel : ∀ g : G, ∀ i ∈ s, (g • c i₀) * c i = c i₀ * (g • c i) := by
    intro g
    have e1 : ∑ i ∈ s, ((g • c i₀) * c i - c i₀ * (g • c i)) • (d i : B ⊗[F] V) =
        (g • c i₀) • ∑ i ∈ s, c i • (d i : B ⊗[F] V) -
          c i₀ • ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by module
    have hsub : ∑ i ∈ s.erase i₀, ((g • c i₀) * c i - c i₀ * (g • c i)) •
        (d i : B ⊗[F] V) = 0 := by
      rw [Finset.sum_erase _ (by rw [mul_comm, sub_self, zero_smul]), e1, hc, hgsum g, smul_zero,
        smul_zero, sub_zero]
    have := ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ hsub
    intro i hi
    by_cases hii : i = i₀
    · subst hii; ring
    · exact sub_eq_zero.1 (this i (Finset.mem_erase.2 ⟨hii, hi⟩))
  choose! e he hce using fun i (hi : i ∈ s) => h.exists_eq_mul hci₀ fun g => hrel g i hi
  let e' : ι → invariantRing G F B := fun i => if hi : i ∈ s then ⟨e i, he i hi⟩ else 0
  have he' : ∀ i ∈ s, ((e' i : invariantRing G F B) : B) = e i := fun i hi => by simp [e', hi]
  have hsumB : ∑ i ∈ s, ((e' i : invariantRing G F B) : B) • (d i : B ⊗[F] V) = 0 := by
    apply (smul_right_injective (B ⊗[F] V) hci₀)
    simp only [smul_zero, Finset.smul_sum]
    rw [← hc]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_smul, he' i hi, hce i hi, mul_comm]
  have hsumE : ∑ i ∈ s, e' i • d i = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, invariantRing_smul_eq, Submodule.coe_zero]
    exact hsumB
  have := linearIndependent_iff'ₛ.1 hd s e' 0
    (by rw [hsumE]; exact (Finset.sum_eq_zero fun i _ => zero_smul _ _).symm) i₀ hi₀
  apply hci₀
  rw [hce i₀ hi₀, ← he' i₀ hi₀, this]
  simp
theorem free : Module.Free (invariantRing G F B) (DB B ρ) := by
  letI := h.field
  exact Module.Free.of_divisionRing (invariantRing G F B) (DB B ρ)
theorem finite_and_finrank_le [FiniteDimensional F V] :
    Module.Finite (invariantRing G F B) (DB B ρ) ∧
      finrank (invariantRing G F B) (DB B ρ) ≤ finrank F V := by
  letI := h.field
  haveI := h.free ρ
  have key : ∀ s : Finset (DB B ρ),
      LinearIndependent (invariantRing G F B) (fun i : s => (i : DB B ρ)) →
        s.card ≤ finrank F V := by
    intro s hs
    have := (h.linearIndependent ρ hs).fintype_card_le_finrank
    rwa [Module.finrank_baseChange, Fintype.card_coe] at this
  have hrk := rank_le key
  exact ⟨Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrk Cardinal.natCast_lt_aleph0),
    finrank_le_of_rank_le hrk⟩
theorem finite [FiniteDimensional F V] : Module.Finite (invariantRing G F B) (DB B ρ) :=
  (h.finite_and_finrank_le ρ).1
theorem comparison_surjective [FiniteDimensional F V] (hadm : IsAdmissible B ρ) :
    Function.Surjective (comparison B ρ) := by
  classical
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  let b : Basis (Fin (finrank F V)) (invariantRing G F B) (DB B ρ) :=
    Module.finBasisOfFinrankEq _ _ hadm
  let v : Basis (Fin (finrank F V)) F V := Module.finBasisOfFinrankEq F V rfl
  let e := Algebra.TensorProduct.basis B v
  let x : Fin (finrank F V) → B ⊗[F] V := fun j => (b j : B ⊗[F] V)
  have hli : LinearIndependent B x := h.linearIndependent ρ b.linearIndependent
  let a := e.toMatrix x
  have hinv : ∀ g : G,
      a = (LinearMap.toMatrix v v (ρ g)).map (algebraMap F B) * a.map (g • ·) := by
    intro g
    ext k j
    rw [Matrix.mul_apply]
    simp only [a, Basis.toMatrix_apply, Matrix.map_apply]
    have hxj : x j = baseChangeRep B ρ g (x j) := ((mem_DB B ρ).1 (b j).2 g).symm
    conv_lhs => rw [hxj]
    exact repr_baseChangeRep B ρ v g _ k
  have hdet : ∀ g : G,
      a.det = algebraMap F B (LinearMap.toMatrix v v (ρ g)).det * (g • a.det) := by
    intro g
    have h1 := (algebraMap F B).map_det (LinearMap.toMatrix v v (ρ g))
    have h2 := (MulSemiringAction.toRingHom G B g).map_det a
    rw [RingHom.mapMatrix_apply] at h1 h2
    conv_lhs => rw [hinv g]
    rw [Matrix.det_mul, h1]
    congr 1
    rw [MulSemiringAction.toRingHom_apply] at h2
    rw [h2]
    rfl
  have hne : a.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw
    have hsum : ∑ j, w j • x j = 0 := by
      apply e.repr.injective
      ext k
      have hk := congrFun hw0 k
      rw [Pi.zero_apply] at hk
      rw [map_zero, Finsupp.zero_apply, map_sum, ← hk]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct, a, Basis.toMatrix_apply, mul_comm]
    exact funext fun j => Fintype.linearIndependent_iff.1 hli w hsum j
  have hunit : IsUnit a.det := h.isUnit_of_mem_span _ hne fun g => by
    rw [Submodule.mem_span_singleton]
    refine ⟨(LinearMap.toMatrix v v (ρ g⁻¹)).det, ?_⟩
    have := congrArg (g • ·) (hdet g⁻¹)
    simp only [smul_mul', smul_algebraMap, smul_inv_smul] at this
    rw [Algebra.smul_def, ← this]
  have hspan : Submodule.span B (Set.range x) = ⊤ :=
    ((e.is_basis_iff_det).2 (by rwa [Basis.det_apply])).2
  intro y
  have hy : y ∈ Submodule.span B (Set.range x) := hspan ▸ Submodule.mem_top
  have hle : Submodule.span B (Set.range x) ≤ LinearMap.range (comparison B ρ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨1 ⊗ₜ b j, by simp [comparison_tmul, x]⟩
  exact hle hy
noncomputable def basisOfIsAdmissible [FiniteDimensional F V] (hadm : IsAdmissible B ρ)
    {ι : Type*} [Fintype ι] (b : Basis ι (invariantRing G F B) (DB B ρ)) :
    Basis ι B (B ⊗[F] V) :=
  Basis.mk (h.linearIndependent ρ b.linearIndependent) (by
    have hsub : ∀ d : DB B ρ, (d : B ⊗[F] V) ∈
        Submodule.span B (Set.range fun i => (b i : B ⊗[F] V)) := by
      intro d
      rw [← b.sum_repr d, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, invariantRing_smul_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rintro y -
    obtain ⟨z, rfl⟩ := h.comparison_surjective ρ hadm y
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => rw [comparison_tmul]; exact Submodule.smul_mem _ c (hsub d)
    | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz')
end IsRegular
end GroundTheory.PAdicHodge


