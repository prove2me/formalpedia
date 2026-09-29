-- Prove2me | solution 1 for AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5fadd70f-0da4-5e88-89e4-10b607825b24

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along FiniteAlong finrankAlong IsCurveOver linearIndependent_of_constantFieldExtension"
namespace TraceBaseChangeProof
p2m_open "AlgebraicCurve"

section Finite

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem exists_finset_adjoin_eq_top
    (hfg : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') :
    ∃ G : Finset F', IntermediateField.adjoin K (G : Set F') = ⊤ := by
  classical
  obtain ⟨x, -, hxfin⟩ := hfg
  set Kx := IntermediateField.adjoin K ({x} : Set F')
  haveI := hxfin
  let b := Module.finBasis Kx F'
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  have hset : ((insert x (Finset.univ.image b) : Finset F') : Set F') = {x} ∪ Set.range b := by
    ext y
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range, Set.singleton_union]
  rw [hset, ← IntermediateField.adjoin_adjoin_left]
  have htop : IntermediateField.adjoin Kx (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hspan : f ∈ Submodule.span Kx (Set.range b) := by
      rw [b.span_eq]; trivial
    have hle : Submodule.span Kx (Set.range b) ≤
        (IntermediateField.adjoin Kx (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.2 (fun y hy => IntermediateField.subset_adjoin Kx _ hy)
    exact hle hspan
  rw [htop]
  rfl

theorem finiteAlong_of_isIntegral_of_adjoin_eq_top (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (T : Finset F')
    (hT : IntermediateField.adjoin K (T : Set F') = ⊤) : FiniteAlong K φ := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin F (T : Set F') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin K (T : Set F') ≤
        (IntermediateField.adjoin F (T : Set F')).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have hy : y ∈ IntermediateField.adjoin K (T : Set F') := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional F (IntermediateField.adjoin F (T : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin F (T : Set F')) ≃ₗ[F] F' :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

theorem finiteAlong_of_hfg (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfg : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') : FiniteAlong K φ := by
  obtain ⟨T, hT⟩ := exists_finset_adjoin_eq_top (K := K) (F' := F') hfg
  exact finiteAlong_of_isIntegral_of_adjoin_eq_top φ hφ T hT

end Finite

section Span

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
  [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE]

variable (E F FE) in

def spanEF : Submodule E FE := Submodule.span E (Set.range (algebraMap F FE))

theorem mul_mem_spanEF {a b : FE} (ha : a ∈ spanEF F E FE) (hb : b ∈ spanEF F E FE) :
    a * b ∈ spanEF F E FE := by
  unfold spanEF at *
  induction ha using Submodule.span_induction generalizing b with
  | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          rw [← map_mul]
          exact Submodule.subset_span ⟨f * g, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul e y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ e hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ (hx hb) (hy hb)
  | smul e x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ e (hx hb)

theorem one_mem_spanEF : (1 : FE) ∈ spanEF F E FE :=
  Submodule.subset_span ⟨1, map_one _⟩

theorem algebraMap_E_mem_spanEF (e : E) : algebraMap E FE e ∈ spanEF F E FE := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ e one_mem_spanEF

theorem prod_mem_spanEF {ι : Type*} (s : Finset ι) (q : ι → FE) (hq : ∀ i ∈ s, q i ∈ spanEF F E FE) :
    ∏ i ∈ s, q i ∈ spanEF F E FE := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one_mem_spanEF
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_mem_spanEF (hq a (Finset.mem_insert_self a s))
        (ih fun i hi => hq i (Finset.mem_insert_of_mem hi))

def spanEFRing : Subring FE where
  carrier := spanEF F E FE
  mul_mem' ha hb := mul_mem_spanEF ha hb
  one_mem' := one_mem_spanEF
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  neg_mem' ha := Submodule.neg_mem _ ha

theorem exists_div_of_adjoin_eq_top
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) (z : FE) :
    ∃ p q : FE, p ∈ spanEF F E FE ∧ q ∈ spanEF F E FE ∧ q ≠ 0 ∧ z = p / q := by
  have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F FE)) := by rw [hgen]; trivial
  have hz' : z ∈ Subfield.closure (Set.range (algebraMap E FE) ∪ Set.range (algebraMap F FE)) := hz
  rw [Subfield.mem_closure_iff] at hz'
  obtain ⟨y, hy, w, hw, hyw⟩ := hz'
  have hsub : Subring.closure (Set.range (algebraMap E FE) ∪ Set.range (algebraMap F FE)) ≤
      (spanEFRing (E := E) (F := F) (FE := FE)) := by
    rw [Subring.closure_le]
    rintro a (⟨e, rfl⟩ | ⟨f, rfl⟩)
    · exact algebraMap_E_mem_spanEF e
    · exact Submodule.subset_span ⟨f, rfl⟩
  have hy' : y ∈ spanEF F E FE := hsub hy
  have hw' : w ∈ spanEF F E FE := hsub hw
  by_cases hw0 : w = 0
  · refine ⟨0, 1, Submodule.zero_mem _, one_mem_spanEF, one_ne_zero, ?_⟩
    rw [← hyw, hw0, div_zero, zero_div]
  · exact ⟨y, w, hy', hw', hw0, hyw.symm⟩

theorem exists_linearIndependent_repr {d : ℕ} (c : Fin d → FE) (hc : ∀ j, c j ∈ spanEF F E FE) :
    ∃ (r : ℕ) (u : Fin r → F), LinearIndependent K u ∧
      ∀ j, ∃ e : Fin r → E, c j = ∑ m, e m • algebraMap F FE (u m) := by
  classical

  have hfin : ∀ j, ∃ S : Finset F, c j ∈ Submodule.span E ((S.image (algebraMap F FE) : Finset FE) : Set FE) := by
    intro j
    obtain ⟨T, hT, hcT⟩ := Submodule.mem_span_finite_of_mem_span (hc j)
    obtain ⟨S, -, hS⟩ := Finset.subset_set_image_iff.1
      (show (T : Set FE) ⊆ algebraMap F FE '' Set.univ by rwa [Set.image_univ])
    exact ⟨S, by rwa [hS]⟩
  choose S hS using hfin
  set Sall : Finset F := Finset.univ.biUnion S with hSall

  set V : Submodule K F := Submodule.span K (Sall : Set F) with hV
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K Sall.finite_toSet
  set bV := Module.finBasis K V
  refine ⟨Module.finrank K V, fun m => (bV m : F), ?_, fun j => ?_⟩
  · exact bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  ·
    have hmem : ∀ f ∈ Sall, algebraMap F FE f ∈
        Submodule.span E (Set.range fun m => algebraMap F FE (bV m : F)) := by
      intro f hf
      have hfV : f ∈ V := Submodule.subset_span hf
      have hrepr := bV.sum_repr ⟨f, hfV⟩
      have hf' : f = ∑ m, bV.repr ⟨f, hfV⟩ m • (bV m : F) := by
        have := congrArg Subtype.val hrepr
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
      rw [hf', map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K E FE, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have hle : Submodule.span E ((S j).image (algebraMap F FE) : Set FE) ≤
        Submodule.span E (Set.range fun m => algebraMap F FE (bV m : F)) := by
      rw [Submodule.span_le]
      intro a ha
      rw [Finset.coe_image] at ha
      obtain ⟨f, hf, rfl⟩ := ha
      exact hmem f (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hf⟩)
    have := hle (hS j)
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, he.symm⟩

end Span

section Independence

variable {K F F' E FE F'E : Type*} [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
  [Algebra K F] [Algebra K F'] [Algebra K E]
  [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
  [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]

theorem linearIndependent_along_baseChange
    (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hli : ∀ {ι : Type} [Fintype ι] (g : ι → F'), LinearIndependent K g →
      LinearIndependent E (fun i => algebraMap F' F'E (g i)))
    {d : ℕ} (b : Fin d → F') (hb : letI := algebraAlong φ; LinearIndependent F b) :
    letI := algebraAlong φE
    LinearIndependent FE (fun j => algebraMap F' F'E (b j)) := by
  classical
  letI : Algebra F F' := algebraAlong φ
  letI : Algebra FE F'E := algebraAlong φE
  have hsmulF : ∀ (s : F) (y : F'), s • y = φ s * y := fun s y => rfl
  have hsmulFE : ∀ (s : FE) (y : F'E), s • y = φE s * y := fun s y => rfl

  have hcore : ∀ c : Fin d → FE, (∀ j, c j ∈ spanEF F E FE) →
      ∑ j, c j • algebraMap F' F'E (b j) = 0 → ∀ j, c j = 0 := by
    intro c hc hrel
    obtain ⟨r, u, hu, he⟩ := exists_linearIndependent_repr (K := K) c hc
    choose e he using he

    have hG : LinearIndependent K (fun mj : Fin r × Fin d => φ (u mj.1) * b mj.2) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hsum : ∑ j, (∑ m, a (m, j) • u m) • b j = 0 := by
        have : ∑ mj : Fin r × Fin d, a mj • (φ (u mj.1) * b mj.2) =
            ∑ j, (∑ m, a (m, j) • u m) • b j := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmulF, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]
        rw [← this]; exact ha
      have h1 := Fintype.linearIndependent_iff.1 hb (fun j => ∑ m, a (m, j) • u m) hsum
      intro mj
      have h2 := Fintype.linearIndependent_iff.1 hu (fun m => a (m, mj.2)) (h1 mj.2) mj.1
      exact h2
    have hG' := hli _ hG

    have hrel' : ∑ mj : Fin r × Fin d,
        e mj.2 mj.1 • algebraMap F' F'E (φ (u mj.1) * b mj.2) = 0 := by
      have : ∑ mj : Fin r × Fin d, e mj.2 mj.1 • algebraMap F' F'E (φ (u mj.1) * b mj.2) =
          ∑ j, c j • algebraMap F' F'E (b j) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsmulFE, he j, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_smul, hφcomm, map_mul, Algebra.smul_def, Algebra.smul_def, mul_assoc]
      rw [this]; exact hrel
    have h0 := Fintype.linearIndependent_iff.1 hG' (fun mj => e mj.2 mj.1) hrel'
    intro j
    rw [he j]
    refine Finset.sum_eq_zero fun m _ => ?_
    have h0' : e j m = 0 := h0 (m, j)
    rw [h0', zero_smul]

  rw [Fintype.linearIndependent_iff]
  intro c hrel
  choose p q hp hq hq0 hcpq using fun j => exists_div_of_adjoin_eq_top hgen (c j)
  set Q : FE := ∏ j, q j with hQ
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hq0 j
  have hc' : ∀ j, c j * Q ∈ spanEF F E FE := by
    intro j
    have : c j * Q = p j * ∏ k ∈ Finset.univ.erase j, q k := by
      have hqj : q j ≠ 0 := hq0 j
      rw [hcpq j, hQ, ← Finset.prod_erase_mul Finset.univ q (Finset.mem_univ j)]
      field_simp
    rw [this]
    exact mul_mem_spanEF (hp j) (prod_mem_spanEF _ q fun k _ => hq k)
  have hrel' : ∑ j, (c j * Q) • algebraMap F' F'E (b j) = 0 := by
    have : ∑ j, (c j * Q) • algebraMap F' F'E (b j) = φE Q * ∑ j, c j • algebraMap F' F'E (b j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsmulFE, hsmulFE, map_mul]; ring
    rw [this, hrel, mul_zero]
  intro j
  have := hcore (fun j => c j * Q) hc' hrel' j
  exact (mul_eq_zero.1 this).resolve_right hQ0

end Independence

end AlgebraicCurve.TraceBaseChangeProof

open AlgebraicCurve.TraceBaseChangeProof in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hφE : φE.toRingHom.IsIntegral) :
    FiniteAlong K φ ∧ FiniteAlong E φE ∧ finrankAlong E φE = finrankAlong K φ ∧
    ∀ u : F',
      (letI := algebraAlong φE; Algebra.trace FE F'E (algebraMap F' F'E u)) =
        algebraMap F FE (letI := algebraAlong φ; Algebra.trace F F' u) := by
  classical

  have hfinφ : FiniteAlong K φ := finiteAlong_of_hfg φ hφ hfg'
  have hfinφE : FiniteAlong E φE := finiteAlong_of_hfg φE hφE hfgE'
  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  haveI : Module.Finite F F' := hfinφ
  letI : Algebra FE F'E := algebraAlong φE
  haveI : IsScalarTower E FE F'E := isScalarTower_along φE
  haveI : Module.Finite FE F'E := hfinφE
  have hsmulFE : ∀ (s : FE) (y : F'E), s • y = φE s * y := fun s y => rfl

  set b := Module.finBasis F F' with hb
  set d := Module.finrank F F' with hd

  have hli : LinearIndependent FE (fun j => algebraMap F' F'E (b j)) := by
    refine linearIndependent_along_baseChange (K := K) φ φE hφcomm hgen ?_ b b.linearIndependent
    intro ι _ g hg
    exact AlgebraicCurve.linearIndependent_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' hg

  have hspan : ⊤ ≤ Submodule.span FE (Set.range fun j => algebraMap F' F'E (b j)) := by

    have hF' : ∀ u : F', algebraMap F' F'E u ∈
        Submodule.span FE (Set.range fun j => algebraMap F' F'E (b j)) := by
      intro u
      have hu : u = ∑ j, b.repr u j • b j := (b.sum_repr u).symm
      rw [hu, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : algebraMap F' F'E (b.repr u j • b j) =
          (algebraMap F FE (b.repr u j)) • algebraMap F' F'E (b j) := by
        rw [hsmulFE, hφcomm, Algebra.smul_def, map_mul]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

    haveI : Algebra.IsIntegral FE F'E := ⟨fun z => hφE z⟩
    haveI : Algebra.IsAlgebraic FE F'E := Algebra.IsIntegral.isAlgebraic
    set A : Subalgebra FE F'E := Algebra.adjoin FE (Set.range (algebraMap F' F'E)) with hA
    have hAfield : IsField A := Subalgebra.isField_of_algebraic A
    have hAinv : ∀ z ∈ A, z⁻¹ ∈ A := by
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0, inv_zero]; exact A.zero_mem
      · obtain ⟨w, hw⟩ := hAfield.mul_inv_cancel (a := ⟨z, hz⟩) (fun h => hz0 (congrArg Subtype.val h))
        have hw' : z * (w : F'E) = 1 := congrArg Subtype.val hw
        have : (w : F'E) = z⁻¹ :=
          (mul_eq_one_iff_eq_inv₀ hz0).1 (by rw [mul_comm]; exact hw')
        rw [← this]; exact w.2
    set A' : IntermediateField E F'E := (A.restrictScalars E).toIntermediateField
      (fun z hz => hAinv z hz) with hA'
    have hA'top : (⊤ : IntermediateField E F'E) ≤ A' := by
      rw [← hgen', IntermediateField.adjoin_le_iff]
      rintro _ ⟨u, rfl⟩
      show algebraMap F' F'E u ∈ A
      exact Algebra.subset_adjoin ⟨u, rfl⟩
    have hAtop : ∀ z : F'E, z ∈ A := fun z => hA'top (IntermediateField.mem_top (x := z))

    intro z _
    have hz : z ∈ Subalgebra.toSubmodule A := hAtop z
    rw [hA, Algebra.adjoin_eq_span] at hz
    have hclos : (Submonoid.closure (Set.range (algebraMap F' F'E)) : Set F'E) ⊆
        Set.range (algebraMap F' F'E) := by
      intro y hy
      have hle : Submonoid.closure (Set.range (algebraMap F' F'E)) ≤
          MonoidHom.mrange ((algebraMap F' F'E : F' →+* F'E) : F' →* F'E) :=
        Submonoid.closure_le.2 (by rintro _ ⟨u, rfl⟩; exact ⟨u, rfl⟩)
      obtain ⟨u, hu⟩ := hle hy
      exact ⟨u, hu⟩
    refine (Submodule.span_le.2 ?_) (Submodule.span_mono hclos hz)
    rintro _ ⟨u, rfl⟩
    exact hF' u
  set bE : Module.Basis (Fin d) FE F'E := Module.Basis.mk hli hspan with hbE
  have hbE_apply : ∀ j, bE j = algebraMap F' F'E (b j) := fun j => by
    rw [hbE, Module.Basis.mk_apply]

  have hdeg : finrankAlong E φE = finrankAlong K φ := by
    show Module.finrank FE F'E = Module.finrank F F'
    rw [Module.finrank_eq_card_basis bE, Fintype.card_fin]
  refine ⟨hfinφ, hfinφE, hdeg, fun u => ?_⟩

  show Algebra.trace FE F'E (algebraMap F' F'E u) = algebraMap F FE (Algebra.trace F F' u)
  rw [Algebra.trace_eq_matrix_trace bE, Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]

  have hexp : algebraMap F' F'E u * bE i =
      ∑ k, algebraMap F FE (b.repr (u * b i) k) • bE k := by
    rw [hbE_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (u * b i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbE_apply, hsmulFE, hφcomm, Algebra.smul_def, map_mul]
    rfl
  rw [hexp, Module.Basis.repr_sum_self]

end
end S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension (solution)
