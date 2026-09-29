-- Prove2me | solution 1 for AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/68987790-2555-5ea4-98fe-a8a709f924d2

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace EvalMatrix

variable {𝕜 : Type*} [Field 𝕜] {X : Type*}

private def evalMatrix {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => v j (x i)

omit [Field 𝕜] in
private theorem evalMatrix_apply {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X) (i j : Fin n) :
    evalMatrix v x i j = v j (x i) := rfl

private theorem exists_det_evalMatrix_ne_zero :
    ∀ {n : ℕ} (v : Fin n → X → 𝕜), LinearIndependent 𝕜 v →
      ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0
  | 0, _, _ => ⟨Fin.elim0, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  | n + 1, v, hv => by
    obtain ⟨x', hx'⟩ :=
      exists_det_evalMatrix_ne_zero (fun j => v j.succ) (hv.comp Fin.succ (Fin.succ_injective n))

    let e : Fin (n + 1) → 𝕜 := fun j =>
      (-1) ^ (j : ℕ) * (Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i)).det
    have hminor : ∀ (y : X) (j : Fin (n + 1)),
        (evalMatrix v (Fin.cons y x')).submatrix Fin.succ j.succAbove
          = Matrix.of fun (i : Fin n) (j' : Fin n) => v (j.succAbove j') (x' i) := by
      intro y j
      ext i j'
      simp [evalMatrix, Matrix.submatrix, Fin.cons_succ]
    have hexp : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = ∑ j, e j * v j y := by
      intro y
      rw [Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hminor y j]
      simp only [e, evalMatrix_apply, Fin.cons_zero]
      ring
    have he0 : e 0 ≠ 0 := by
      have h0 : (Matrix.of fun (i : Fin n) (j' : Fin n) => v ((0 : Fin (n + 1)).succAbove j') (x' i))
          = evalMatrix (fun j => v j.succ) x' := by
        ext i j'
        simp [evalMatrix]
      simp only [e, Fin.val_zero, pow_zero, one_mul, h0]
      exact hx'
    by_cases hy : ∃ y : X, (evalMatrix v (Fin.cons y x')).det ≠ 0
    · obtain ⟨y, hy⟩ := hy
      exact ⟨Fin.cons y x', hy⟩
    · exfalso
      have hzero : ∀ y : X, (evalMatrix v (Fin.cons y x')).det = 0 :=
        fun y => by_contra fun h => hy ⟨y, h⟩
      have hsum : ∑ j, e j • v j = 0 := by
        funext y
        have := hexp y
        rw [hzero y] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact this.symm
      exact he0 (Fintype.linearIndependent_iff.mp hv e hsum 0)

private theorem linearIndependent_of_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜)
    (x : Fin n → X) (h : (evalMatrix v x).det ≠ 0) : LinearIndependent 𝕜 v := by
  have hrows : LinearIndependent 𝕜 (fun j => (evalMatrix v x).transpose j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (by rwa [Matrix.det_transpose])
  let f : (X → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) := LinearMap.pi fun i => LinearMap.proj (x i)
  have hcomp : (⇑f ∘ v) = fun j => (evalMatrix v x).transpose j := by
    funext j i
    rfl
  exact LinearIndependent.of_comp f (by rw [hcomp]; exact hrows)

private theorem linearIndependent_iff_exists_det_evalMatrix_ne_zero {n : ℕ} (v : Fin n → X → 𝕜) :
    LinearIndependent 𝕜 v ↔ ∃ x : Fin n → X, (evalMatrix v x).det ≠ 0 :=
  ⟨exists_det_evalMatrix_ne_zero v, fun ⟨x, hx⟩ => linearIndependent_of_det_evalMatrix_ne_zero v x hx⟩

private theorem eq_sum_inv_evalMatrix_mulVec_smul {n : ℕ} (v : Fin n → X → 𝕜) (x : Fin n → X)
    (hx : (evalMatrix v x).det ≠ 0) (g : X → 𝕜) (hg : g ∈ Submodule.span 𝕜 (Set.range v)) :
    g = ∑ j, ((evalMatrix v x)⁻¹.mulVec (fun i => g (x i))) j • v j := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := 𝕜)).mp hg
  have hvals : (fun i => (∑ j, c j • v j) (x i)) = (evalMatrix v x).mulVec c := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      evalMatrix_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hinv : (evalMatrix v x)⁻¹.mulVec ((evalMatrix v x).mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  rw [hvals, hinv]

end EvalMatrix

namespace FlatFamilyDecomposition

variable (F : Type) [Field F] [NumberField F]

private abbrev InK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

private abbrev KT : Type := {k : AdelicGL2 (𝓞 F) F // InK F k}

private def restr (f : AdelicGL2 (𝓞 F) F → ℂ) : KT F → ℂ := fun k => f k.1

variable {F}

private theorem exists_linearIndependent_subfamily {X : Type} {n : ℕ} (v : Fin n → (X → ℂ)) :
    ∃ (m : ℕ) (ι : Fin m → Fin n), LinearIndependent ℂ (v ∘ ι) ∧
      Submodule.span ℂ (Set.range (v ∘ ι)) = Submodule.span ℂ (Set.range v) := by
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℂ (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbsub
  haveI : Fintype b := hbfin.fintype
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  have hmem : ∀ i : Fin (Fintype.card b), ((e i : b) : X → ℂ) ∈ Set.range v := fun i => hbsub (e i).2
  choose ι hι using hmem
  have hcomp : v ∘ ι = fun i => ((e i : b) : X → ℂ) := funext hι
  have hrange : Set.range (fun i => ((e i : b) : X → ℂ)) = b := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hf
      exact ⟨e.symm ⟨f, hf⟩, by simp⟩
  refine ⟨_, ι, ?_, ?_⟩
  · rw [hcomp]
    exact hbind.comp e e.injective
  · rw [hcomp, hrange, hbspan]

private theorem eq_of_eqOn_of_isOpen {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) (h : Set.EqOn f g U) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  obtain ⟨z₀, hz₀⟩ := hne
  funext z
  exact hf'.eqOn_of_preconnected_of_eventuallyEq hg' isPreconnected_univ (Set.mem_univ z₀)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hz₀) h) (Set.mem_univ z)

variable (F)

private theorem eq_of_isInducedSection_of_forall_inK (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {f g : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (hg : IsInducedSection (𝓞 F) F χ₁ χ₂ g) (h : ∀ k, InK F k → f k = g k) : f = g := by
  funext x
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F x
  rw [hf b hb k, hg b hb k, h k ⟨hk1, hk2⟩]

private theorem isInducedSection_sum (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {m : ℕ} (c : Fin m → ℂ)
    (ψ : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (hψ : ∀ i, IsInducedSection (𝓞 F) F χ₁ χ₂ (ψ i)) :
    IsInducedSection (𝓞 F) F χ₁ χ₂ (fun g => ∑ i, c i * ψ i g) := by
  have hfun : (fun g => ∑ i, c i * ψ i g) = ∑ i, c i • ψ i := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : (∑ i, c i • ψ i) ∈ inducedSectionSubmodule χ₁ χ₂ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hψ i)
  rw [hfun]
  exact hmem

end FlatFamilyDecomposition

open FlatFamilyDecomposition in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (n : ℕ) (c : Fin n → ℂ → ℂ) (ψ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ i, Differentiable ℂ (c i))
      ∧ (∀ i s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ i s))
      ∧ (∀ i s, IsArchKFinite F (ψ i s))
      ∧ (∀ i s, IsKfSmooth F (ψ i s))
      ∧ (∀ i, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ i p.1 p.2))
      ∧ (∀ i g, Differentiable ℂ (fun s => ψ i s g))
      ∧ (∀ (i : Fin n) (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ i s k = ψ i s' k)
      ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = ∑ i, c i s * ψ i s g := by
  intro α hα μ ν φ hφ hφK hφf hφjc hφhol

  obtain ⟨U, hU, hne, n, σ, hspan⟩ := AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous F φ hφK hφf hφjc

  have hA1 : ∀ i : Fin n, ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ (σ i) = φ (σ i)
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ (∀ s, IsArchKFinite F (ψ s))
      ∧ (∀ s, IsKfSmooth F (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k :=
    fun i => AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν (σ i) (φ (σ i)) (hφ (σ i)) (hφK (σ i)) (hφf (σ i))
      (hφjc.comp (continuous_const.prodMk continuous_id))
  choose ψ hψ using hA1

  have hmem : ∀ s ∈ U,
      restr F (φ s) ∈ Submodule.span ℂ (Set.range fun i => restr F (φ (σ i))) := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan s hs
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).2 ⟨c, ?_⟩
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, restr]
    exact (hc k.1 k.2.1 k.2.2).symm

  obtain ⟨m, ι, hind, hspan'⟩ := exists_linearIndependent_subfamily (fun i => restr F (φ (σ i)))
  obtain ⟨x, hx⟩ := EvalMatrix.exists_det_evalMatrix_ne_zero _ hind
  let Mi : Matrix (Fin m) (Fin m) ℂ := (EvalMatrix.evalMatrix ((fun i => restr F (φ (σ i))) ∘ ι) x)⁻¹
  let cf : ℂ → Fin m → ℂ := fun s => Mi.mulVec (fun l => φ s (x l).1)
  have hcf_hol : ∀ j, Differentiable ℂ (fun s => cf s j) := by
    intro j
    show Differentiable ℂ (fun s => ∑ l, Mi j l * φ s (x l).1)
    exact Differentiable.fun_sum fun l _ => (hφhol (x l).1).const_mul (Mi j l)
  have hcf_U : ∀ s ∈ U, restr F (φ s) = ∑ j, cf s j • restr F (φ (σ (ι j))) := by
    intro s hs
    have hs' : restr F (φ s) ∈ Submodule.span ℂ (Set.range ((fun i => restr F (φ (σ i))) ∘ ι)) := by
      rw [hspan']
      exact hmem s hs
    exact EvalMatrix.eq_sum_inv_evalMatrix_mulVec_smul _ x hx _ hs'

  have hall : ∀ (s : ℂ) (k : KT F), φ s k.1 = ∑ j, cf s j * φ (σ (ι j)) k.1 := by
    intro s k
    have hfun := eq_of_eqOn_of_isOpen (f := fun s => φ s k.1)
      (g := fun s => ∑ j, cf s j * φ (σ (ι j)) k.1) (hφhol k.1)
      (Differentiable.fun_sum fun j _ => (hcf_hol j).mul_const (φ (σ (ι j)) k.1)) hU hne (fun s hs => by
        have h := congrFun (hcf_U s hs) k
        simpa only [restr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h)
    exact congrFun hfun s
  refine ⟨m, fun j s => cf s j, fun j => ψ (ι j), hcf_hol, fun j s => (hψ (ι j)).2.1 s,
    fun j s => (hψ (ι j)).2.2.1 s, fun j s => (hψ (ι j)).2.2.2.1 s, fun j => (hψ (ι j)).2.2.2.2.1,
    fun j g => (hψ (ι j)).2.2.2.2.2.1 g, fun j s s' k h1 h2 => (hψ (ι j)).2.2.2.2.2.2 s s' k h1 h2, ?_⟩
  intro s g
  have hsec := eq_of_isInducedSection_of_forall_inK F (etaFst μ α hα s) (etaSnd ν α hα s) (hφ s)
    (isInducedSection_sum F _ _ (fun j => cf s j) (fun j => ψ (ι j) s) (fun j => (hψ (ι j)).2.1 s))
    (fun k hk => by
      have hk' : ∀ j, ψ (ι j) s k = φ (σ (ι j)) k := fun j =>
        ((hψ (ι j)).2.2.2.2.2.2 s (σ (ι j)) k hk.1 hk.2).trans (congrFun (hψ (ι j)).1 k)
      simp only [hk']
      exact hall s ⟨k, hk⟩)
  exact congrFun hsec g

#print axioms solution

end S_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
end P2MW
export P2MW.S_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family (solution)
