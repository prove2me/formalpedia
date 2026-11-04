-- Prove2me | Definitions.Def_FreeGroupFactorProof21
-- name    : FreeGroupFactorProof21
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:18:15.709286+00:00
-- url     : https://prove2.me/theorems/e40529db-cedc-4037-b592-1171ac0eb1cc
-- title:
--   Free group factors: supporting development, part 21
-- statement:
--   Part 21 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof20

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem laurent_flow_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) :
    ∀ t (g : FreeGroup (Option ι)),
      canonicalTrace (UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
          (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let C : unitary (groupVonNeumann (FreeGroup (Option ι))) := generatorUnitary none
  let S := UnitaryEvaluation.laurentValue C l
  let Y := UnitaryEvaluation.signedTrajectory X hU C
  have hu0 : UnitaryEvaluation.extendUnitary (fun j => ⟨X 0 j, hU 0 j⟩) C =
      generatorUnitary := by
    funext i
    cases i with
    | none => rfl
    | some j => apply Subtype.ext; exact congrFun hX₀ j
  have hY₀ (ib) : Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib) := by
    dsimp [Y, UnitaryEvaluation.signedTrajectory]
    rw [hu0, wordHom_generatorUnitary]
  have hsmooth (ib) : ContDiff ℝ ∞ (fun t => Y t ib) :=
    UnitaryEvaluation.smooth_signedTrajectory X hU C
      (PolynomialFlow.smooth_solution S h X hX) ib
  have hbounded (t ib) : ‖Y t ib‖ ≤ 1 :=
    UnitaryEvaluation.norm_signedTrajectory_le_one X hU C t ib
  intro t g
  let p := AlgebraPolynomial.encode (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)
  have hmoment := source_laurent_moments h l Y hY₀ hsmooth hbounded
    (UnitaryEvaluation.signedTrajectory_ode C h l hS X hU hX) p t
  have he (s) : NCPolynomial.eval (Y s) p =
      UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C) g := by
    change NCPolynomial.eval (fun ib => UnitaryEvaluation.wordHom
      (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C)
        (AlgebraPolynomial.signed ib)) (AlgebraPolynomial.encode
          (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)) = _
    rw [UnitaryEvaluation.eval_encode, UnitaryEvaluation.algebraHom_of]
  rw [he, he, hu0, wordHom_generatorUnitary, canonicalTrace_groupUnitary] at hmoment
  exact hmoment

 theorem actual_laurent_flow_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l)) :
    ∃ (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
      (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι)))),
      X 0 = (fun j => groupUnitary (FreeGroup.of (some j))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) ∧
      ∀ t (g : FreeGroup (Option ι)),
        canonicalTrace (UnitaryEvaluation.wordHom
          (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
            (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let C : unitary (groupVonNeumann (FreeGroup (Option ι))) := generatorUnitary none
  let S := UnitaryEvaluation.laurentValue C l
  obtain ⟨X, hX₀, hX, hU⟩ := PolynomialFlow.global_unitary_solution S hS h
    (fun j => groupUnitary (FreeGroup.of (some j))) (fun j => groupUnitary_mem_unitary _)
  refine ⟨X,hU,hX₀,hX,?_⟩
  exact laurent_flow_moments h l hS X hU hX₀ hX

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Nontrivial A] [Fintype ι] [DecidableEq ι] in
theorem coe_wordList (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (w : List (ι × Bool)) (X : ι → E) :
    ((wordList w X : E) : A) = wordList w (fun i => (X i : A)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b <;> simpa [wordList] using
      congrArg (fun z : A => _ * z) ih

omit [Nontrivial A] [Fintype ι] in
theorem coe_field (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (S : E)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → E) (j : ι) :
    ((field S h X j : E) : A) = field (S : A) h (fun i => (X i : A)) j := by
  classical
  simp [field, hamiltonian, Finsupp.sum, word, coe_wordList]

theorem solution_mem_subalgebra (E : StarSubalgebra ℂ A) (hE : IsClosed (E : Set A))
    (S : A) (hS : IsSelfAdjoint S) (hSE : S ∈ E) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hU : ∀ t j, X t j ∈ unitary A) (t₀ : ℝ) (h₀ : ∀ j, X t₀ j ∈ E) :
    ∀ t j, X t j ∈ E := by
  let : IsClosed (E : Set A) := hE
  let S' : E := ⟨S, hSE⟩
  let V : ι → E := fun j => ⟨X t₀ j, h₀ j⟩
  have hS' : IsSelfAdjoint S' := Subtype.ext hS
  have hV : ∀ j, V j ∈ unitary E := by
    intro j
    rw [Unitary.mem_iff]
    exact ⟨Subtype.ext (hU t₀ j).1, Subtype.ext (hU t₀ j).2⟩
  obtain ⟨Y, hY₀, hY, hUY⟩ := global_unitary_solution S' hS' h V hV
  let L : (ι → E) →L[ℝ] (ι → A) :=
    ContinuousLinearMap.pi fun j =>
      (E.toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ).comp
        (ContinuousLinearMap.proj j)
  let Z : ℝ → ι → A := fun t => L (Y (t - t₀))
  have hZ : ∀ t, HasDerivAt Z (field S h (Z t)) t := by
    intro t
    have hd := (hY (t - t₀)).scomp t ((hasDerivAt_id t).sub_const t₀)
    have hm := L.hasFDerivAt.comp_hasDerivAt t hd
    have hm' : HasDerivAt Z (L (field S' h (Y (t - t₀)))) t := by
      simpa only [Function.comp_def, id_eq, one_smul, Z] using hm
    have hf : L (field S' h (Y (t - t₀))) = field S h (Z t) := by
      ext j
      exact coe_field E S' h (Y (t - t₀)) j
    rw [hf] at hm'
    exact hm'
  have hUZ : ∀ t j, Z t j ∈ unitary A := by
    intro t j
    exact ⟨congrArg Subtype.val (hUY (t - t₀) j).1,
      congrArg Subtype.val (hUY (t - t₀) j).2⟩
  have heq : X = Z := unitary_solutions_unique S h X Z hX hZ hU hUZ t₀ (by
    ext j
    change X t₀ j = ((Y (t₀ - t₀) j : E) : A)
    rw [sub_self, hY₀])
  intro t j
  rw [heq]
  exact (Y (t - t₀) j).property

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

theorem groupVN_matrix {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x y : G) :
    ((T : GroupOperator G) (lp.single 2 y 1)) x =
      ((T : GroupOperator G) deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne)
    (groupVN_commute_right T y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

theorem groupVN_star_coefficient {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x : G) :
    ((star T : GroupOperator G) deltaOne) x =
      conj (((T : GroupOperator G) deltaOne) x⁻¹) := by
  calc
    ((star T : GroupOperator G) deltaOne) x =
        inner ℂ (lp.single 2 x (1 : ℂ)) ((star T : GroupOperator G) deltaOne) := by
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    _ = inner ℂ ((T : GroupOperator G) (lp.single 2 x 1)) deltaOne := by
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj (((T : GroupOperator G) (lp.single 2 x 1)) 1) := by
      simp only [deltaOne, lp.inner_single_right, RCLike.inner_apply, one_mul]
    _ = _ := by rw [groupVN_matrix]; simp

theorem canonicalTrace_star_mul_inner {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) :
    canonicalTrace (star T * U) = inner ℂ
      ((T : GroupOperator G) deltaOne) ((U : GroupOperator G) deltaOne) := by
  classical
  rw [canonicalTrace_eq_inner, ← deltaOne_eq]
  change inner ℂ deltaOne (star (T : GroupOperator G) ((U : GroupOperator G) deltaOne)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem canonicalTrace_mul {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) : canonicalTrace (T * U) = canonicalTrace (U * T) := by
  have he (T U : groupVonNeumann G) :
      canonicalTrace (T * U) = ∑' x : G,
        ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x := by
    rw [← star_star T, canonicalTrace_star_mul_inner]
    change (∑' x, inner ℂ (((star T : GroupOperator G) deltaOne) x)
      (((U : GroupOperator G) deltaOne) x)) = _
    apply tsum_congr
    intro x
    rw [groupVN_star_coefficient]
    simp [RCLike.inner_apply, mul_comm]
  rw [he, he]
  simpa only [Equiv.inv_apply, inv_inv, mul_comm] using
    ((Equiv.inv G).tsum_eq (fun x =>
      ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x)).symm

def hilbertSequenceMap {G : Type uG} {H : Type uH} (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : lp (fun _ : ℕ => GroupHilbert G) 2) :
    lp (fun _ : ℕ => GroupHilbert H) 2 :=
  ⟨fun n => e (ξ n), Memℓp.of_norm (by simpa only [e.norm_map] using (lp.memℓp ξ).norm)⟩

theorem spatial_ultraweak_continuous {G : Type uG} {H : Type uH}
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology H)
      e.conjStarAlgEquiv := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have heq :
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (e.conjStarAlgEquiv T (ξ k))) =
      (fun T : GroupOperator G => ∑' k : ℕ,
        inner ℂ (hilbertSequenceMap e.symm η k) (T (hilbertSequenceMap e.symm ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    change inner ℂ (η k) (e (T (e.symm (ξ k)))) =
      inner ℂ (e.symm (η k)) (T (e.symm (ξ k)))
    rw [← e.inner_map_map]
    simp
  change @Continuous _ _ (ultraweakOperatorTopology G) _
    (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (e.conjStarAlgEquiv T (ξ k)))
  rw [heq]
  exact continuous_iInf_dom (i := hilbertSequenceMap e.symm ξ)
    (continuous_iInf_dom (i := hilbertSequenceMap e.symm η) continuous_induced_dom)

def spatialGroupIso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H where
  toFun T := ⟨e.conjStarAlgEquiv T, (hVN T).mp T.property⟩
  invFun T := ⟨e.conjStarAlgEquiv.symm T, (hVN _).mpr (by rw [e.conjStarAlgEquiv.apply_symm_apply]; exact T.property)⟩
  left_inv T := Subtype.ext (e.conjStarAlgEquiv.symm_apply_apply T)
  right_inv T := Subtype.ext (e.conjStarAlgEquiv.apply_symm_apply T)
  map_mul' T U := Subtype.ext (map_mul e.conjStarAlgEquiv (T : GroupOperator G) (U : GroupOperator G))
  map_add' T U := Subtype.ext (map_add e.conjStarAlgEquiv (T : GroupOperator G) (U : GroupOperator G))
  map_star' T := Subtype.ext (map_star e.conjStarAlgEquiv (T : GroupOperator G))
  map_smul' c T := Subtype.ext (map_smul e.conjStarAlgEquiv c (T : GroupOperator G))

theorem spatialGroupIso_normal {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology H)
      (spatialGroupIso e hVN) := by
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (GroupOperator H) := ultraweakOperatorTopology H
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
  apply continuous_induced_rng.mpr
  have hinc : Continuous (fun T : groupVonNeumann G => (T : GroupOperator G)) :=
    continuous_induced_dom
  exact (spatial_ultraweak_continuous e).comp hinc

open scoped ComplexConjugate ENNReal

 theorem operator_matrix_ext {G : Type uG} [DecidableEq G] (T U : GroupOperator G)
    (h : ∀ g, T (lp.single 2 g 1) = U (lp.single 2 g 1)) : T = U := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have hT := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL T
  have hU := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL U
  have he (g : G) : T (lp.single 2 g (ξ g)) = U (lp.single 2 g (ξ g)) := by
    have hc : lp.single (E := fun _ : G => ℂ) 2 g (ξ g) =
        (ξ g) • lp.single (E := fun _ : G => ℂ) 2 g 1 := by
      ext b
      simp [lp.single_apply, Pi.single_apply]
    rw [hc, map_smul, map_smul, h]
  simp only [he] at hT
  exact hT.unique hU

 theorem operator_coeff_tsum {G : Type uG} [DecidableEq G] (T : GroupOperator G)
    (ξ : GroupHilbert G) (x : G) :
    (T ξ) x = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
  calc
    (T ξ) x = inner ℂ (lp.single 2 x 1) (T ξ) := by simp [lp.inner_single_left]
    _ = inner ℂ (star T (lp.single 2 x 1)) ξ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro y
      have he : conj ((star T (lp.single 2 x 1)) y) = (T (lp.single 2 y 1)) x := by
        calc
          _ = inner ℂ (star T (lp.single 2 x 1)) (lp.single 2 y 1) := by
            simp [lp.inner_single_right]
          _ = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
            rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
          _ = _ := by simp [lp.inner_single_left]
      simp only [RCLike.inner_apply, he, mul_comm]

 theorem matrix_of_commute_right {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, rightRegular g * T = T * rightRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end


