-- Prove2me | Definitions.Def_FreeGroupFactorProof27
-- name    : FreeGroupFactorProof27
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:40:37.419946+00:00
-- url     : https://prove2.me/theorems/b77c223f-b84c-4f47-b1ca-aa11409ddaf4
-- title:
--   Free group factors: supporting development, part 27
-- statement:
--   Part 27 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof26

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem signedTrajectory_coordinate_ode [DecidableEq ι]
    (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue C l))
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (PolynomialFlow.field (laurentValue C l) h (X t) i) t)
    (t : ℝ) (ib : Option ι × Bool) :
    HasDerivAt (fun s => signedTrajectory X hU C s ib)
      (NCPolynomial.eval (signedTrajectory X hU C t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t := by
  have hpos (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,true)) =
      coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
        (TraceCocycle.fieldCoefficients h l j) *
        (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) :=
    eval_encodedField_pos _ _ _
  have hneg (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,false)) =
      -(star (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) *
        coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
          (TraceCocycle.fieldCoefficients h l j)) :=
    eval_encodedField_neg _ _ _
  rcases ib with ⟨i,b⟩
  cases i with
  | none =>
    cases b
    · rw [hneg]
      simp only [TraceCocycle.fieldCoefficients, map_zero, mul_zero, neg_zero]
      simpa only [signedTrajectory_none_neg] using hasDerivAt_const t (star (C : A))
    · rw [hpos]
      simp only [TraceCocycle.fieldCoefficients, map_zero, zero_mul]
      simpa only [signedTrajectory_none_pos] using hasDerivAt_const t (C : A)
  | some i =>
    have hi := hX t i
    cases b
    · rw [hneg, coefficientHom_fieldCoefficients]
      have hs := hi.star
      have he : star (PolynomialFlow.field (laurentValue C l) h (X t) i) =
          -(star (X t i) * (Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (X t))) := by
        simp only [PolynomialFlow.field, star_smul, star_mul, Complex.star_def,
          Complex.conj_I, (PolynomialFlow.selfAdjoint_hamiltonian _ hS _ _).star_eq,
          neg_smul, mul_smul_comm]
      rw [he] at hs
      simpa only [signedTrajectory_some_neg, extendUnitary, Option.elim_some] using hs
    · rw [hpos, coefficientHom_fieldCoefficients]
      simpa only [signedTrajectory_some_pos, extendUnitary, Option.elim_some,
        PolynomialFlow.field, smul_mul_assoc] using hi

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

theorem encodedField_finite_range {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0) :
    (Set.range (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l))).Finite := by
  classical
  let S : Finset (Option ι × Bool) := (insert none (s.image some)).product Finset.univ
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  have hz (ib : Option ι × Bool) (hib : ib ∉ S) :
      V ib = AlgebraPolynomial.encode (0 : MonoidAlgebra ℂ (FreeGroup (Option ι))) := by
    have hi : ∃ i, ib.1 = some i ∧ i ∉ s := by
      rcases ib with ⟨i,b⟩
      cases i with
      | none => simp [S] at hib
      | some i => exact ⟨i,rfl,by simpa [S] using hib⟩
    obtain ⟨i,hi,his⟩ := hi
    have hf : TraceCocycle.fieldCoefficients h l (some i) = 0 := by
      simp [TraceCocycle.fieldCoefficients,hs i his]
    change AlgebraPolynomial.encode (TraceCocycle.algebraDerivative _
      (MonoidAlgebra.of ℂ _ (AlgebraPolynomial.signed ib))) = _
    congr 1
    ext b
    cases hb : ib.2 <;>
      simp [AlgebraPolynomial.signed,hi,hb,TraceCocycle.cocycle_inv,hf]
  apply (Set.Finite.insert (AlgebraPolynomial.encode (0 : MonoidAlgebra ℂ (FreeGroup (Option ι))))
    (S.finite_toSet.image V)).subset
  rintro q ⟨ib,rfl⟩
  by_cases hb : ib ∈ S
  · exact Set.mem_insert_of_mem _ ⟨ib,hb,rfl⟩
  · exact Set.mem_insert_iff.mpr (Or.inl (hz ib hb))

theorem source_laurent_moments_finite {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  let S := (encodedField_finite_range h l s hs).toFinset
  have hmem (ib) : V ib ∈ S := by simp [S,V]
  let J := S.sup NCPolynomial.degree
  let B := ∑ q ∈ S, NCPolynomial.mass q
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => NCPolynomial.mass_nonneg _
  apply source_laurent_moments_bounded h l Y hY₀ hsmooth hbounded hODE J B hB
  · intro ib
    exact (Finset.le_sup (f := NCPolynomial.degree) (hmem ib)).trans (Nat.le_succ _)
  · intro ib
    exact Finset.single_le_sum (fun q _ => NCPolynomial.mass_nonneg q) (hmem ib)

 theorem laurent_flow_coordinate_moments {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (s : Finset ι) (hs : ∀ i, i ∉ s → h i = 0)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (PolynomialFlow.field
      (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t) i) t)
    (hsmoothX : ∀ i, ContDiff ℝ ∞ (fun t => X t i)) :
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
  have hsmooth (ib) : ContDiff ℝ ∞ (fun t => Y t ib) := by
    rcases ib with ⟨i,b⟩
    cases i with
    | none => cases b <;>
        simp only [Y,signedTrajectory_none_pos,signedTrajectory_none_neg] <;>
        exact contDiff_const
    | some i => cases b
                · simp only [Y,signedTrajectory_some_neg]
                  exact (starL ℝ (A := groupVonNeumann (FreeGroup (Option ι)))).contDiff.comp (hsmoothX i)
                · simpa only [Y,signedTrajectory_some_pos] using hsmoothX i
  have hbounded (t ib) : ‖Y t ib‖ ≤ 1 :=
    UnitaryEvaluation.norm_signedTrajectory_le_one X hU C t ib
  intro t g
  let p := AlgebraPolynomial.encode (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)
  have hmoment := source_laurent_moments_finite h l s hs Y hY₀ hsmooth hbounded
    (UnitaryEvaluation.signedTrajectory_coordinate_ode C h l hS X hU hX) p t
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

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

theorem hamiltonian_map [DecidableEq ι] [DecidableEq κ]
    (S : A) (h : FreeGroup ι →₀ ℝ) (f : ι → κ) (U : κ → unitary A) :
    PolynomialFlow.hamiltonian S (Finsupp.mapDomain (FreeGroup.map f) h) (fun j => (U j : A)) =
      PolynomialFlow.hamiltonian S h (fun i => (U (f i) : A)) := by
  classical
  simp only [PolynomialFlow.hamiltonian]
  rw [Finsupp.sum_mapDomain_index (fun g => by simp) (fun g a b => by simp [add_smul])]
  apply Finsupp.sum_congr
  intro g hg
  rw [← wordHom_word,wordHom_map,wordHom_word]
  rfl

theorem solution_coordinate_deriv [Fintype ι] [DecidableEq ι]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field S h (X t)) t) (t : ℝ) (i : ι) :
    HasDerivAt (fun s => X s i) (PolynomialFlow.field S h (X t) i) t :=
  hasDerivAt_pi.mp (hX t) i

theorem solution_coordinate_smooth [Fintype ι] [DecidableEq ι]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field S h (X t)) t) (i : ι) :
    ContDiff ℝ ∞ (fun t => X t i) :=
  (contDiff_apply ℝ A i).comp (PolynomialFlow.smooth_solution S h X hX)

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

def coefficients (h : ι → FreeGroup ι →₀ ℝ) : (ι ⊕ κ) → FreeGroup (ι ⊕ κ) →₀ ℝ :=
  Sum.elim (fun i => Finsupp.mapDomain (FreeGroup.map Sum.inl) (h i)) (fun _ => 0)

theorem field_inl [DecidableEq ι] [DecidableEq κ]
    (S : Ambient ι κ) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ι → Ambient ι κ) (hX : ∀ i, X i ∈ unitary (Ambient ι κ)) (i : ι) :
    PolynomialFlow.field S (coefficients h) (tuple X) (Sum.inl i) =
      PolynomialFlow.field S h X i := by
  let U : (ι ⊕ κ) → unitary (Ambient ι κ) := fun j => ⟨tuple X j,tuple_unitary X hX j⟩
  change Complex.I • (PolynomialFlow.hamiltonian S
    (Finsupp.mapDomain (FreeGroup.map Sum.inl) (h i)) (fun j => (U j : Ambient ι κ)) * X i) = _
  rw [hamiltonian_map]
  rfl

@[simp] theorem field_inr [DecidableEq ι] [DecidableEq κ]
    (S : Ambient ι κ) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ι → Ambient ι κ) (k : κ) :
    PolynomialFlow.field S (coefficients h) (tuple X) (Sum.inr k) = 0 := by
  change Complex.I • ((0 : Ambient ι κ) * tuple X (Sum.inr k)) = 0
  rw [zero_mul]
  apply Subtype.ext
  exact smul_zero Complex.I

theorem moments [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue
      (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t (g : FreeGroup (Option (ι ⊕ κ))), canonicalTrace (wordHom
      (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
        (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let s : Finset (ι ⊕ κ) := Finset.univ.image Sum.inl
  have hs (j) (hj : j ∉ s) : coefficients (κ := κ) h j = 0 := by
    cases j with
    | inl i => simp [s] at hj
    | inr k => rfl
  apply laurent_flow_coordinate_moments (coefficients h) l s hs hS
    (fun t => tuple (X t)) (fun t => tuple_unitary (X t) (hU t))
  · funext j
    cases j with
    | inl i => exact congrFun hX₀ i
    | inr k => rfl
  · intro t j
    cases j with
    | inl i =>
      rw [field_inl _ h (X t) (hU t)]
      exact solution_coordinate_deriv _ h X hX t i
    | inr k =>
      rw [field_inr]
      exact hasDerivAt_const t _
  · intro j
    cases j with
    | inl i =>
      change ContDiff ℝ _ (fun t => X t i)
      exact solution_coordinate_smooth _ h X hX i
    | inr k => exact contDiff_const

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain
open UnitaryEvaluation
open scoped ENNReal
 theorem canonical_total_of_reducing {ι : Type uι}
    (K : Submodule ℂ (GroupHilbert (FreeGroup ι)))
    (hK : IsClosed (K : Set (GroupHilbert (FreeGroup ι)))) (hδ : deltaOne ∈ K)
    (hgen : ∀ i : ι, (generatorUnitary i : groupVonNeumann (FreeGroup ι)) ∈
      (reducingAlgebra K).comap (groupVonNeumann (FreeGroup ι)).subtype) : ⊤ ≤ K := by
  classical
  let E := (reducingAlgebra K).comap (groupVonNeumann (FreeGroup ι)).subtype
  have hgroup (g : FreeGroup ι) : groupUnitary g ∈ E := by
    rw [← wordHom_generatorUnitary]
    exact wordHom_mem E generatorUnitary hgen g
  have hsingle (g : FreeGroup ι) : lp.single 2 g (1 : ℂ) ∈ K := by
    have hh := (hgroup g).1 deltaOne hδ
    have he : (leftRegular g) deltaOne = lp.single 2 g 1 := by
      ext x
      simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
    change (leftRegular g) deltaOne ∈ K at hh
    rwa [he] at hh
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert (FreeGroup ι)) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

end FreeGroupFactorMain

end

end OAI
end


