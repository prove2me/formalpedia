-- Prove2me | Definitions.Def_OAIErdos3B163
-- name    : OAIErdos3B163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:14:01.363894+00:00
-- url     : https://prove2.me/theorems/e73fdb8c-4e56-4118-8a9d-4a918c5ebafb
-- title:
--   OpenAI Erdős-3 split, definitions bundle 164 of 177
-- statement:
--   Definitions bundle 164 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B162`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 164 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.coefficientDeckChartEvent_measurableSet`, `OAI.Erdos3.VectorPolynomial.coefficientSamplerAmbientPoint_measurable`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B161

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in

theorem coefficientSamplerAmbientPoint_measurable (a : CoefficientAmbientIndex K J) :
    Measurable (fun x : CoefficientSamplerArrays (K := K) I n =>
      coefficientSamplerAmbientPoint U b o x a) := by
  exact (PiLp.continuous_apply 2 (fun _ : J a.1.1 => ℝ) a.2).measurable.comp
    ((normalizedLatticePoint_continuous (euclideanSubspace (U a.1.1)) (b a.1.1)).measurable.comp
      ((orthonormalMixedChart (o a.1.1)).measurable.comp
        ((measurable_pi_apply a.1.2).comp
          ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply a.1.1)))))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientDeckChartEvent_measurableSet (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) :
    MeasurableSet {y | coefficientDeckChartEvent U bW b hb o q event y} := by
  let T := CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q
  let chart : Set T := {z | (∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2) ∧
    event (coefficientSamplerChartResidues q z.1 z.2)}
  have hsmall : MeasurableSet {z : T | ∀ a,
      |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_lt ((coefficientSamplerAmbientPoint_measurable U b o a).comp measurable_fst).abs
      measurable_const
  have hread : Measurable (fun z : T => coefficientSamplerChartResidues q z.1 z.2) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro e
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | inl i =>
      exact (measurable_of_countable (fun v : ℤ => (v : ZMod q))).comp
        ((measurable_pi_apply e).comp ((measurable_pi_apply i).comp
          (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst))))
    | inr i =>
      exact (measurable_pi_apply i).comp ((measurable_pi_apply e).comp
        ((measurable_pi_apply j).comp measurable_snd))
  have hchart : MeasurableSet chart := hsmall.inter
    (hread (Set.toFinite {r | event r}).measurableSet)
  have instS : StandardBorelSpace (CoefficientSamplerArrays (K := K) I n) := by infer_instance
  have instR : StandardBorelSpace (CoefficientDeckResidues (K := K) E q) := by infer_instance
  let : StandardBorelSpace T := @StandardBorelSpace.prod _ _ _ _ instS instR
  have himage := hchart.image_of_measurable_injOn
    (canonicalCoefficientDeckSample_measurable U bW b hb o q)
    ((canonicalCoefficientDeckSample_injOn_smallAmbient U bW b hb o q (NeZero.pos q)).mono
      (fun _ hz => hz.1))
  convert himage using 1
  ext y
  constructor
  · rintro ⟨x, r, hs, hy, he⟩
    exact ⟨(x,r), ⟨hs,he⟩, hy⟩
  · rintro ⟨⟨x,r⟩, ⟨hs,he⟩, hy⟩
    exact ⟨x,r,hs,hy,he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped Classical

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]

end Erdos3.VectorPolynomial

end

end OAI

end


