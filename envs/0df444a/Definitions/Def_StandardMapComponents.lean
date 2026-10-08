-- Prove2me | Definitions.Def_StandardMapComponents
-- name    : StandardMapComponents
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.960201+00:00
-- url     : https://prove2.me/theorems/a4b293ee-2c23-46db-8554-9c7f3a20ab9b
-- statement:
--   This block works on the torus T² = (ℝ/ℤ)² with the product of Lebesgue measures as area. The functions sine and cosine on the circle are the 1-periodic descents of sin(2πx) and cos(2πx). For a real parameter k, standardMap(k) sends (x,y) to (x+y+k·sine(x), y+k·sine(x)). The torusPotential is 2+2πk·cosine(x). transferStep(v) is the real-linear map on ℂ = ℝ² sending z to (v·Re z − Im z) + i·Re z, wedge(z,w) = Re z·Im w − Im z·Re w, and tangentCoordinates sends z to Re z + i(Re z − Im z). The standardDerivative at a point z is tangentCoordinates composed with transferStep(torusPotential(k, x-coordinate of z)) composed with tangentCoordinates, and standardDerivativeProduct is the composition of these maps along the first n iterates of standardMap(k) starting at z. VectorGrowth(k,z,v,l) says v is nonzero and (1/n)·log‖standardDerivativeProduct(k,z,n)v‖ tends to l. LyapunovSpectrumAt(k,z,l) says l ≥ 0 and either l = 0 and every nonzero vector has growth rate 0, or l > 0 and there is a nonzero s such that every nonzero v has growth rate −l when wedge(s,v) = 0 and growth rate l otherwise. normalizedArea(E) is area restricted to E divided by area(E). IsBernoulli(f,μ) says there are a probability measure β on ℝ and almost-everywhere mutually inverse measure-preserving maps between (T²,μ) and the product measure β^ℤ on sequences, such that f corresponds to the left shift. HyperbolicBernoulliComponent(k) is the defined proposition that there is a measurable set E of positive area, almost invariant under standardMap(k), on which standardMap(k) is ergodic for normalizedArea(E), with almost every point having some positive l satisfying LyapunovSpectrumAt; moreover E is, up to null sets, a union of N ≥ 1 measurable pieces with pairwise null overlaps, each of positive area equal to area(E)/N, cyclically permuted almost everywhere by standardMap(k) (piece j goes to piece j+1 mod N), such that the N-th iterate of standardMap(k) is Bernoulli on each piece with its normalized area. MainComponentsObligation is the defined proposition, not an established theorem, that there exists k₀ > 0 such that HyperbolicBernoulliComponent(k) holds for every k ≥ k₀.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StandardMapComponents.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StandardMapComponents.lean; bytes 16..4687
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace StandardMapEntropy

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

lemma sine_periodic : Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  dsimp only
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact Real.sin_add_two_pi _

noncomputable def sine (x : Circle) : ℝ := sine_periodic.lift x

noncomputable def standardMap (k : ℝ) (z : Torus) : Torus :=
  (z.1 + z.2 + (k * sine z.1 : ℝ), z.2 + (k * sine z.1 : ℝ))

noncomputable def area : Measure Torus :=
  (volume : Measure Circle).prod (volume : Measure Circle)


lemma cosine_periodic : Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*x)) 1 := by
  intro x
  dsimp only
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring]
  exact Real.cos_add_two_pi _
noncomputable def cosine (x : Circle) : ℝ := cosine_periodic.lift x

noncomputable def torusPotential (k : ℝ) (x : Circle) : ℝ := 2+(2*Real.pi*k)*cosine x

noncomputable def transferStep (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨v*z.re-z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (((continuous_const.mul Complex.continuous_re).sub Complex.continuous_im).prodMk Complex.continuous_re) }

noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

noncomputable def tangentCoordinates : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.re, z.re-z.im⟩
        map_add' := by intro z w; apply Complex.ext <;> simp; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp; ring }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Complex.continuous_re.sub Complex.continuous_im)) }

local instance realTangentCompTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance

noncomputable def standardDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp ((transferStep (torusPotential k z.1)).comp tangentCoordinates)

noncomputable def standardDerivativeProduct (k : ℝ) (z : Torus) (steps : ℕ) : ℂ →L[ℝ] ℂ :=
  Nat.rec (ContinuousLinearMap.id ℝ ℂ)
    (fun iteration product => (standardDerivative k ((standardMap k)^[iteration] z)).comp product) steps

def VectorGrowth (k : ℝ) (z : Torus) (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n v‖ / (n : ℝ))
    atTop (𝓝 l)

def LyapunovSpectrumAt (k : ℝ) (z : Torus) (l : ℝ) : Prop :=
  0 ≤ l ∧ ((l = 0 ∧ ∀ v : ℂ, v ≠ 0 → VectorGrowth k z v 0) ∨
    (0 < l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
      VectorGrowth k z v (if wedge s v = 0 then -l else l)))

noncomputable def normalizedArea (E : Set Torus) : Measure Torus :=
  (area E)⁻¹ • area.restrict E

def IsBernoulli (f : Torus → Torus) (μ : Measure Torus) : Prop :=
  ∃ (β : Measure ℝ), IsProbabilityMeasure β ∧
    ∃ (encode : Torus → (ℤ → ℝ)) (decode : (ℤ → ℝ) → Torus),
      MeasurePreserving encode μ (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) ∧
      MeasurePreserving decode (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) μ ∧
      (∀ᵐ z ∂μ, decode (encode z) = z) ∧
      (∀ᵐ w ∂MeasureTheory.Measure.infinitePi (fun _ : ℤ => β), encode (decode w) = w) ∧
      (∀ᵐ z ∂μ, encode (f z) = fun i : ℤ => encode z (i+1))

def HyperbolicBernoulliComponent (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ((standardMap k) ⁻¹' E =ᵐ[area] E) ∧
    Ergodic (standardMap k) (normalizedArea E) ∧
    (∀ᵐ z ∂normalizedArea E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l) ∧
    ∃ (N : ℕ) (hN : 0 < N) (P : Fin N → Set Torus),
      (∀ j, MeasurableSet (P j)) ∧
      ((⋃ j, P j) =ᵐ[area] E) ∧
      (∀ i j, i ≠ j → area (P i ∩ P j) = 0) ∧
      (∀ j : Fin N, (standardMap k '' P j) =ᵐ[area]
        P ⟨(j.val+1)%N, Nat.mod_lt _ hN⟩) ∧
      (∀ j, area (P j) = area E / (N : ℝ≥0∞) ∧ 0 < area (P j)) ∧
      (∀ j, IsBernoulli ((standardMap k)^[N]) (normalizedArea (P j)))

def MainComponentsObligation : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k → HyperbolicBernoulliComponent k



end StandardMapEntropy
end OAI


