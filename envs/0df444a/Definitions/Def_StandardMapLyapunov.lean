-- Prove2me | Definitions.Def_StandardMapLyapunov
-- name    : StandardMapLyapunov
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:26.365136+00:00
-- url     : https://prove2.me/theorems/2a3ee1fb-c381-4265-88dd-1bf70e83552c
-- statement:
--   The block works on the torus Circle × Circle, where Circle is the real numbers modulo 1, with area the product of the Lebesgue measures. The functions sine and cosine on the circle are x ↦ sin(2πx) and x ↦ cos(2πx), lifted from their period-1 versions. The standard map with parameter k sends (x,y) to (x+y+k·sine(x), y+k·sine(x)). For entropy, a FinitePartition with r is a measurable function from the torus to Fin(r+1); blockAtom is the set of points whose first n iterates under f have the prescribed partition labels w. blockEntropy is −Σ_w μ(atom)·log μ(atom) over all label words, with real-valued measures; partitionEntropy is the infimum over n≥1 of ofReal(blockEntropy for n steps divided by n), valued in [0,∞]; metricEntropy is the supremum over r and over partitions of that quantity. For Lyapunov exponents, torusPotential(k,x) = 2 + 2πk·cosine(x), and transferStep(v) is the real-linear map on ℂ sending z to (v·Re z − Im z) + i·Re z. tangentCoordinates sends z to Re z + i(Re z − Im z). standardDerivative(k,z) is tangentCoordinates composed with transferStep(torusPotential(k, first coordinate of z)) composed with tangentCoordinates, and standardDerivativeProduct(k,z,n) composes these along the first n orbit points of the standard map, with the earliest applied first. wedge(z,w) = Re z·Im w − Im z·Re w. VectorGrowth(k,z,v,l) says v≠0 and (1/n)·log‖product_n v‖ tends to l. LyapunovSpectrumAt(k,z,l) requires l≥0 and either l=0 with every nonzero vector having growth rate 0, or l>0 with a nonzero vector s such that every nonzero v has growth rate −l if wedge(s,v)=0 and l otherwise. PositiveLargestLyapunov(k) is the defined proposition that some measurable set E of positive area exists such that every z in E has some l>0 with LyapunovSpectrumAt(k,z,l) and with (1/n)·log of the operator norm of the product tending to l. It is a defined proposition, not a proved result.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StandardMapLyapunov.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StandardMapLyapunov.lean; bytes 16..4245
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

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

def FinitePartition (r : ℕ) := { p : Torus → Fin (r + 1) // Measurable p }

def blockAtom {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r + 1)) : Set Torus :=
  { z | ∀ i : Fin n, p.val (f^[i.val] z) = w i }

noncomputable def blockEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) (n : ℕ) : ℝ :=
  - ∑ w : Fin n → Fin (r + 1),
    (μ (blockAtom f p n w)).toReal * Real.log (μ (blockAtom f p n w)).toReal

noncomputable def partitionEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (blockEntropy μ f p (n + 1) / (n + 1 : ℝ))

noncomputable def metricEntropy (μ : Measure Torus) (f : Torus → Torus) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ p : FinitePartition r, partitionEntropy μ f p


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

noncomputable def standardDerivativeProduct (k : ℝ) (z : Torus) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  Nat.rec (ContinuousLinearMap.id ℝ ℂ)
    (fun i A => (standardDerivative k ((standardMap k)^[i] z)).comp A) n

noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

def VectorGrowth (k : ℝ) (z : Torus) (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n v‖ / (n : ℝ))
    atTop (𝓝 l)

def LyapunovSpectrumAt (k : ℝ) (z : Torus) (l : ℝ) : Prop :=
  0 ≤ l ∧ ((l = 0 ∧ ∀ v : ℂ, v ≠ 0 → VectorGrowth k z v 0) ∨
    (0 < l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 →
      VectorGrowth k z v (if wedge s v = 0 then -l else l)))

def PositiveLargestLyapunov (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ∀ z ∈ E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l ∧
      Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 l)



end StandardMapEntropy
end OAI


