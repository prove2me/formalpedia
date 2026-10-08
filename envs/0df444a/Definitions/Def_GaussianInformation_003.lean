-- Prove2me | Definitions.Def_GaussianInformation_003
-- name    : GaussianInformation_003
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.670352+00:00
-- url     : https://prove2.me/theorems/b985274c-6163-4053-aa64-5e1444237753
-- statement:
--   Work in Ambient(d), d-dimensional Euclidean space, with m=⌊d/16⌋. sphereProbability(d) is the uniform probability measure on the unit sphere, obtained by normalizing Lebesgue measure on the unit ball and pushing it forward by x↦x/‖x‖. For a measure ν, the kernel potential J(ν,s) is the lower integral over u~ν of ‖u−s‖^(−2m), B(ν) is the ν-average of log J(ν,s), and Phi(ν) is the real part of the relative entropy KL(ν‖sphereProbability(d)) minus B(ν). BoundedDensity(ν) says ν ≤ H·sphereProbability(d) for some H>0. rowLaw(d) is the law of an m×d array of independent standard Gaussians, and labels(a,s) is the vector of the m inner products of the rows of a with s. A BlockRule(d,N) is a measurable family of probability vectors on Fin N, depending on a triple (a current index in Fin N, a Gaussian array, an m-vector of labels), with nonnegative entries summing to 1. Given a measure μ on Ambient(d)×Fin N, outgoingLaw(μ,rule) draws (s,v) from μ and an independent Gaussian array a, then moves to a new index w with probability given by the rule at (v,a,labels(a,s)), keeping s. component(μ,v) is the restriction of μ to index v, projected to Ambient(d); posterior(μ,v) is that component normalized to total mass one; averagePhi(μ) is the sum over v of component mass times Phi of the posterior. CoercivityStatement is a defined proposition: there exist C>0 and d₀ such that for all d≥d₀, every probability measure ν with bounded density satisfies Phi(ν) ≥ ½·KL(ν‖sphereProbability(d)) − Cd; Phi of the sphere measure is at most 2m·log 2; and Phi is convex along finite probability mixtures of bounded-density probability measures, meaning Phi of the mixture is at most the weighted average of the Phi values. DriftStatement is a defined proposition: there exist C>0 and d₀ such that for all d≥d₀, all N≥1 with log N ≤ d², every probability measure μ on Ambient(d)×Fin N whose first marginal is sphereProbability(d), and every BlockRule, averagePhi(outgoingLaw(μ,rule)) ≤ averagePhi(μ)+Cd. Neither is asserted as a proved theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianInformation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianInformation.lean; bytes 6297..9641
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianInformation_002

namespace OAI

open MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal

open MeasureTheory Metric

open scoped ENNReal

namespace AllScaleInverseVolume

attribute [local instance] _root_.OAI.AllScaleInverseVolume.namedAtLeastTwoTwo

attribute [local instance] _root_.OAI.AllScaleInverseVolume.ambientSub

attribute [local instance] _root_.OAI.AllScaleInverseVolume.ambientInner


end AllScaleInverseVolume


open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
local instance namedAtLeastTwoTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Rows (d : ℕ) := Fin (d/16) → Fin d → ℝ
noncomputable def radial {d : ℕ} (x : Ambient d) : Ambient d := ‖x‖⁻¹ • x
noncomputable def sphereProbability (d : ℕ) : Measure (Ambient d) :=
  ((volume (ball (0 : Ambient d) 1))⁻¹ • volume.restrict (ball (0 : Ambient d) 1)).map radial
noncomputable def J {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : ℝ≥0∞ :=
  ∫⁻ u,((ENNReal.ofReal ‖u-s‖)⁻¹)^(2*(d/16)) ∂ν
noncomputable def B {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  ∫ s, Real.log ((J ν s).toReal) ∂ν
noncomputable def Phi {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  (InformationTheory.klDiv ν (sphereProbability d)).toReal - B ν

def BoundedDensity {d : ℕ} (ν : Measure (Ambient d)) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ν ≤ ENNReal.ofReal H • sphereProbability d

noncomputable def rowLaw (d : ℕ) : Measure (Rows d) :=
  Measure.pi (fun _ : Fin (d/16) => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
noncomputable def labels {d : ℕ} (a : Rows d) (s : Ambient d) : Fin (d/16) → ℝ :=
  fun i => ∑ j,a i j*s j
structure BlockRule (d N : ℕ) where
  prob : (Fin N × (Rows d × (Fin (d/16) → ℝ))) → Fin N → ℝ
  measurable_prob : ∀ w, Measurable (fun x => prob x w)
  nonneg_prob : ∀ x w, 0 ≤ prob x w
  sum_prob : ∀ x, ∑ w,prob x w=1

noncomputable def outgoingLaw {d N : ℕ} (μ : Measure (Ambient d × Fin N))
    (rule : BlockRule d N) : Measure (Ambient d × Fin N) :=
  ∑ w : Fin N, ((μ.prod (rowLaw d)).withDensity (fun x =>
    ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w))).map (fun x => (x.1.1,w))
noncomputable def component {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (μ.restrict {x|x.2=v}).map Prod.fst
noncomputable def posterior {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (component μ v univ)⁻¹ • component μ v
noncomputable def averagePhi {d N : ℕ} (μ : Measure (Ambient d × Fin N)) : ℝ :=
  ∑ v : Fin N, (component μ v univ).toReal * Phi (posterior μ v)

def CoercivityStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ ν : Measure (Ambient d), IsProbabilityMeasure ν → BoundedDensity ν →
      (1/2:ℝ)*(InformationTheory.klDiv ν (sphereProbability d)).toReal-C*d ≤ Phi ν) ∧
    Phi (sphereProbability d) ≤ (2*(d/16):ℕ)*Real.log 2 ∧
    (∀ (q : ℕ) (w : Fin q → ℝ), (∀ i,0 ≤ w i) → (∑ i,w i)=1 →
      ∀ ν : Fin q → Measure (Ambient d), (∀ i,IsProbabilityMeasure (ν i)) →
      (∀ i,BoundedDensity (ν i)) →
      Phi (∑ i,ENNReal.ofReal (w i) • ν i) ≤ ∑ i,w i*Phi (ν i))

def DriftStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, 1 ≤ N →
    Real.log N ≤ (d:ℝ)^2 → ∀ μ : Measure (Ambient d × Fin N), IsProbabilityMeasure μ →
    μ.map Prod.fst=sphereProbability d → ∀ rule : BlockRule d N,
      averagePhi (outgoingLaw μ rule) ≤ averagePhi μ+C*d



end KernelPotential
end OAI


