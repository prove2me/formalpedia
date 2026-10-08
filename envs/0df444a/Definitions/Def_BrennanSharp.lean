-- Prove2me | Definitions.Def_BrennanSharp
-- name    : BrennanSharp
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.825264+00:00
-- url     : https://prove2.me/theorems/5db515c1-9409-4c52-84b7-c781b6ce2ffd
-- statement:
--   The disk is the open unit disk in the complex plane. A function is univalent on a set U when it is complex differentiable on U and injective there; it is schlicht when it is univalent on the disk and satisfies f(0)=0 and f′(0)=1. The Koebe map is k(z)=z/(1−z)², its domain image is Ω=k(disk), and koebeInverse is the inverse chosen from preimages in the disk, viewed as a function on the whole complex plane. For a function f, set U, and real exponent t, areaMoment(f,U,t) is the extended nonnegative Lebesgue integral over U of ‖f′(z)‖ᵗ with respect to planar area measure. SharpEndpointStatement is the defined proposition asserting that k is schlicht, that both areaMoment(k,disk,−2) and areaMoment(k,disk,2/3) are infinite, and that neither ‖(koebeInverse)′(z)‖⁴ nor ‖(koebeInverse)′(z)‖^(4/3) is integrable over Ω with respect to planar area measure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BrennanSharp.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BrennanSharp.lean; bytes 16..1010
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def koebeMap (z : ℂ) : ℂ := z/(1-z)^2

namespace Sharp

def koebeDomain : Set ℂ := koebeMap '' disk

def koebeInverse : ℂ → ℂ := Function.invFunOn koebeMap disk

def areaMoment (f : ℂ → ℂ) (U : Set ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ t) ∂volume

def SharpEndpointStatement : Prop :=
  Schlicht koebeMap ∧
  areaMoment koebeMap disk (-2) = ⊤ ∧
  areaMoment koebeMap disk (2 / 3) = ⊤ ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume



end Sharp
end Brennan
end
end OAI


