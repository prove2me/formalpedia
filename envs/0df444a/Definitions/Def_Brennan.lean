-- Prove2me | Definitions.Def_Brennan
-- name    : Brennan
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.738984+00:00
-- url     : https://prove2.me/theorems/317d9477-4a87-4e52-a745-e49ff2bb15e2
-- statement:
--   Let D be the open unit disk in ℂ. A function is univalent on a set U if it is complex differentiable on U and injective there; it is schlicht if it is univalent on D, f(0)=0, and f′(0)=1. For real t and r, its integral mean is M(f,t,r)=(2π)⁻¹∫₋π^π |f′(re^{iθ})|ᵗ dθ. The extended-real growth exponent β(f,t) is the upper limit of log M(f,t,r)/log(1/(1−r)) as r approaches 1 from below, and the spectrum B(t) is the supremum of β(f,t) over all schlicht functions. A set has nontrivial spherical boundary when the boundary of its image in the one-point compactification of ℂ contains at least two points. MainStatement is the defined proposition consisting of four assertions: for every ε>0 there is a real constant C such that every schlicht f satisfies M(f,−2,r)≤C(1−r)^(−1−ε) for every 1/2≤r<1; B(−2)=1; whenever W⊆ℂ is open, connected, and simply connected with nontrivial spherical boundary, every complex-differentiable bijection φ from W onto D has |φ′|ˢ integrable over W with respect to planar Lebesgue measure for every 4/3<s<4; and every function f univalent on D has |f′|ᵗ integrable over D with respect to that measure for every −2<t<2/3. These four assertions are packaged as a proposition, rather than proved in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Brennan.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Brennan.lean; bytes 16..1638
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

def beta (f : ℂ → ℂ) (t : ℝ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean f t r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

def spectrum (t : ℝ) : EReal :=
  sSup {b | ∃ f : ℂ → ℂ, Schlicht f ∧ beta f t = b}

def SphericalBoundaryNontrivial (W : Set ℂ) : Prop :=
  Set.Nontrivial (frontier (((↑) : ℂ → OnePoint ℂ) '' W))

def MainStatement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
    ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)) ∧
  spectrum (-2) = 1 ∧
  (∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace W →
    SphericalBoundaryNontrivial W → ∀ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ W → Set.BijOn φ W disk →
      ∀ s : ℝ, 4 / 3 < s → s < 4 →
        IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W volume) ∧
  (∀ f : ℂ → ℂ, UnivalentOn f disk → ∀ t : ℝ,
    -2 < t → t < 2 / 3 →
      IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk volume)



end Brennan
end
end OAI


