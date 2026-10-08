-- Prove2me | Definitions.Def_Conductivity
-- name    : Conductivity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.907641+00:00
-- url     : https://prove2.me/theorems/c8235a9b-c126-4aaa-b965-03071cff94e0
-- statement:
--   On the open ball B of radius 3 centered at the origin in ℝ³, with restricted Lebesgue measure, a smooth function has a four-component jet consisting of its value and its gradient. The ambient jet space is L²(B; ℝ⁴). H¹ is the closure of the real linear span of square-integrable jets of globally smooth functions; H¹₀ consists of those H¹ elements lying in the ambient closure of the span of jets of smooth functions with compact support contained in B. This zero-trace subspace is closed, and the trace space is the quotient H¹/H¹₀, with trace given by the quotient map. The weak gradient of an H¹ element is its last three jet components. For a scalar conductivity γ, the energy pairing is Eγ(u,v)=∫B γ⟨∇u,∇v⟩. An element u is γ-harmonic if Eγ(u,h)=0 for every h in H¹₀. A Dirichlet-to-Neumann operator is a continuous linear map Λ from the trace space to its continuous linear dual such that each trace f has a unique γ-harmonic extension u and Λ(f)(trace(v))=Eγ(u,v) for every v in H¹. Being equal to one near the boundary means that γ=1 almost everywhere on some annulus r<‖x‖<3 with 0<r<3. MainStatement is the defined proposition that there exist two measurable, essentially bounded conductivities γ₀ and γ₁, constants 0<c<C, and one such operator Λ, with c≤γᵢ≤C almost everywhere for both conductivities, both equal to one near the boundary, differing on a set of positive measure in B, and both having Λ as their Dirichlet-to-Neumann operator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Conductivity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Conductivity.lean; bytes 16..2793
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev JetFiber := EuclideanSpace ℝ (Fin 4)
def ball : Set R3 := Metric.ball 0 3
def ballMeasure : Measure R3 := volume.restrict ball
abbrev JetSpace := Lp JetFiber 2 ballMeasure

def smoothJet (f : R3 → ℝ) (x : R3) : JetFiber :=
  WithLp.toLp 2 (Fin.cases (f x) (fun i => gradient f x i))

def smoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def compactSmoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (_ : HasCompactSupport f) (_ : tsupport f ⊆ ball)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def H1Space : Submodule ℝ JetSpace :=
  (Submodule.span ℝ smoothJets).topologicalClosure
abbrev H1 := H1Space

def zeroTraceAmbient : Submodule ℝ JetSpace :=
  (Submodule.span ℝ compactSmoothJets).topologicalClosure

def H10 : Submodule ℝ H1 := zeroTraceAmbient.comap H1Space.subtype

instance H10_isClosed : IsClosed (H10 : Set H1) := by
  exact (Submodule.isClosed_topologicalClosure
    (Submodule.span ℝ compactSmoothJets)).preimage continuous_subtype_val

abbrev TraceSpace := H1 ⧸ H10
abbrev TraceDual := TraceSpace →L[ℝ] ℝ
abbrev DNOperator := TraceSpace →L[ℝ] TraceDual

def trace (u : H1) : TraceSpace := H10.mkQ u

def weakGradient (u : H1) (x : R3) : R3 :=
  WithLp.toLp 2 (fun i => (u.val x) i.succ)

def energy (γ : R3 → ℝ) (u v : H1) : ℝ :=
  ∫ x, γ x * inner ℝ (weakGradient u x) (weakGradient v x) ∂ballMeasure

def Harmonic (γ : R3 → ℝ) (u : H1) : Prop :=
  ∀ h : H1, h ∈ H10 → energy γ u h = 0

def IsDirichletToNeumann (γ : R3 → ℝ) (Λ : DNOperator) : Prop :=
  ∀ f : TraceSpace, ∃ u : H1,
    trace u = f ∧ Harmonic γ u ∧
    (∀ u' : H1, trace u' = f → Harmonic γ u' → u' = u) ∧
    ∀ v : H1, Λ f (trace v) = energy γ u v

def EqualOneNearBoundary (γ : R3 → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 3 ∧ ∀ᵐ x ∂ballMeasure, r < ‖x‖ → γ x = 1

def MainStatement : Prop :=
  ∃ (γ₀ γ₁ : R3 → ℝ) (c C : ℝ) (Λ : DNOperator),
    0 < c ∧ c < C ∧
    Measurable γ₀ ∧ Measurable γ₁ ∧
    MemLp γ₀ ∞ ballMeasure ∧ MemLp γ₁ ∞ ballMeasure ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₀ x ∧ γ₀ x ≤ C) ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₁ x ∧ γ₁ x ≤ C) ∧
    EqualOneNearBoundary γ₀ ∧ EqualOneNearBoundary γ₁ ∧
    0 < ballMeasure {x | γ₀ x ≠ γ₁ x} ∧
    IsDirichletToNeumann γ₀ Λ ∧ IsDirichletToNeumann γ₁ Λ



end ScalarConductivity
end
end OAI


