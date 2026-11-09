-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws
-- name    : MomentAmbiguitySecretary_Secretary_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:33.474782+00:00
-- url     : https://prove2.me/theorems/cd68ac7f-829e-4707-9cae-2c603ade745f
-- title:
--   Admissible nonnegative laws and exact moment disclosure
-- statement:
--   A law is a Borel probability measure $\mu$ on $[0,\infty)$ with finite moments of every nonnegative integer order. Write
--
--   $$M(\mu)_k=\int x^k\,d\mu(x),\qquad k\ge0.$$
--
--   Two laws are moment-equivalent when both have every finite moment and these sequences agree. A disclosed sequence is realizable when it equals $M(\mu)$ for such a law; its ambiguity class consists of all compatible laws. The Dirac law at zero witnesses nonemptiness.
--
--   This supplies the common information interface, without any support or density restriction. The moment integrals are used only for laws carrying their all-orders integrability condition.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Definitions 2.1–2.2, PDF/printed p.4, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Mathlib

open scoped NNReal

open MeasureTheory

namespace MomentAmbiguitySecretary.Secretary

abbrev Distribution := ProbabilityMeasure ℝ≥0

def HasAllMoments (μ : Distribution) : Prop :=
  ∀ k : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μ : Measure ℝ≥0)

abbrev Law := {μ : Distribution // HasAllMoments μ}

noncomputable def moments (μ : Distribution) : ℕ → ℝ :=
  fun k => ∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μ : Measure ℝ≥0)

def MomentEquivalent (μ ν : Distribution) : Prop :=
  HasAllMoments μ ∧ HasAllMoments ν ∧ moments μ = moments ν

def momentClass (s : ℕ → ℝ) : Set Distribution :=
  {μ | HasAllMoments μ ∧ moments μ = s}

/-- Only realizable full moment sequences are disclosed. -/
abbrev Disclosure := {s : ℕ → ℝ // ∃ μ : Law, moments μ.val = s}

noncomputable def disclose (μ : Law) : Disclosure :=
  ⟨moments μ.val, μ, rfl⟩

noncomputable def zeroLaw : Law :=
  ⟨⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩, by
    intro k
    change Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (Measure.dirac (0 : ℝ≥0))
    exact integrable_dirac (f := fun x : ℝ≥0 => (x : ℝ) ^ k) (by simp)⟩

instance : Nonempty Law := ⟨zeroLaw⟩
instance : Nonempty Disclosure := ⟨disclose zeroLaw⟩

end MomentAmbiguitySecretary.Secretary


