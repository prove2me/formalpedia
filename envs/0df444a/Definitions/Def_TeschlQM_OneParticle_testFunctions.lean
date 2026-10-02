-- Prove2me | Definitions.Def_TeschlQM_OneParticle_testFunctions
-- name    : TeschlQM_OneParticle_testFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:43:18.249785+00:00
-- url     : https://prove2.me/theorems/58c4f28b-47e7-48f6-8bd1-9006fd2ea804
-- title:
--   C_c^∞(ℝⁿ) as a subspace of L²(ℝⁿ)
-- statement:
--   $C_c^\infty(\mathbb R^n)$ is the space of infinitely differentiable functions $\mathbb R^n \to \mathbb C$ with compact support, regarded as a subspace of $L^2(\mathbb R^n)$: an element $\psi \in L^2(\mathbb R^n)$ belongs to it if $\psi$ agrees almost everywhere with such a function.
--
--   It is a core for $H_0$ (Lemma 7.9) and, for the potentials of Theorem 10.2, for $H_0 + V$.
--
--   **Formalization Note.** Smoothness is `ContDiff ℝ ∞` (infinitely differentiable, not analytic), compact support is `HasCompactSupport`, and membership is almost-everywhere equality of the $L^2$ class with such a function.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 168, Section 7.2, Lemma 7.9

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator

namespace TeschlQM.OneParticle

open MeasureTheory
open scoped ContDiff

/-- Teschl, Lemma 7.9, p. 168: `C_c^∞(ℝⁿ)`, the smooth functions with compact support, as a
subspace of `L²(ℝⁿ)`: the classes having a representative that is `C^∞` and compactly
supported. -/
def testFunctions (n : ℕ) : Submodule ℂ (L2 n) where
  carrier := {ψ | ∃ f : EuclideanSpace ℝ (Fin n) → ℂ,
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    exact Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))
  add_mem' := by
    rintro ψ φ ⟨f, hf, hfc, hψ⟩ ⟨g, hg, hgc, hφ⟩
    refine ⟨f + g, hf.add hg, hfc.add hgc, ?_⟩
    filter_upwards [Lp.coeFn_add ψ φ, hψ, hφ] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2, Pi.add_apply]
  smul_mem' := by
    rintro c ψ ⟨f, hf, hfc, hψ⟩
    refine ⟨c • f, contDiff_const.smul hf, hfc.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c ψ, hψ] with x hx h1
    rw [hx, Pi.smul_apply, h1, Pi.smul_apply]

end TeschlQM.OneParticle


