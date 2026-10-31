-- Prove2me | Definitions.Def_DistortedCondExp_Distortion
-- name    : DistortedCondExp_Distortion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:53.703145+00:00
-- url     : https://prove2.me/theorems/f37122a2-266b-4484-93d3-75ca14cdb27b
-- title:
--   Distortion functions, distorted expectation and the class $\mathcal I$
-- statement:
--   Three objects from §1–§2.1 of Ma, Wong and Zhang.
--
--   1. **Distortion function** (Definition 2.1(i)). A mapping $\varphi:[0,1]\to[0,1]$ is a distortion function if it is continuous, strictly increasing, and satisfies $\varphi(0)=0$ and $\varphi(1)=1$.
--   2. **Distorted expectation** (eq. (1.2), Definition 2.1(ii)). On a probability space $(\Omega,\mathcal F,\mathbb P)$, for a random variable $\xi\ge 0$,
--   $$
--   \mathcal E[\xi]:=\int_0^\infty \varphi\bigl(\mathbb P(\xi\ge x)\bigr)\,dx .
--   $$
--   For $\varphi(p)=p$ this is the ordinary expectation $\mathbb E[\xi]=\int_0^\infty\mathbb P(\xi\ge x)\,dx$.
--   3. **The class $\mathcal I$** (eq. (2.1)). $\mathcal I:=\{g:\mathbb R\to[0,\infty) : g \text{ is bounded, continuous, and increasing}\}$.
--
--   The distorted expectation is the static object whose dynamic, time-consistent version the mission constructs; $\mathcal I$ is the class of payoffs $g(X_t)$ on which the conditional version is defined.
--
--   **Formalization Note** $\varphi$ is a function $\mathbb R\to\mathbb R$; continuity and strict monotonicity are required on $[0,1]$ only, and $\varphi([0,1])\subseteq[0,1]$ follows. The integral is a Bochner integral over $(0,\infty)$, which is $0$ when $\mathcal E[\xi]=\infty$; it is used only for random variables with finitely many values, for which it is finite. "Increasing" for $g\in\mathcal I$ is non-strict (`Monotone`), as in the paper.
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, Definition 2.1, p.4; eq. (1.2), p.1; eq. (2.1), p.5

import Mathlib

open MeasureTheory Set

namespace DistortedCondExp

/-- **Distortion function** (Ma–Wong–Zhang, *Time-consistent conditional expectation under
probability distortion*, arXiv:1809.08262v5, Definition 2.1(i), p.4): a mapping
`φ : [0, 1] → [0, 1]` that is continuous, strictly increasing, and satisfies `φ(0) = 0` and
`φ(1) = 1`.

**Formalization Note** `φ` is a function `ℝ → ℝ` whose values off `[0, 1]` are irrelevant;
continuity and strict monotonicity are required on `[0, 1]` only. That `φ` maps `[0, 1]` into
`[0, 1]` is a consequence of strict monotonicity and the two endpoint values. -/
def IsDistortion (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Icc 0 1) ∧ StrictMonoOn φ (Icc 0 1) ∧ φ 0 = 0 ∧ φ 1 = 1

/-- **Distorted expectation** (Ma–Wong–Zhang, arXiv:1809.08262v5, eq. (1.2), p.1, and
Definition 2.1(ii), p.4): for a random variable `ξ ≥ 0` on a probability space `(Ω, F, P)`,
`𝓔[ξ] := ∫₀^∞ φ(P(ξ ≥ x)) dx`.

**Formalization Note** The integral is the Bochner integral over `(0, ∞)` of
`y ↦ φ(P{ξ ≥ y})`, with `≥` as in (1.2) and `P` the real-valued measure `μ.real`. The Bochner
integral is `0` when the integrand is not integrable, i.e. when `𝓔[ξ] = ∞`; the paper's class
`𝕃¹_φ(F) := {ξ ∈ 𝕃⁰₊(F) : 𝓔[ξ] < ∞}` is the class where this is the paper's value. Every random
variable this development applies it to takes finitely many values, so it is in `𝕃¹_φ`. -/
noncomputable def distortedExp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (φ : ℝ → ℝ)
    (ξ : Ω → ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), φ (μ.real {ω | y ≤ ξ ω})

/-- **The class `ℐ`** (Ma–Wong–Zhang, arXiv:1809.08262v5, eq. (2.1), p.5):
`ℐ := {g : ℝ → [0, ∞) : g is bounded, continuous, and increasing}`.

**Formalization Note** "Increasing" is non-strict in this paper (it writes "strictly increasing"
where it means it), so it is `Monotone g`. Boundedness of a nonnegative function is boundedness
from above. -/
def InI (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ Monotone g ∧ (∀ x, 0 ≤ g x) ∧ BddAbove (range g)

end DistortedCondExp


