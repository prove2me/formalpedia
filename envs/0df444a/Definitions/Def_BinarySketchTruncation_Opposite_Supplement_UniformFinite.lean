-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UniformFinite
-- name    : BinarySketchTruncation_Opposite_Supplement_UniformFinite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:34.366268+00:00
-- url     : https://prove2.me/theorems/041c8e36-be27-4417-912d-e0737ae5062d
-- title:
--   Uniform finite probability, variance and coordinate conditioning
-- statement:
--   Let Ω be a nonempty finite set, with the uniform probability law. For a real function q on Ω and an event E ⊆ Ω, define
--
--   $$
--   \mathbb E[q]=\frac{\sum_{x\in\Omega}q(x)}{|\Omega|},\qquad
--   \Pr(E)=\mathbb E[\mathbf1_E],\qquad
--   \operatorname{Var}(q)=\mathbb E[(q-\mathbb E[q])^2].
--   $$
--
--   For a finite coordinate set D, a binary vector z ∈ 𝔽₂ᴰ and I ⊆ D, let C_I(z) consist of all w that agree with z on I. The conditional mean of q given those coordinates is
--
--   $$
--   \mathbb E[q(Z)\mid Z_I](z)=\frac{\sum_{w\in C_I(z)}q(w)}{|C_I(z)|}.
--   $$
--
--   The fiber contains z, so its denominator is positive, including when D or I is empty. These are ordinary uniform expectations and conditional expectations, shared by function evaluation and graph connectivity. The definitions use finite sums and real probabilities, with the published binary field as their coordinate alphabet.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 9, 11–12, 18–19 (PDF pp. 10, 12–13, 19–20), Eqs. (3), (7), Lemma 3 and Appendix A.2

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite.Supplement

/-- Arithmetic expectation on a nonempty finite uniform sample space. -/
noncomputable def uniformMean {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) : ℝ := (∑ x, f x) / Fintype.card Ω

/-- Uniform probability, with real rather than extended-real values. -/
noncomputable def uniformProbability {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) : ℝ := by
  classical
  exact uniformMean (fun x => if E x then 1 else 0)

/-- Centered second moment, on the same finite uniform sample space. -/
noncomputable def uniformVariance {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) : ℝ := uniformMean (fun x => (f x - uniformMean f) ^ 2)

/-- The complete fiber of the observed coordinates. It always contains z,
including when the coordinate set or index type is empty. -/
noncomputable def coordinateFiber {ι : Type} [Fintype ι]
    (I : Finset ι) (z : ι → Bit) : Finset (ι → Bit) := by
  classical
  exact Finset.univ.filter (fun w => ∀ i ∈ I, w i = z i)

/-- Conditional expectation given the coordinates in I: average over their fiber.
The denominator is positive since z belongs to its own fiber. -/
noncomputable def coordinateConditionalMean {ι : Type} [Fintype ι]
    (f : (ι → Bit) → ℝ) (I : Finset ι) (z : ι → Bit) : ℝ :=
  (∑ w ∈ coordinateFiber I z, f w) / (coordinateFiber I z).card

end BinarySketchTruncation.Opposite.Supplement


