-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
-- name    : OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:22:58.979798+00:00
-- url     : https://prove2.me/theorems/2e538a46-bbf9-4562-a008-33350d61b366
-- title:
--   Weighted row and column domains for interpolation
-- statement:
--   Given real weights w_0, v_0, theta and w indexed by m coordinates, form column weights (w_0,w) and row weights (v_0,w/theta). The column domain is the finite real-weighted simplex at height H with column weights. The row domain is the product of Fin K and the strict weighted simplex at height H with row weights. These are the exact finite indexing domains used by the source interpolation matrix.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean#L58-L68

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

abbrev Column {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  ↥(PiExponent.realWeightedSimplex (columnWeights w0 w) H)

abbrev Row {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  Fin K × ↥(PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H)

end PiExponent.InterpolationMatrix

end OAI


