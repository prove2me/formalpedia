-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_TensorAdversary
-- name    : TarskiBootstrap_Dimensional_TensorAdversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:18:50.546395+00:00
-- url     : https://prove2.me/theorems/e2f98754-b4d0-4585-a52b-332dc6278746
-- title:
--   The chain tensor-sum matrix
-- statement:
--   With the tensor terms defined from the original matrix and vector, put
--
--   $$\Gamma=\sum_{i=1}^t\Gamma_i.$$
--
--   This is an explicit matrix on tuples of original inputs. Adversary validity, the numerator bound and the denominator bound are separate theorem statements.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Equation (3.7), PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_TensorTerm

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- The actual tensor sum Γ, equation (3.7), p. 13. -/
noncomputable def tensorAdversary {S : Type*} (t : ℕ+) (Γ₀ : Matrix S S ℝ)
    (v : S → ℝ) : Matrix (Fin (t : ℕ) → S) (Fin (t : ℕ) → S) ℝ :=
  ∑ i : Fin (t : ℕ), tensorTerm t Γ₀ v i

end TarskiBootstrap.Dimensional


