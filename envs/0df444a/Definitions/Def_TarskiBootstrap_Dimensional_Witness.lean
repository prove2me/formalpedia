-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Witness
-- name    : TarskiBootstrap_Dimensional_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:13:54.046422+00:00
-- url     : https://prove2.me/theorems/6691ea1b-2726-4a98-b013-bf4f1ab9bec6
-- title:
--   Spectral witness inequalities
-- statement:
--   For a real matrix $\Gamma$ on a finite input set and real numbers $\lambda,\delta$, the spectral witness inequalities are
--
--   $$\|\Gamma\|_{2\to2}\ge\lambda,\qquad\forall x,\quad\|\Gamma\circ\Delta_x\|_{2\to2}\le\delta.$$
--
--   Here $\circ$ is entrywise multiplication. Each norm is the norm of the associated continuous linear operator on real Euclidean space, with counting-measure coordinates and no normalization. The paper calls this a lower bound of $\lambda/\delta$ when $\delta>0$; every theorem using that terminology supplies this positivity separately. Adversary validity is also a separate condition.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, §2.3, equation (2.9), PDF/printed p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Adversary
import Definitions.Def_TarskiBootstrap_Dimensional_QueryMask

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Equation (2.9), p. 7. The norm is explicitly the real Euclidean operator norm. -/
noncomputable def SpectralWitness {S Q O : Type*} [Fintype S]
    (oracle : S → Q → O) (Γ : Matrix S S ℝ) (lam δ : ℝ) : Prop := by
  classical
  exact lam ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ∧
    ∀ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ ⊙ queryMask oracle x)‖ ≤ δ

end TarskiBootstrap.Dimensional


