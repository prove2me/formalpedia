-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_ImageAdversary
-- name    : TarskiBootstrap_Dimensional_ImageAdversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:30:15.714271+00:00
-- url     : https://prove2.me/theorems/da83bace-2dc7-468c-b4eb-65d932248040
-- title:
--   Tensor matrix on actual chained instances
-- statement:
--   Transfer the tensor-sum entries from tuple indices to the image family by
--
--   $$\Gamma'[g,h]=\Gamma[\operatorname{pre}(g),\operatorname{pre}(h)],\qquad g,h\in C_t(F^t).$$
--
--   The preimage selector is defined from image membership. Lemma 3.3 establishes that $C_t$ is injective, after which this transfer is exactly a permutation of the matrix indices. The definition alone does not assert injectivity, adversary validity or a norm bound.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, §3.2, equation (3.5) and preceding indexing paragraph, PDF/printed p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_TensorAdversary
import Definitions.Def_TarskiBootstrap_Dimensional_ChainFamily
import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- The same entries on the actual image family, using Lemma 3.3's indexing. -/
noncomputable def imageAdversary {n k : ℕ+} (t : ℕ+) (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k)) (Γ₀ : Matrix F F ℝ) (v : F → ℝ) :
    Matrix (chainFamily t A F) (chainFamily t A F) ℝ :=
  fun f g => tensorAdversary t Γ₀ v (chainPreimage t A F f) (chainPreimage t A F g)

end TarskiBootstrap.Dimensional


