-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Chain
-- name    : TarskiBootstrap_Dimensional_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:22:03.750805+00:00
-- url     : https://prove2.me/theorems/0eadd486-c958-409f-a34d-f55b911361ea
-- title:
--   The prescribed chain oracle
-- statement:
--   For the padding $T$ and stopping index $\sigma$, the **chain constructor** has output block
--
--   $$C_t(\mathbf f)(\mathbf x)_i=\begin{cases}x_i&i<\sigma,\\f_i(x_i)&i=\sigma,\\T(x_\sigma)&i>\sigma.\end{cases}$$
--
--   When every query block is fixed, every output block equals its input block. The implementation guards access to the stopping block, so it never reads the sentinel as a coordinate. No injectivity, monotonicity or fixed-point conclusion is included in this construction.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 3.1, equation (3.3), PDF/printed p. 11, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Padding
import Definitions.Def_TarskiBootstrap_Dimensional_StoppingIndex

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Definition 3.1, p. 11; the guard prevents reading the sentinel block. -/
noncomputable def chain {n k t : ℕ+} (A : Set (Grid n k))
    (f : Fin (t : ℕ) → (Grid n k → Grid n k)) (x : Blocks n k t) : Blocks n k t :=
  fun i =>
    let s := firstNonfixed f x
    if i.val < s then x i
    else if i.val = s then f i (x i)
    else if hs : s < (t : ℕ) then padding A (x ⟨s, hs⟩) else x i

end TarskiBootstrap.Dimensional


