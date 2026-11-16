-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_AntichainConstructor
-- name    : TarskiBootstrap_Dimensional_Supplement_AntichainConstructor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:04.399296+00:00
-- url     : https://prove2.me/theorems/9fc79ca3-4666-46eb-ae07-434f0a67da23
-- title:
--   Conjugation and the antichain constructor $\mathcal B$
-- statement:
--   For $x\in[n]^k$ its **conjugate** is $\bar x=(n-1)\mathbf 1-x$. For a self-map $f$ of $[n]^k$, the **antichain constructor** produces the self-map of $[n]^{2k}=[n]^k\times[n]^k$
--
--   $$
--   \mathcal B(f)(x,y)=\bigl(f(x),\ \overline{f(\bar y)}\bigr).
--   $$
--
--   For a family $\mathcal F$, $\mathcal B(\mathcal F)=\{\mathcal B(f):f\in\mathcal F\}$.
--
--   The constructor doubles the dimension and places the fixed points $(f^*,\overline{f^*})$ on the antichain of points with coordinate sum $k(n-1)$, which the logarithmic and dimensional bootstrapping theorems require.
--
--   **Formalization Note** $[n]^{2k}$ is represented as the product `Grid n k × Grid n k` with the componentwise order, which is the coordinatewise order on the $2k$ coordinates (an explicit order isomorphism is `flattenBlocks n k 2` of the published grid definition).
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 3.8 and equation (3.21), PDF/printed p. 16, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_FixedPoint

namespace TarskiBootstrap.Dimensional.Supplement

/-- The conjugate `x̄ = (n-1)𝟏 - x` of a grid point, §3.3, PDF/printed p. 16. -/
def gridConj {n k : ℕ+} (x : Grid n k) : Grid n k := fun i => Fin.rev (x i)

/-- Definition 3.8, PDF/printed p. 16: `B(f)(x, y) = (f(x), conj(f(conj y)))`.
The grid `[n]^{2k}` is the pair `Grid n k × Grid n k` with the product order, which is
the coordinatewise order on the `2k` coordinates. -/
def antichainConstructor {n k : ℕ+} (f : Grid n k → Grid n k) :
    Grid n k × Grid n k → Grid n k × Grid n k :=
  fun p => (f p.1, gridConj (f (gridConj p.2)))

/-- The image family `B(F) = {B(f) : f ∈ F}`. -/
def antichainFamily {n k : ℕ+} (F : Set (Grid n k → Grid n k)) :
    Set (Grid n k × Grid n k → Grid n k × Grid n k) :=
  Set.range (fun f : F => antichainConstructor f.val)

end TarskiBootstrap.Dimensional.Supplement


