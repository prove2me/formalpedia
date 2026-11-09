-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_ChainFamily
-- name    : TarskiBootstrap_Dimensional_ChainFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:26:31.274751+00:00
-- url     : https://prove2.me/theorems/277a73bf-b41a-46ac-ac0d-24ca8b5f6151
-- title:
--   The image family and tuple indexing
-- statement:
--   For a family $F$ of actual grid maps, restrict $C_t$ to tuples in $F^t$ and define the output family by
--
--   $$F'=C_t(F^t).$$
--
--   The family is a set of actual block-grid endomaps. A preimage selector chooses a tuple mapping to each member of the image. Existence follows from image membership; uniqueness is a conclusion of Lemma 3.3 and is not assumed or embedded in the selector. This interface allows the tensor matrix to be indexed by actual output instances.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 3.1, PDF/printed p. 11; Lemma 3.3, p. 12; §3.2, p. 13, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Chain
import Definitions.Def_TarskiBootstrap_Dimensional_FixedPoint

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- C_t restricted to tuples of members of F, Definition 3.1, p. 11. -/
noncomputable def chainOnFamily {n k : ℕ+} (t : ℕ+) (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k))
    (f : Fin (t : ℕ) → F) : Blocks n k t → Blocks n k t :=
  chain A (fun i => (f i).val)

/-- The image family, not a freely supplied family, Theorem 1.1, pp. 4, 10. -/
def chainFamily {n k : ℕ+} (t : ℕ+) (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k)) : Set (Blocks n k t → Blocks n k t) :=
  Set.range (chainOnFamily t A F)

/-- A preimage selector; Lemma 3.3, not this definition, supplies its uniqueness. -/
noncomputable def chainPreimage {n k : ℕ+} (t : ℕ+) (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k)) (g : chainFamily t A F) : Fin (t : ℕ) → F :=
  Classical.choose g.property

end TarskiBootstrap.Dimensional


