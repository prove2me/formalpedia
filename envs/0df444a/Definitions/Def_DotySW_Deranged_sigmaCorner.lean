-- Prove2me | Definitions.Def_DotySW_Deranged_sigmaCorner
-- name    : DotySW_Deranged_sigmaCorner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:43.450357+00:00
-- url     : https://prove2.me/theorems/af8f1551-7e6b-45af-9a16-8c505e67c79c
-- title:
--   The image $\sigma(e\mathcal B^{(n)}_{r,r}e)$ in $\mathrm{End}(\mathfrak{sl}_n^{\otimes r})$
-- statement:
--   The set of endomorphisms $T$ of $\mathfrak{sl}_n^{\otimes r}$ that are the restriction of $\sigma(x)$ for some $x$ in the deranged algebra. This is the left side of (20), and the algebra of operators whose commutant is the right side of (19).
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.3, Eqs. (19)–(20), p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_corner
import Definitions.Def_DotySW_Deranged_ActsBy

namespace DotySW.Deranged

/-- **The image `σ(e B^{(n)}_{r,r} e)` in `End(sl_n^{⊗r})`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.3, Eq. (20), p. 11.

The set of endomorphisms of `sl_n^{⊗r}` induced by the elements of the deranged algebra.

**Formalization Note** `End_{eBe}(sl_n^{⊗r})` in Eq. (19) is the commutant of this set. -/
def sigmaCorner (n r : ℕ) : Set (Module.End ℂ (slTensor n r)) :=
  {T | ∃ x ∈ corner n r, ActsBy n r x T}

end DotySW.Deranged


