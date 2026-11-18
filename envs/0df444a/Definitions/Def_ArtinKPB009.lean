-- Prove2me | Definitions.Def_ArtinKPB009
-- name    : ArtinKPB009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:23:59.920238+00:00
-- url     : https://prove2.me/theorems/8220943c-805c-4784-843c-8f19453a1d14
-- title:
--   Definitions bundle ArtinKPB009 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 1 declaration of that development: 1 definition. The definitions and types are `ArtinKP.X.X.pou`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X_Discrete`.
--
--   **Imports.** It imports the bundle `ArtinKPB008` of this split; the published statement `ArtinKP.X.exists_isPOU_forall_pos`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB010`; the statement `ArtinKP.X.X.isPOU_pou`; the proof of `ArtinKP.X.X.isPOU_pou`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB008
import Theorems.Thm_ArtinKP_X_exists_isPOU_forall_pos

section
-- module Solutions.Artin.KP.X_Discrete
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-- A chosen positive partition of unity for `Γ`. -/
def X.pou (Γ : Subgroup (SL(2, 𝓞 F))) : X F → ℝ≥0∞ := Classical.choose (exists_isPOU_forall_pos Γ)

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end


