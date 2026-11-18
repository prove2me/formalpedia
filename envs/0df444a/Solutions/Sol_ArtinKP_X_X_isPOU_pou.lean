-- Prove2me | solution 1 for ArtinKP.X.X.isPOU_pou
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:24:48.476202+00:00
-- url     : https://prove2.me/submissions/131de891-d7ae-4508-9747-47aab3c932dc

import Mathlib
import Definitions.Def_ArtinKPB009
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

lemma X.isPOU_pou_oai (Γ : Subgroup (SL(2, 𝓞 F))) : IsPOU Γ (X.pou Γ) :=
  (Classical.choose_spec (exists_isPOU_forall_pos Γ)).1

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.isPOU_pou_oai.{u_1} := @ArtinKP.X.X.isPOU_pou_oai.{u_1}
