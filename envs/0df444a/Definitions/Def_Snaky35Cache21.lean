-- Prove2me | Definitions.Def_Snaky35Cache21
-- name    : Snaky35Cache21
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T12:50:01.725989+00:00
-- url     : https://prove2.me/theorems/98d22884-61e8-4f3a-bb38-3070c2e135ba
-- title:
--   Snaky35Cache21
-- statement:
--   Candidate literal RowData values for original 35-move certificate rows 610 through 614, consisting only of the required cells, the envelope cells, and height. Their equality to the original rowAt recursion is established by separate support theorems; these literals alone do not assert correctness.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean; Proposition 10, original 35-move finite certificate.

import Definitions.Def_Snaky35Cache21Row610
import Definitions.Def_Snaky35Cache21Row611
import Definitions.Def_Snaky35Cache21Row612
import Definitions.Def_Snaky35Cache21Row613
import Definitions.Def_Snaky35Cache21Row614
namespace OAI.SnakyCertificate.MilestoneChecks
def cache21Rows : List ℕ := [610, 611, 612, 613, 614]
end OAI.SnakyCertificate.MilestoneChecks


