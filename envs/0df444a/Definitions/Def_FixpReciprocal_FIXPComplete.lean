-- Prove2me | Definitions.Def_FixpReciprocal_FIXPComplete
-- name    : FixpReciprocal_FIXPComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:34.465091+00:00
-- url     : https://prove2.me/theorems/58a41750-616e-4794-a89c-7665f9f971af
-- title:
--   The class FIXP, FIXP-hardness and FIXP-completeness
-- statement:
--   The class **FIXP** consists of the real-valued search problems that admit an SL-reduction to the basic FIXP problem. A problem $\Pi$ is **FIXP-hard** if every problem in FIXP admits an SL-reduction to $\Pi$, and **FIXP-complete** if in addition $\Pi\in$ FIXP.
--
--   Completeness makes exact computation in $\Pi$ equivalent, under SL-reductions, to the algebraic fixed-point problem defining the class.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Definition 3.1 and the paragraph after Definition 3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_FixpReciprocal_SLReduces
import Definitions.Def_FixpReciprocal_basicFIXP

namespace FixpReciprocal

/-- **The class FIXP (Definition 3.1):** "the real-valued search problems that admit an SL-reduction,
as defined in Definition 3.2, to such problems."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1, p.10. -/
def InFIXP (P : RealSearch) : Prop := SLReduces P basicFIXP

/-- **FIXP-hardness:** "every problem in FIXP admits an SL-reduction to Π."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §3, p.10. -/
def FIXPHard (Q : RealSearch) : Prop := ∀ P : RealSearch, InFIXP P → SLReduces P Q

/-- **FIXP-completeness:** "A search problem Π is FIXP-complete if Π ∈ FIXP and every problem in FIXP
admits an SL-reduction to Π."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §3, p.10. -/
def FIXPComplete (Q : RealSearch) : Prop := InFIXP Q ∧ FIXPHard Q

end FixpReciprocal


