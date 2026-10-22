-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:30:45.866983+00:00
-- url     : https://prove2.me/theorems/875f1de1-f837-41e2-8311-a97bdfef90d9
-- title:
--   Convexity of the selected face family
-- statement:
--   This bundle supplies convexity of the selected face family. These are declarations about finite downward-closed face families and their selected index predicates, including the distinct void and {empty face} complexes. The Koszul-family predicate is combinatorial support data; it does not itself construct a polynomial resolution or assert exactness.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SrFamily/faceFamily_convex.lean, selected declarations in lines 18–21; source SHA-256 63212321228aef6fdad094ff45e0d6d53e88bf588ece2f30172d78f82ad7fad5; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs

namespace Proofs.BassLyubeznik.SrFamily

open Finset Proofs.BassLyubeznik.SignedCore

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem faceFamily_convex (K : SComplex V) : IsConvex (faceFamily K)
-- SWARM:STATEMENT-END
:= by
  exact fun _ _ _ _ hJ'' _ hJ'J'' => K.down_closed hJ'' hJ'J''
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SrFamily


