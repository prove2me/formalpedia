-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:31:34.289455+00:00
-- url     : https://prove2.me/theorems/899aa9d2-bee5-4e46-9cf5-60f4ecb8f4a8
-- title:
--   Monotonicity of the selected face family
-- statement:
--   This bundle supplies monotonicity of the selected face family. These are declarations about finite downward-closed face families and their selected index predicates, including the distinct void and {empty face} complexes. The Koszul-family predicate is combinatorial support data; it does not itself construct a polynomial resolution or assert exactness.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SrFamily/faceFamily_mono.lean, selected declarations in lines 19–23; source SHA-256 b9bbfbc6c4317cd2138a67fad0278de61729055147462d1d463ccaa657cdb9ad; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs

namespace Proofs.BassLyubeznik.SrFamily

open Finset Proofs.BassLyubeznik.SignedCore

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem faceFamily_mono {K' K : SComplex V} (h : K' ≤ K) (τ : Finset V) (hτ : faceFamily K' τ) :
    faceFamily K τ
-- SWARM:STATEMENT-END
:= by
  exact SComplex.le_def.mp h hτ
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SrFamily


