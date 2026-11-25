-- Prove2me | Definitions.Def_DetDLP_S8M_AtomMapNatFits
-- name    : DetDLP_S8M_AtomMapNatFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:36:18.526745+00:00
-- url     : https://prove2.me/theorems/23ee06f5-7ae0-4cd7-ad87-0431f89ba3df
-- title:
--   Named atom and conversion block fits
-- statement:
--   Canonical name models for atom and conversion blocks of the EC pair network.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomMapNat
import Definitions.Def_DetDLP_S8M_AtomMapModel_v2

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.AtomMapNatFits

open S8H0.RegisterMap S8H0.GateRoutes
open DetDLP.S8M.Routes DetDLP.S8M.MakePacket DetDLP.S8M.AtomMapNat

variable {m d e : ℕ}

/-- The flattened pure-natural atom code fits its routed seed-query block.
The bank edge parameter remains abstract throughout. -/
theorem atom_spec (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S : SeedData m) (i : Fin (2*m)) :
    Fits (atomN hd p T c S i) (atomRows hd p T c S i) := by
  exact DetDLP.S8M.MakePacket.atomN_Fits hd p T c S i

/-- The flattened pure-natural conversion code fits its routed map block.
The bank edge parameter remains abstract throughout. -/
theorem map_spec (hd : 1 ≤ d) (p b2 a1 a3 : ℕ)
    (i : Fin (2*m)) :
    Fits (mapN (m := m) hd p b2 a1 a3 i)
      (mapRows (m := m) hd p b2 a1 a3 i) := by
  exact DetDLP.S8M.MakePacket.mapN_Fits hd p b2 a1 a3 i

end DetDLP.S8M.AtomMapNatFits


