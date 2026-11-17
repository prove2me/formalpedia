-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InPSPACE
-- name    : AvoidPlast_Supplement_InPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:48:39.820662+00:00
-- url     : https://prove2.me/theorems/b1759255-d233-4113-9073-ca95bd9c2959
-- title:
--   The class PSPACE
-- statement:
--   $\mathsf{PSPACE}=\bigcup_{k\in\mathbb N}\mathrm{SPACE}[n^k]$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3.4, p.16; Theorem 6.1, p.31

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_InSPACE

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The class `PSPACE = ∪_k SPACE[n^k]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3.4, p.16; Theorem 6.1, p.31). -/
def InPSPACE (L : Set (List Bool)) : Prop := ∃ k : ℕ, InSPACE (fun n => (n : ℝ) ^ k) L

end AvoidPlast.Supplement


