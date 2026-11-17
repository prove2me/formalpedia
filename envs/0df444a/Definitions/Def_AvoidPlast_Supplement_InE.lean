-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InE
-- name    : AvoidPlast_Supplement_InE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:47:22.057367+00:00
-- url     : https://prove2.me/theorems/ac4c7376-03ce-4270-9f76-638c10484078
-- title:
--   The class $\mathsf E$
-- statement:
--   $\mathsf E=\bigcup_{c\in\mathbb N}\mathrm{DTIME}[2^{cn}]$: languages decidable in time $2^{O(n)}$.
--
--   Theorems 1.4, 5.10 and 5.11 simulate $\mathsf E$ in the worst case by low space or by few alternations.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.4, 5.10, 5.11, pp.4, 26–27

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_InDTIME

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The class `E = ∪_c DTIME[2^{cn}]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 1.4, 5.10, 5.11, pp.4, 26–27). -/
def InE (L : Set (List Bool)) : Prop := ∃ c : ℕ, InDTIME (fun n => 2 ^ (c * n)) L

end AvoidPlast.Supplement


