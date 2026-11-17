-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InP
-- name    : AvoidPlast_Supplement_InP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:46:16.811196+00:00
-- url     : https://prove2.me/theorems/9441d87a-5f21-4099-90cd-277fede830a8
-- title:
--   The class P
-- statement:
--   A language $L\subseteq\{0,1\}^*$ is in $\mathsf P$ if a deterministic polynomial-time machine (in the mission's RAM model) accepts exactly the strings of $L$.
--
--   This is the class whose average-case low-space or alternating simulation is studied in Theorems 3.14, 5.6, 5.8–5.11.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3.4, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PolyTime

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The class P (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3.2 and §3.4, p.16): `L` is decided by a deterministic
polynomial-time machine, `x ∈ L` iff the machine accepts `x`. -/
def InP (L : Set (List Bool)) : Prop :=
  ∃ M : Machine 1, PolyTime M ∧ ∀ x : List Bool, Accepts M ![x] ↔ x ∈ L

end AvoidPlast.Supplement


