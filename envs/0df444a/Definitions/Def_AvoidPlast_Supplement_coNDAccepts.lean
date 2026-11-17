-- Prove2me | Definitions.Def_AvoidPlast_Supplement_coNDAccepts
-- name    : AvoidPlast_Supplement_coNDAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:12:38.085199+00:00
-- url     : https://prove2.me/theorems/6aeabcbd-c995-4e92-936b-fa543f276752
-- title:
--   Acceptance of a co-non-deterministic procedure
-- statement:
--   $D(x,r)=1$ iff every co-non-deterministic choice $w$ (of length at most $b$) makes $D(x,r,w)$ accept; $D(x,r)=0$ otherwise.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.7, p.15; Definition 7.1, p.39

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `D(x, r) = 1` for a co-non-deterministic procedure (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.7, p.15; Definition
7.1, p.39): every co-non-deterministic choice `w` of length at most `b` makes `D(x, r, w)` accept. -/
def coNDAccepts (D : Machine 3) (b : ℕ) (x r : List Bool) : Prop :=
  ∀ w : List Bool, w.length ≤ b → Accepts D ![x, r, w]

end AvoidPlast.Supplement


