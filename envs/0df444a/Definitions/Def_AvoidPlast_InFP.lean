-- Prove2me | Definitions.Def_AvoidPlast_InFP
-- name    : AvoidPlast_InFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:31.012232+00:00
-- url     : https://prove2.me/theorems/c164bc0f-1334-429d-b971-c5fede8d11cf
-- title:
--   The class FP
-- statement:
--   A function $f:\{0,1\}^*\to\{0,1\}^*$ is in **FP** if a polynomial-time machine computes it, the whole multi-bit output being printed on the output tape.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_PolyTime

namespace AvoidPlast

/-- The class FP (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 1.2, p.3): functions `f : {0,1}^* → {0,1}^*` computed by a
deterministic polynomial-time machine, multi-bit outputs included. -/
def InFP (f : List Bool → List Bool) : Prop :=
  ∃ M : Machine 1, PolyTime M ∧ ∀ x, output M ![x] = f x

end AvoidPlast


