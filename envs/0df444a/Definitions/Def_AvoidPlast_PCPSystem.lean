-- Prove2me | Definitions.Def_AvoidPlast_PCPSystem
-- name    : AvoidPlast_PCPSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:59.762678+00:00
-- url     : https://prove2.me/theorems/8b041d9b-01bc-4d0b-85e5-e96f4921b262
-- title:
--   PCP systems
-- statement:
--   The data of a PCP system: a verifier with read-only tapes for the input $x$, the random string $\rho$ and the proof $\pi$; a machine producing honest proofs from $(x,w)$; and the proof and randomness lengths as functions of $n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.1, p.17; proof of Theorem 5.12, p.28

import Mathlib
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast

/-- A PCP system (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.1, p.17 and proof of Theorem 5.12, p.28, "Fix a PCP system"): a
verifier with read-only tapes for the input `x`, the random string `ρ` and the proof `π`, the proof
and randomness lengths, and a machine producing honest proofs from `(x, w)`. -/
structure PCPSystem where
  /-- the verifier, on `(x, ρ, π)` -/
  V : Machine 3
  /-- the machine computing an honest proof from `(x, w)` -/
  P : Machine 2
  /-- the proof length -/
  proofLen : ℕ → ℕ
  /-- the randomness length -/
  randLen : ℕ → ℕ

end AvoidPlast


