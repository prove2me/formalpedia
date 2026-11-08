-- Prove2me | Definitions.Def_AvoidPlast_SolvesAvoidND
-- name    : AvoidPlast_SolvesAvoidND
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:53.270058+00:00
-- url     : https://prove2.me/theorems/06127d91-a54d-4144-8f50-eb6b240175b7
-- title:
--   Non-deterministic solutions of Avoid$_C$
-- statement:
--   A non-deterministic algorithm $A$ solves Avoid$_C$ on $x$ if it has an accepting path on $x$ and every accepting path outputs an Avoid$_C$ solution. This is the page's convention (proof of Theorem 5.12, p.28, and the convention of p.4).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.12, p.27; proof, p.28; Theorem 1.6, p.4

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_SolvesAvoid

namespace AvoidPlast

/-- A non-deterministic algorithm `A` solves `Avoid_C` on `x` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.12, p.27, with the p.4
convention and the proof on p.28): `A` has an accepting path on `x`, and every accepting path outputs
an `Avoid_C` solution. -/
def SolvesAvoidND (A : Machine 2) (C : List Bool → List Bool → List Bool) (ℓin ℓout : ℕ → ℕ)
    (x : List Bool) : Prop :=
  (∃ w : List Bool, Accepts A ![x, w]) ∧
    ∀ w : List Bool, Accepts A ![x, w] → SolvesAvoid C ℓin ℓout x (output A ![x, w])

end AvoidPlast


