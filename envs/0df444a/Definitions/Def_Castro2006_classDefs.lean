-- Prove2me | Definitions.Def_Castro2006_classDefs
-- name    : Castro2006_classDefs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T19:50:15.991433+00:00
-- url     : https://prove2.me/theorems/14c1692b-bbfc-45c9-a615-022993c3e2bf
-- title:
--   Action specifications for the modular and semidihedral groups
-- statement:
--   Predicates specifying the generator actions of the two exceptional semidirect products in the classification.

import Mathlib

namespace Castro2006

/-- The generator of `ZMod p` acts on `ZMod (p^n)` by multiplication by `1 + p^(n-1)`
(the modular action defining the type-(3) group). -/
def IsModularAction (p n : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ n)))) : Prop :=
  ∀ u : ZMod (p ^ n),
    φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd u) =
      Multiplicative.ofAdd ((1 + (p : ZMod (p ^ n)) ^ (n - 1)) * u)

/-- The generator of `ZMod 2` acts on `ZMod (2^n)` by multiplication by `-1 + 2^(n-1)`
(the semidihedral action defining the type-(6) group). -/
def IsSemidihedralAction (n : ℕ)
    (φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (2 ^ n)))) : Prop :=
  ∀ u : ZMod (2 ^ n),
    φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd u) =
      Multiplicative.ofAdd ((-1 + (2 : ZMod (2 ^ n)) ^ (n - 1)) * u)

end Castro2006


