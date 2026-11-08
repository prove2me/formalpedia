-- Prove2me | Definitions.Def_AvoidPlast_truthTable
-- name    : AvoidPlast_truthTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:34.053036+00:00
-- url     : https://prove2.me/theorems/2dbdd039-b15e-4848-bf1c-67204d5d41c3
-- title:
--   Truth tables of $g:F^m\to F$
-- statement:
--   The truth table of $g:F^m\to F$ as a bit string: all entries, each in $\lceil\log_2|F|\rceil$ bits, so of length $|F|^m\lceil\log_2|F|\rceil$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib
import Definitions.Def_AvoidPlast_fixedBits

namespace AvoidPlast

/-- The truth table of `g : F^m → F` over `F = Fin Q` as a bit string (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.5, p.18, "`f` is
represented by a truthtable"): the entries in the order of `finFunctionFinEquiv`, each in
`⌈log₂ Q⌉` bits, so its length is `|F|^m · ⌈log₂ |F|⌉`. -/
def truthTable {Q m : ℕ} (g : (Fin m → Fin Q) → Fin Q) : List Bool :=
  (List.finRange (Q ^ m)).flatMap fun i =>
    fixedBits (Nat.clog 2 Q) (g (finFunctionFinEquiv.symm i)).val

end AvoidPlast


