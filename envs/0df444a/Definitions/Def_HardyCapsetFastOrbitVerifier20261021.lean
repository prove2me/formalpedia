-- Prove2me | Definitions.Def_HardyCapsetFastOrbitVerifier20261021
-- name    : HardyCapsetFastOrbitVerifier20261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T16:58:18.482755+00:00
-- url     : https://prove2.me/theorems/a69a18a2-accb-4b52-a18d-4a6e591322d0
-- title:
--   HardyCapsetFastOrbitVerifier20261021
-- statement:
--   Natural-number evaluation of the nine explicit signed permutations and their words, with exact finite orbit witness checks. No coverage fact is assumed.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetOrbitVerifier20261021
set_option autoImplicit false
namespace HardyCapset20261020.Cert
abbrev NatPoint := Fin 8 -> Nat
def natPermutations : Fin 9 -> Fin 8 -> Nat := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 5, 4, 3, 6, 7], ![0, 2, 1, 3, 4, 5, 7, 6], ![0, 6, 7, 3, 4, 5, 1, 2], ![4, 1, 6, 3, 0, 5, 2, 7]]
def natSigns : Fin 9 -> Fin 8 -> Nat := ![![1, 1, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 1, 2, 1, 1], ![1, 1, 2, 1, 1, 1, 2, 1], ![1, 2, 1, 1, 1, 1, 1, 2], ![2, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]]
def natGen (i : Nat) (v : NatPoint) (j : Fin 8) : Nat :=
  if hi : i < 9 then
    (natSigns (Fin.mk i hi) j * v (Fin.mk (natPermutations (Fin.mk i hi) j % 8) (Nat.mod_lt _ (by decide)))) % 3
  else v j
def natWord : List Nat -> NatPoint -> NatPoint
  | [], v => v
  | i :: rest, v => natGen i (natWord rest v)
def rawDigits (q : Nat) : NatPoint := fun j => digit q j.val
def castPoint (v : NatPoint) : Point := fun j => (v j : ZMod 3)
def fastOrbitEntryB (start packed k : Nat) : Bool :=
  let n := start+k
  let r := orbitRecord packed k
  decide (r.representative < 246) && decide (r.groupIndex < groupWords.size) &&
    (r.factor == 1 || r.factor == 2) &&
    (List.range 8).all (fun j =>
      digit (n/3+1) j == (r.factor * natWord groupWords[r.groupIndex]!
        (rawDigits (entry representativeNormals r.representative)) (Fin.mk (j%8) (Nat.mod_lt _ (by decide)))) % 3) &&
    (n % 3 == (r.factor * entry representativeLevels r.representative) % 3)
def fastOrbitBlockB (start packed len : Nat) : Bool :=
  (List.range len).all (fastOrbitEntryB start packed)
end HardyCapset20261020.Cert


