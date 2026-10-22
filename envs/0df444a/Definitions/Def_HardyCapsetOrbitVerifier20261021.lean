-- Prove2me | Definitions.Def_HardyCapsetOrbitVerifier20261021
-- name    : HardyCapsetOrbitVerifier20261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T16:40:21.43098+00:00
-- url     : https://prove2.me/theorems/56a127b9-71e4-4f84-8a50-73d7ed9d443d
-- title:
--   HardyCapsetOrbitVerifier20261021
-- statement:
--   Explicit packed finite orbit witnesses and Boolean coordinate checks for signed-permutation words, together with the existential OrbitCovered property. Definitions assert no coverage fact.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetSymmetryData20261020
set_option autoImplicit false
namespace HardyCapset20261020.Cert

def orbitRecord (packed k : ℕ) : CoverageRecord :=
  let n := (packed >>> (20 * k)) % 1048576
  { representative := n % 256, groupIndex := (n / 256) % 512, factor := n / 131072 }

def orbitEntryB (start packed k : ℕ) : Bool :=
  let n := start + k
  let r := orbitRecord packed k
  decide (r.representative < 246 ∧ r.groupIndex < groupWords.size ∧
    (r.factor : ZMod 3) ≠ 0 ∧
    decode (n / 3 + 1) = (r.factor : ZMod 3) •
      wordMap generators groupWords[r.groupIndex]!
        (decode (entry representativeNormals r.representative)) ∧
    ((n % 3 : ℕ) : ZMod 3) = (r.factor : ZMod 3) *
      (entry representativeLevels r.representative : ZMod 3))

def orbitBlockB (start packed len : ℕ) : Bool :=
  (List.range len).all (orbitEntryB start packed)

def OrbitCovered (n : ℕ) : Prop :=
  ∃ (r : Fin 246) (w : List ℕ) (a : ZMod 3), a ≠ 0 ∧
    decode (n / 3 + 1) = a • wordMap generators w
      (decode (entry representativeNormals r.val)) ∧
    ((n % 3 : ℕ) : ZMod 3) = a * (entry representativeLevels r.val : ZMod 3)

end HardyCapset20261020.Cert


