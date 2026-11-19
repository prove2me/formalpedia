-- Prove2me | Definitions.Def_PPSLattice_Supplement_PPSBit
-- name    : PPSLattice_Supplement_PPSBit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T07:43:46.055527+00:00
-- url     : https://prove2.me/theorems/e235d9fa-a3a7-4160-bfb4-466ff7f860d1
-- title:
--   Bit-message programmable pseudorandom set sampler
-- statement:
--   A bit-message PPS is the published PPS interface specialized to the message space $\{0,1\}$, with efficiency, perfect correctness, full compactness, mode indistinguishability, and payload hiding retained.
--
--   **Formalization Note** A bit is encoded as a one-element Boolean string; all target-set and query admissibility checks are those of Definition 4.1.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1 and the bit-message specializations in Constructions 5.3 and 6.2, pp.19, 33, 45

import Mathlib
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_PPS_Correct
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_PPS_FullyCompact
import Definitions.Def_PPSLattice_Supplement_BIBE
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decPMove
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- Perfect PPS correctness when the message family is `{0,1}` rather than `{0,1}^λ`. -/
def PPS.BitCorrect (E : PPS) : Prop :=
  ∀ lam N : ℕ, 1 ≤ lam → N ≤ 2 ^ lam → ∀ S ⊆ Finset.Icc 1 N, ∀ i ∈ S, ∀ mu : Bool,
    ((E.gsetup lam N).bind fun crs => (E.mskgen lam N crs).bind fun msk =>
      (E.skEnc lam N crs msk i [mu]).bind fun ct => (E.kgen lam N crs msk S).map fun sk =>
        decide (E.decode lam N crs S sk i ct = some [mu])) true = 1

/-- Full compactness for a bit-message PPS. -/
def PPS.BitFullyCompact (E : PPS) : Prop :=
  ∃ c : ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    ∀ crs ∈ (E.gsetup lam N).support, crs.length ≤ (lam + Nat.clog 2 N + 2) ^ c ∧
      ∀ msk ∈ (E.mskgen lam N crs).support,
        msk.length ≤ (lam + Nat.clog 2 N + 2) ^ c ∧
        (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N crs i).support,
          ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        (∀ i ∈ Finset.Icc 1 N, ∀ mu : Bool, ∀ ct ∈ (E.skEnc lam N crs msk i [mu]).support,
          ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        ∀ S ⊆ Finset.Icc 1 N, ∀ sk ∈ (E.kgen lam N crs msk S).support,
          sk.length ≤ (lam + Nat.clog 2 N + 2) ^ c

noncomputable def ppsBitRun (E : PPS) (A : RestrictedDec.Adversary) (lam N : ℕ) (crs msk : Str)
    (istar : ℕ) (payload b : Bool) : ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input => (A.activate lam st input).bind fun r =>
      match decPMove r.2 with
      | .query i mu =>
          if i ∈ Finset.Icc 1 N ∧ i ≠ istar ∧ mu.length = 1 then
            (E.skEnc lam N crs msk i mu).bind fun ct =>
              ppsBitRun E A lam N crs msk istar payload b fuel r.1 ct
          else ppsBitRun E A lam N crs msk istar payload b fuel r.1 []
      | .setS S =>
          if S ⊆ Finset.Icc 1 N ∧ ((payload ∧ istar ∉ S) ∨ (!payload ∧ istar ∈ S)) then
            (E.kgen lam N crs msk S).bind fun sk =>
              match fuel with
              | 0 => PMF.uniformOfFintype Bool
              | _ + 1 => (A.activate lam r.1 sk).map fun q =>
                  match decPMove q.2 with | .guess b' => decide (b' = b) | _ => false
          else PMF.uniformOfFintype Bool
      | .guess _ => PMF.uniformOfFintype Bool

/-- Bit-message PPS mode (`payload=false`) and payload (`payload=true`) games. -/
noncomputable def ppsBitGame (payload : Bool) (E : PPS) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let istar := decBin (fs.getD 1 [])
    let muA := (fs.getD 2 []).headD false
    if istar ∈ Finset.Icc 1 N then (PMF.uniformOfFintype Bool).bind fun b =>
      (E.gsetup lam N).bind fun crs => (E.mskgen lam N crs).bind fun msk =>
        (if b then
          (if payload then PMF.pure muA else PMF.uniformOfFintype Bool).bind fun mu =>
            E.skEnc lam N crs msk istar [mu]
         else E.pkEnc lam N crs istar).bind fun ct =>
          ppsBitRun E A lam N crs msk istar payload b (A.p.eval lam + 1) r0.1
            (BeyondDS.tup [crs, ct])
    else PMF.uniformOfFintype Bool

def PPS.BitModeInd (E : PPS) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((ppsBitGame false E A lam) true).toReal - 1 / 2|

def PPS.BitPayloadHiding (E : PPS) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((ppsBitGame true E A lam) true).toReal - 1 / 2|

def PPS.IsBitScheme (E : PPS) : Prop :=
  E.Efficient ∧ PPSLattice.Supplement.PPS.BitCorrect E ∧
    PPSLattice.Supplement.PPS.BitFullyCompact E ∧
    PPSLattice.Supplement.PPS.BitModeInd E ∧
    PPSLattice.Supplement.PPS.BitPayloadHiding E

/-- The bit-message PPS interface used by Constructions 5.3 and 6.2. -/
def PPSBit (E : PPS) : Prop := PPSLattice.Supplement.PPS.IsBitScheme E

end PPSLattice.Supplement


