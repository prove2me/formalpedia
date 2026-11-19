-- Prove2me | Definitions.Def_PPSLattice_Supplement_RPPS
-- name    : PPSLattice_Supplement_RPPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T07:30:01.861966+00:00
-- url     : https://prove2.me/theorems/662fc125-a026-4d2c-bd99-c48cfbb28310
-- title:
--   Robust programmable pseudorandom set sampler
-- statement:
--   A robust PPS returns public parameters and a master key and supports public-key encryption, set-key generation, secret-key encryption, and decoding. Correctness may have negligible error; robust payload hiding permits arbitrarily interleaved encryption and set-key queries, all excluding the challenge index.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 6.14 and Remark 6.15, pp.50–51

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_decPMove
import Definitions.Def_PPSLattice_decSet
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- A robust programmable pseudorandom set sampler for a string message family. Setup returns
public parameters and the master secret key together; every algorithm receives the public
parameters explicitly. Goyal--Yadugiri, Definition 6.14, pp.50--51. -/
structure RPPS where
  setup : ℕ → ℕ → PMF (Str × Str)
  pkEnc : ℕ → ℕ → Str → ℕ → PMF Str
  kgen : ℕ → ℕ → Str → Str → Finset ℕ → PMF Str
  skEnc : ℕ → ℕ → Str → Str → ℕ → Str → PMF Str
  decode : ℕ → ℕ → Str → Finset ℕ → Str → ℕ → Str → Option Str

/-- All five RPPS algorithms are uniform polynomial-time algorithms. -/
def RPPS.Efficient (E : RPPS) : Prop :=
  PPTSampler (fun x : ℕ × ℕ => BeyondDS.tup [encNat x.1, encBin x.2])
    (fun x => (E.setup x.1 x.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × ℕ =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, x.2.2.1, encBin x.2.2.2])
    (fun x => E.pkEnc x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, x.2.2.1, x.2.2.2.1,
        BeyondDS.tup ((x.2.2.2.2.sort (· ≤ ·)).map encBin)])
    (fun x => E.kgen x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × Str × ℕ × Str =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, x.2.2.1, x.2.2.2.1,
        encBin x.2.2.2.2.1, x.2.2.2.2.2])
    (fun x => E.skEnc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
  ∧ PolyTimeOn (fun x : ℕ × ℕ × Str × Finset ℕ × Str × ℕ × Str =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, x.2.2.1,
        BeyondDS.tup ((x.2.2.2.1.sort (· ≤ ·)).map encBin), x.2.2.2.2.1,
        encBin x.2.2.2.2.2.1, x.2.2.2.2.2.2])
    (fun x => match E.decode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2 with
      | none => [] | some mu => mu)

/-- Negligible-error correctness of Definition 6.14, for every `N ≤ 2^λ`. -/
def RPPS.Correct (E : RPPS) (Message : ℕ → Set Str) : Prop :=
  ∃ nu : ℕ → ℝ, NoisyOWMPC.Negligible nu ∧ ∀ lam N : ℕ, 1 ≤ lam → N ≤ 2 ^ lam →
    ∀ S ⊆ Finset.Icc 1 N, ∀ i ∈ S, ∀ mu ∈ Message lam,
      1 - nu lam ≤ (((E.setup lam N).bind fun z =>
        (E.kgen lam N z.1 z.2 S).bind fun sk =>
          (E.skEnc lam N z.1 z.2 i mu).map fun ct =>
            decide (E.decode lam N z.1 S sk i ct = some mu)) true).toReal

/-- Key and ciphertext compactness, independent of `|S|` (Definition 6.14). -/
def RPPS.Compact (E : RPPS) (Message : ℕ → Set Str) : Prop :=
  ∃ c : ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    ∀ z ∈ (E.setup lam N).support,
      (∀ S ⊆ Finset.Icc 1 N, ∀ sk ∈ (E.kgen lam N z.1 z.2 S).support,
        sk.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
      (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N z.1 i).support,
        ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
      ∀ i ∈ Finset.Icc 1 N, ∀ mu ∈ Message lam,
        ∀ ct ∈ (E.skEnc lam N z.1 z.2 i mu).support,
          ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c

/-- Robust-PPS adversarial moves; key and encryption queries may occur in any order. -/
inductive RPPSMove
  | enc (i : ℕ) (mu : Str)
  | key (S : Finset ℕ)
  | guess (b : Bool)

def decRPPSMove (w : Str) : RPPSMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => .enc (decBin (fs.getD 1 [])) (fs.getD 2 [])
  | [false, true] => .key (decSet (fs.getD 1 []))
  | _ => .guess ((fs.getD 1 []).headD false)

open Classical in
/-- The interleaved robust-payload-hiding interaction. Every encryption query excludes `i*` and
every key set excludes it; there is no query-count or phase restriction. -/
noncomputable def rppsRun (E : RPPS) (Message : ℕ → Set Str) (A : RestrictedDec.Adversary)
    (lam N : ℕ) (pp msk : Str) (istar : ℕ) (b : Bool) (maxKey : Option ℕ) :
    ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input =>
      (A.activate lam st input).bind fun r =>
        match decRPPSMove r.2 with
        | .enc i mu =>
            if i ∈ Finset.Icc 1 N ∧ i ≠ istar ∧ mu ∈ Message lam then
              (E.skEnc lam N pp msk i mu).bind fun ct =>
                rppsRun E Message A lam N pp msk istar b maxKey fuel r.1 ct
            else rppsRun E Message A lam N pp msk istar b maxKey fuel r.1 []
        | .key S =>
            if S ⊆ Finset.Icc 1 N ∧ istar ∉ S ∧ (maxKey.elim True fun B => S.card ≤ B) then
              (E.kgen lam N pp msk S).bind fun sk =>
                rppsRun E Message A lam N pp msk istar b maxKey fuel r.1 sk
            else PMF.uniformOfFintype Bool
        | .guess b' => PMF.pure (decide (b' = b))

open Classical in
/-- Robust payload hiding, Definition 6.14. The adversary chooses `(N,i*,μ*)` before setup. -/
noncomputable def rppsGame (E : RPPS) (Message : ℕ → Set Str)
    (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let istar := decBin (fs.getD 1 [])
    let mu := fs.getD 2 []
    if istar ∈ Finset.Icc 1 N ∧ mu ∈ Message lam then
      (PMF.uniformOfFintype Bool).bind fun b => (E.setup lam N).bind fun z =>
        (if b then E.skEnc lam N z.1 z.2 istar mu else E.pkEnc lam N z.1 istar).bind fun ct =>
          rppsRun E Message A lam N z.1 z.2 istar b none (A.p.eval lam + 1) r0.1
            (BeyondDS.tup [z.1, ct])
    else PMF.uniformOfFintype Bool

open Classical in
/-- The bounded-set variant of the robust game: every queried key set additionally has cardinality
at most `B` (the variant preceding Construction 6.22, p.56). -/
noncomputable def rppsGameUpTo (E : RPPS) (Message : ℕ → Set Str) (B : ℕ)
    (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let istar := decBin (fs.getD 1 [])
    let mu := fs.getD 2 []
    if istar ∈ Finset.Icc 1 N ∧ mu ∈ Message lam then
      (PMF.uniformOfFintype Bool).bind fun b => (E.setup lam N).bind fun z =>
        (if b then E.skEnc lam N z.1 z.2 istar mu else E.pkEnc lam N z.1 istar).bind fun ct =>
          rppsRun E Message A lam N z.1 z.2 istar b (some B) (A.p.eval lam + 1) r0.1
            (BeyondDS.tup [z.1, ct])
    else PMF.uniformOfFintype Bool

def RPPS.RobustPayloadHiding (E : RPPS) (Message : ℕ → Set Str) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((rppsGame E Message A lam) true).toReal - 1 / 2|

def RPPS.IsScheme (E : RPPS) (Message : ℕ → Set Str) : Prop :=
  E.Efficient ∧ E.Correct Message ∧ E.Compact Message ∧ E.RobustPayloadHiding Message

open Classical in
/-- PPS payload hiding with the ciphertext oracle still available after the one set key is
returned (Remark 6.15, p.51). -/
noncomputable def ppsPostKeyRun (E : PPS) (Message : ℕ → Set Str) (A : RestrictedDec.Adversary) (lam N : ℕ)
    (crs msk : Str) (istar : ℕ) (b : Bool) : ℕ → Bool → Str → Str → PMF Bool
  | 0, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, keyed, st, input =>
      (A.activate lam st input).bind fun r =>
        match decPMove r.2 with
        | .query i mu =>
            if i ∈ Finset.Icc 1 N ∧ i ≠ istar ∧ mu ∈ Message lam then
              (E.skEnc lam N crs msk i mu).bind fun ct =>
                ppsPostKeyRun E Message A lam N crs msk istar b fuel keyed r.1 ct
            else ppsPostKeyRun E Message A lam N crs msk istar b fuel keyed r.1 []
        | .setS S =>
            if !keyed ∧ S ⊆ Finset.Icc 1 N ∧ istar ∉ S then
              (E.kgen lam N crs msk S).bind fun sk =>
                ppsPostKeyRun E Message A lam N crs msk istar b fuel true r.1 sk
            else PMF.uniformOfFintype Bool
        | .guess b' => if keyed then PMF.pure (decide (b' = b)) else PMF.uniformOfFintype Bool

open Classical in
noncomputable def ppsPostKeyGame (E : PPS) (Message : ℕ → Set Str)
    (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let istar := decBin (fs.getD 1 [])
    let mu := fs.getD 2 []
    if istar ∈ Finset.Icc 1 N ∧ mu ∈ Message lam then
      (PMF.uniformOfFintype Bool).bind fun b => (E.gsetup lam N).bind fun crs =>
        (E.mskgen lam N crs).bind fun msk =>
          (if b then E.skEnc lam N crs msk istar mu else E.pkEnc lam N crs istar).bind fun ct =>
            ppsPostKeyRun E Message A lam N crs msk istar b (A.p.eval lam + 1) false r0.1
              (BeyondDS.tup [crs, ct])
    else PMF.uniformOfFintype Bool

def PPS.PostKeyPayloadHiding (E : PPS) (Message : ℕ → Set Str) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((ppsPostKeyGame E Message A lam) true).toReal - 1 / 2|

end PPSLattice.Supplement


