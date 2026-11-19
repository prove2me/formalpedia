-- Prove2me | Definitions.Def_PPSLattice_Supplement_BIBE
-- name    : PPSLattice_Supplement_BIBE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T07:36:28.316282+00:00
-- url     : https://prove2.me/theorems/fb4ae6d6-f1b2-49a8-9537-feb727d5faf0
-- title:
--   Selectively secure batched identity-based encryption
-- statement:
--   Batched IBE derives one set key from the digest of a set of identities and decrypts ciphertexts for identities in that set. The selective-security experiment permits set-key queries both before and after the challenge, with every queried set excluding the target identity and having cardinality at most $B$.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 6.21 and Construction 6.22, pp.55–56

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_Supplement_RPPS
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decSet
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- Batched identity-based encryption (Definition 6.21, pp.55--56). Identities are naturals;
the external predicate `Identity λ` specifies the source's identity space `I_λ`. -/
structure BIBE where
  setup : ℕ → ℕ → PMF (Str × Str)
  digest : ℕ → ℕ → Str → Finset ℕ → Str
  kgen : ℕ → ℕ → Str → Str → PMF Str
  enc : ℕ → ℕ → Str → ℕ → Bool → PMF Str
  dec : ℕ → ℕ → Str → Finset ℕ → Str → ℕ → Str → Option Bool

/-- The five batched-IBE algorithms are uniform polynomial time; the batch bound is unary at
setup, as in Definition 6.21. -/
def BIBE.Efficient (E : BIBE) : Prop :=
  PPTSampler (fun x : ℕ × ℕ => BeyondDS.tup [encNat x.1, encNat x.2])
    (fun x => (E.setup x.1 x.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PolyTimeOn (fun x : ℕ × ℕ × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1,
        BeyondDS.tup ((x.2.2.2.sort (· ≤ ·)).map encBin)])
    (fun x => E.digest x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × Str =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1, x.2.2.2])
    (fun x => E.kgen x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × ℕ × Bool =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1, encBin x.2.2.2.1,
        [x.2.2.2.2]])
    (fun x => E.enc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  PolyTimeOn (fun x : ℕ × ℕ × Str × Finset ℕ × Str × ℕ × Str =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1,
        BeyondDS.tup ((x.2.2.2.1.sort (· ≤ ·)).map encBin), x.2.2.2.2.1,
        encBin x.2.2.2.2.2.1, x.2.2.2.2.2.2])
    (fun x => match E.dec x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2 with
      | none => [] | some b => [b])

def BIBE.Correct (E : BIBE) (Identity : ℕ → Set ℕ) : Prop :=
  ∃ nu : ℕ → ℝ, NoisyOWMPC.Negligible nu ∧ ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    ∀ S : Finset ℕ, (∀ i ∈ S, i ∈ Identity lam) → S.card ≤ B →
      ∀ id ∈ S, ∀ mu : Bool,
        1 - nu lam ≤ (((E.setup lam B).bind fun z =>
          (E.kgen lam B z.2 (E.digest lam B z.1 S)).bind fun sk =>
            (E.enc lam B z.1 id mu).map fun ct =>
              decide (E.dec lam B z.1 S sk id ct = some mu)) true).toReal

def BIBE.Compact (E : BIBE) : Prop :=
  ∃ c : ℕ, ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → ∀ z ∈ (E.setup lam B).support,
    (∀ S : Finset ℕ, S.card ≤ B → ∀ sk ∈ (E.kgen lam B z.2 (E.digest lam B z.1 S)).support,
      sk.length ≤ (lam + Nat.clog 2 B + 2) ^ c) ∧
    ∀ id mu ct, ct ∈ (E.enc lam B z.1 id mu).support →
      ct.length ≤ (lam + Nat.clog 2 B + 2) ^ c

inductive BIBEMove
  | key (S : Finset ℕ)
  | challenge (mu0 mu1 : Bool)
  | guess (b : Bool)

def decBIBEMove (w : Str) : BIBEMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => .key (decSet (fs.getD 1 []))
  | [false, true] => .challenge ((fs.getD 1 []).headD false) ((fs.getD 2 []).headD false)
  | _ => .guess ((fs.getD 1 []).headD false)

open Classical in
noncomputable def bibePost (E : BIBE) (Identity : ℕ → Set ℕ)
    (A : RestrictedDec.Adversary) (lam B idstar : ℕ) (mpk msk : Str) (b : Bool) :
    ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input =>
      (A.activate lam st input).bind fun r =>
        match decBIBEMove r.2 with
        | .key S =>
            if (∀ i ∈ S, i ∈ Identity lam) ∧ S.card ≤ B ∧ idstar ∉ S then
              (E.kgen lam B msk (E.digest lam B mpk S)).bind fun sk =>
                bibePost E Identity A lam B idstar mpk msk b fuel r.1 sk
            else PMF.uniformOfFintype Bool
        | .guess b' => PMF.pure (decide (b' = b))
        | .challenge _ _ => PMF.uniformOfFintype Bool

open Classical in
noncomputable def bibePre (E : BIBE) (Identity : ℕ → Set ℕ)
    (A : RestrictedDec.Adversary) (lam B idstar : ℕ) (mpk msk : Str) :
    ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input =>
      (A.activate lam st input).bind fun r =>
        match decBIBEMove r.2 with
        | .key S =>
            if (∀ i ∈ S, i ∈ Identity lam) ∧ S.card ≤ B ∧ idstar ∉ S then
              (E.kgen lam B msk (E.digest lam B mpk S)).bind fun sk =>
                bibePre E Identity A lam B idstar mpk msk fuel r.1 sk
            else PMF.uniformOfFintype Bool
        | .challenge mu0 mu1 => (PMF.uniformOfFintype Bool).bind fun b =>
            (E.enc lam B mpk idstar (if b then mu1 else mu0)).bind fun ct =>
              bibePost E Identity A lam B idstar mpk msk b fuel r.1 ct
        | .guess _ => PMF.uniformOfFintype Bool

open Classical in
/-- Selective-security game with key queries both before and after the challenge (Definition 6.21). -/
noncomputable def bibeGame (E : BIBE) (Identity : ℕ → Set ℕ)
    (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let B := BeyondDS.decNat (fs.getD 0 [])
    let idstar := decBin (fs.getD 1 [])
    if 1 ≤ B ∧ idstar ∈ Identity lam then (E.setup lam B).bind fun z =>
      bibePre E Identity A lam B idstar z.1 z.2 (A.p.eval lam + 1) r0.1 z.1
    else PMF.uniformOfFintype Bool

def BIBE.SelectivelySecure (E : BIBE) (Identity : ℕ → Set ℕ) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((bibeGame E Identity A lam) true).toReal - 1 / 2|

/-- Definition 6.21, including `[2^λ] ⊆ I_λ`. -/
def BIBE.IsScheme (E : BIBE) (Identity : ℕ → Set ℕ) : Prop :=
  (∀ lam, (Finset.Icc 1 (2 ^ lam) : Set ℕ) ⊆ Identity lam) ∧
    E.Efficient ∧ E.Correct Identity ∧ E.Compact ∧ E.SelectivelySecure Identity

/-- Construction 6.22 for a fixed maximum batch size `B`. Its message space is one-bit strings. -/
noncomputable def construction622 (B : ℕ) (E : BIBE) : RPPS where
  setup lam _ := E.setup lam B
  pkEnc lam _ mpk i := E.enc lam B mpk i false
  kgen lam _ mpk msk S := E.kgen lam B msk (E.digest lam B mpk S)
  skEnc lam _ mpk _ i mu := E.enc lam B mpk i (mu.headD false)
  decode lam _ mpk S sk i ct :=
    if i ∈ S then (E.dec lam B mpk S sk i ct).map fun b => [b] else none

def BitMessage (lam : ℕ) : Set Str := {m | m.length = 1}

/-- Robust payload hiding restricted to KGen sets of size at most `B`, the bounded variant stated
immediately before Construction 6.22. -/
def RPPS.RobustPayloadHidingUpTo (E : RPPS) (B : ℕ) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((rppsGameUpTo E BitMessage B A lam) true).toReal - 1 / 2|

end PPSLattice.Supplement


