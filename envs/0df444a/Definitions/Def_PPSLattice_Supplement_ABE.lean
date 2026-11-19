-- Prove2me | Definitions.Def_PPSLattice_Supplement_ABE
-- name    : PPSLattice_Supplement_ABE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T08:17:18.557222+00:00
-- url     : https://prove2.me/theorems/15a82172-0daa-41bd-bf82-71e9b5f88392
-- title:
--   Selectively secure circuit ABE with succinct keys
-- statement:
--   The key-policy circuit-ABE interface has setup for an input length and depth, circuit-key generation, attribute encryption, and decryption. Perfect correctness and selective security are paired with size bounds polynomial in security parameter, input length, and depth, but independent of circuit size.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 6.25 and Construction 6.27, pp.58–59

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_Supplement_BIBE
import Definitions.Def_PPSLattice_circDepth
import Definitions.Def_PPSLattice_encvec
import Definitions.Def_PPSLattice_memCircuit
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_RestrictedDec_Circuit

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- Key-policy circuit ABE (Definition 6.25, p.58). -/
structure SuccinctABE where
  setup : ℕ → ℕ → ℕ → PMF (Str × Str)
  kgen : ℕ → ℕ → ℕ → Str → RestrictedDec.Circuit → PMF Str
  enc : ℕ → ℕ → ℕ → Str → Str → Bool → PMF Str
  dec : ℕ → ℕ → ℕ → Str → RestrictedDec.Circuit → Str → Str → Str → Option Bool

/-- The key-policy circuit-ABE syntax used in Definition 6.25. -/
abbrev ABE := SuccinctABE

/-- Uniform polynomial-time syntax for key-policy circuit ABE. The length and depth parameters
are unary, and keys are restricted to one-output Boolean circuits. -/
def SuccinctABE.Efficient (E : SuccinctABE) : Prop :=
  PPTSampler (fun x : ℕ × ℕ × ℕ => BeyondDS.tup [encNat x.1, encNat x.2.1, encNat x.2.2])
    (fun x => (E.setup x.1 x.2.1 x.2.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × Str × RestrictedDec.Circuit =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, encNat x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.code])
    (fun x => E.kgen x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × Str × Str × Bool =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, encNat x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.1, [x.2.2.2.2.2]])
    (fun x => E.enc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) ∧
  PolyTimeOn (fun x : ℕ × ℕ × ℕ × Str × RestrictedDec.Circuit × Str × Str × Str =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, encNat x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.1.code, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2])
    (fun x => match E.dec x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2 with
      | none => [] | some b => [b])

/-- Perfect ABE correctness for every accepting circuit of the declared input length and depth. -/
def SuccinctABE.Correct (E : SuccinctABE) : Prop :=
  ∀ lam ell d : ℕ, 1 ≤ lam → ∀ f : RestrictedDec.Circuit,
    circDepth ell f ≤ d → ∀ x : Str, x.length = ell → f.eval x = [true] → ∀ mu : Bool,
      ((E.setup lam ell d).bind fun z => (E.kgen lam ell d z.2 f).bind fun sk =>
        (E.enc lam ell d z.1 x mu).map fun ct =>
          decide (E.dec lam ell d z.1 f sk x ct = some mu)) true = 1

/-- Succinctness: mpk, keys, and ciphertexts are bounded by one polynomial in `(λ,ℓ,d)`;
in particular the key bound contains no circuit-size term. -/
def SuccinctABE.Succinct (E : SuccinctABE) : Prop :=
  ∃ c : ℕ, ∀ lam ell d : ℕ, ∀ z ∈ (E.setup lam ell d).support,
    z.1.length ≤ (lam + ell + d + 2) ^ c ∧
    (∀ f : RestrictedDec.Circuit, f.outs.length = 1 → circDepth ell f ≤ d →
      ∀ sk ∈ (E.kgen lam ell d z.2 f).support, sk.length ≤ (lam + ell + d + 2) ^ c) ∧
    ∀ x mu ct, ct ∈ (E.enc lam ell d z.1 x mu).support →
      ct.length ≤ (lam + ell + d + 2) ^ c

inductive ABEMove
  | key (f : RestrictedDec.Circuit)
  | challenge (mu0 mu1 : Bool)
  | guess (b : Bool)

def decABEMove (w : Str) : ABEMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => match RestrictedDec.decCircuit (fs.getD 1 []) with
      | some f => .key f | none => .guess false
  | [false, true] => .challenge ((fs.getD 1 []).headD false) ((fs.getD 2 []).headD false)
  | _ => .guess ((fs.getD 1 []).headD false)

noncomputable def abePost (E : SuccinctABE) (A : RestrictedDec.Adversary)
    (lam ell d : ℕ) (xstar mpk msk : Str) (b : Bool) : ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input => (A.activate lam st input).bind fun r =>
      match decABEMove r.2 with
      | .key f =>
          if f.outs.length = 1 ∧ circDepth ell f ≤ d ∧ f.eval xstar = [false] then
            (E.kgen lam ell d msk f).bind fun sk => abePost E A lam ell d xstar mpk msk b fuel r.1 sk
          else PMF.uniformOfFintype Bool
      | .guess b' => PMF.pure (decide (b' = b))
      | .challenge _ _ => PMF.uniformOfFintype Bool

noncomputable def abePre (E : SuccinctABE) (A : RestrictedDec.Adversary)
    (lam ell d : ℕ) (xstar mpk msk : Str) : ℕ → Str → Str → PMF Bool
  | 0, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, st, input => (A.activate lam st input).bind fun r =>
      match decABEMove r.2 with
      | .key f =>
          if f.outs.length = 1 ∧ circDepth ell f ≤ d ∧ f.eval xstar = [false] then
            (E.kgen lam ell d msk f).bind fun sk => abePre E A lam ell d xstar mpk msk fuel r.1 sk
          else PMF.uniformOfFintype Bool
      | .challenge mu0 mu1 => (PMF.uniformOfFintype Bool).bind fun b =>
          (E.enc lam ell d mpk xstar (if b then mu1 else mu0)).bind fun ct =>
            abePost E A lam ell d xstar mpk msk b fuel r.1 ct
      | .guess _ => PMF.uniformOfFintype Bool

/-- Selective ABE security with circuit-key queries before and after the challenge. -/
noncomputable def abeGame (E : SuccinctABE) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let ell := BeyondDS.decNat (fs.getD 0 [])
    let d := BeyondDS.decNat (fs.getD 1 [])
    let xstar := fs.getD 2 []
    if xstar.length = ell then (E.setup lam ell d).bind fun z =>
      abePre E A lam ell d xstar z.1 z.2 (A.p.eval lam + 1) r0.1 z.1
    else PMF.uniformOfFintype Bool

def SuccinctABE.SelectivelySecure (E : SuccinctABE) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((abeGame E A lam) true).toReal - 1 / 2|

def SuccinctABE.IsScheme (E : SuccinctABE) : Prop :=
  E.Efficient ∧ E.Correct ∧ E.Succinct ∧ E.SelectivelySecure

/-- The exact depth bound `d_{N,B}` of p.59. -/
def dNB (N B : ℕ) : ℕ := 1 + 2 * Nat.clog 2 (Nat.clog 2 N) + 2 * Nat.clog 2 B

def dNN (N : ℕ) : ℕ := dNB N N

/-- Construction 6.27: index `i` is the published `encvec N i`; a set key is an ABE key for the
published membership circuit `memCircuit N S`, under depth bound `d_{N,N}`. -/
noncomputable def construction627 (E : SuccinctABE) : RPPS where
  setup lam N := E.setup lam (Nat.clog 2 N) (dNN N)
  pkEnc lam N mpk i := E.enc lam (Nat.clog 2 N) (dNN N) mpk (encvec N i) false
  kgen lam N _ msk S := E.kgen lam (Nat.clog 2 N) (dNN N) msk (memCircuit N S)
  skEnc lam N mpk _ i mu := E.enc lam (Nat.clog 2 N) (dNN N) mpk (encvec N i) (mu.headD false)
  decode lam N mpk S sk i ct :=
    if i ∈ S then
      (E.dec lam (Nat.clog 2 N) (dNN N) mpk (memCircuit N S) sk (encvec N i) ct).map fun b => [b]
    else none

end PPSLattice.Supplement


