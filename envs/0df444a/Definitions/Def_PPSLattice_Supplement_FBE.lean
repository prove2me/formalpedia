-- Prove2me | Definitions.Def_PPSLattice_Supplement_FBE
-- name    : PPSLattice_Supplement_FBE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:25:55.785376+00:00
-- url     : https://prove2.me/theorems/3ee1bd4f-f12e-4165-9e74-fede57c98721
-- title:
--   Flexible broadcast encryption and its security games
-- statement:
--   A flexible broadcast-encryption scheme supplies global setup, per-handle key generation, encryption to an ordered list of public keys, and decryption by a recipient handle. This interface includes the paper's perfect correctness, compactness, uniform-PPT efficiency, semi-static game, and fully adaptive handle/corruption game.
--
--   **Formalization Note** Handles are one-based natural numbers. Game transcripts are explicit finite reactive-machine interactions; an exhausted or inadmissible run returns an independent fair bit.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definitions 5.1–5.2, pp.32–33

import Mathlib
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity Filter Polynomial
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- A flexible broadcast-encryption scheme: public setup, independent user-key generation,
encryption to an ordered list of public keys, and decryption with a one-based position and its
secret key.  Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
Definition 5.1, pp.32--33.

**Formalization Note.** Common strings, public and secret keys, ciphertexts, and messages are bit
strings. Randomized algorithms are their exact `PMF` laws. The message bit is a `Bool`; `none`
is the source's failure symbol. -/
structure FBE where
  gsetup : ℕ → PMF Str
  kgen : ℕ → Str → PMF (Str × Str)
  enc : ℕ → Str → List Str → Bool → PMF Str
  dec : ℕ → Str → List Str → ℕ → Str → Str → Option Bool

/-- The algorithms in an FBE syntax are uniform polynomial time (Definition 5.1, p.32). -/
def FBE.Efficient (E : FBE) : Prop :=
  PPTSampler (fun lam => encNat lam) E.gsetup ∧
  PPTSampler (fun x : ℕ × Str => BeyondDS.tup [encNat x.1, x.2])
    (fun x => (E.kgen x.1 x.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × Str × List Str × Bool =>
      BeyondDS.tup [encNat x.1, x.2.1, BeyondDS.tup x.2.2.1, [x.2.2.2]])
    (fun x => E.enc x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  PolyTimeOn (fun x : ℕ × Str × List Str × ℕ × Str × Str =>
      BeyondDS.tup [encNat x.1, x.2.1, BeyondDS.tup x.2.2.1, encBin x.2.2.2.1,
        x.2.2.2.2.1, x.2.2.2.2.2])
    (fun x => match E.dec x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 with
      | none => [] | some b => [b])

/-- Perfect correctness from Definition 5.1: every recipient position decrypts every honestly
generated ciphertext with probability one. -/
def FBE.Correct (E : FBE) : Prop :=
  ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → ∀ i ∈ Finset.Icc 1 N, ∀ mu : Bool,
    (E.gsetup lam).bind (fun crs =>
      (List.range N).foldr
        (fun _ acc => (E.kgen lam crs).bind fun z => acc.map fun zs => z :: zs)
        (PMF.pure []) |>.bind fun zs =>
          (E.enc lam crs (zs.map Prod.fst) mu).map fun ct =>
            decide (E.dec lam crs (zs.map Prod.fst) i (zs.getD (i - 1) ([], [])).2 ct = some mu))
      true = 1

/-- A natural-valued function is sublinear: `a(N)/N → 0`. -/
def Sublinear (a : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (nhds 0)

/-- FBE ciphertext compactness, `|ct| = o(N) poly(λ, log N)`, uniformly on the support of
honest encryption (Definition 5.1, p.32). -/
def FBE.Compact (E : FBE) : Prop :=
  ∃ a : ℕ → ℕ, Sublinear a ∧ ∃ c : ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    ∀ crs ∈ (E.gsetup lam).support, ∀ zs ∈
      ((List.range N).foldr
        (fun _ acc => (E.kgen lam crs).bind fun z => acc.map fun ys => z :: ys)
        (PMF.pure [])).support,
      ∀ mu : Bool, ∀ ct ∈ (E.enc lam crs (zs.map Prod.fst) mu).support,
        ct.length ≤ a N * (lam + Nat.clog 2 N + 2) ^ c

/-- Moves in the handle-based FBE security experiment (Definitions 5.1--5.2). -/
inductive FBEMove
  | gen
  | corrupt (h : ℕ)
  | challenge (handles : List ℕ)
  | guess (b : Bool)

/-- Canonical parser: tags `00,01,10,11` denote generation, corruption, challenge, and guess;
numbers are binary and a challenge list is a tuple of binary handles. -/
def decFBEMove (w : Str) : FBEMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => .gen
  | [false, true] => .corrupt (decBin (fs.getD 1 []))
  | [true, false] => .challenge
      (((BeyondDS.untup (fs.getD 1 [])).map decBin).toFinset.sort (· ≤ ·))
  | _ => .guess ((fs.getD 1 []).headD false)

private def lookupKey (K : List (ℕ × Str × Str)) (h : ℕ) : Option (Str × Str) :=
  (K.find? fun z => z.1 = h).map fun z => (z.2.1, z.2.2)

/-- The FBE game run. Handles begin at one. Corruption removes a handle; the challenge list must
contain only currently uncorrupted handles. In the semi-static game corruption is disallowed.
Malformed or inadmissible runs score an independent fair guess. -/
noncomputable def fbeRun (adaptive : Bool) (E : FBE) (A : RestrictedDec.Adversary)
    (lam : ℕ) (crs : Str) : ℕ → ℕ → List (ℕ × Str × Str) → Str → Str → PMF Bool
  | 0, _, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, ctr, K, st, input =>
      (A.activate lam st input).bind fun r =>
        match decFBEMove r.2 with
        | .gen => (E.kgen lam crs).bind fun z =>
            fbeRun adaptive E A lam crs fuel (ctr + 1) (K ++ [(ctr, z.1, z.2)]) r.1
              (BeyondDS.tup [encBin ctr, z.1])
        | .corrupt h =>
            if adaptive then
              match lookupKey K h with
              | none => fbeRun adaptive E A lam crs fuel ctr K r.1 []
              | some z => fbeRun adaptive E A lam crs fuel ctr (K.filter fun q => q.1 ≠ h) r.1 z.2
            else PMF.uniformOfFintype Bool
        | .challenge hs =>
            let oks := hs.map (lookupKey K)
            if hs ≠ [] ∧ hs.Pairwise (fun x y => x ≠ y) ∧ ∀ z ∈ oks, z.isSome then
              let pks := oks.map (fun z => z.getD ([], []) |>.1)
              (PMF.uniformOfFintype Bool).bind fun b =>
                (E.enc lam crs pks b).bind fun ct =>
                  match fuel with
                  | 0 => PMF.uniformOfFintype Bool
                  | _ + 1 => (A.activate lam r.1 ct).map fun q =>
                      match decFBEMove q.2 with | .guess b' => decide (b' = b) | _ => false
            else PMF.uniformOfFintype Bool
        | .guess _ => PMF.uniformOfFintype Bool

/-- The adaptive (`true`) or semi-static (`false`) FBE experiment. -/
noncomputable def fbeGame (adaptive : Bool) (E : FBE) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (E.gsetup lam).bind fun crs => fbeRun adaptive E A lam crs (A.p.eval lam + 1) 1 [] [] crs

/-- Semi-static security is correctness, compactness, algorithmic efficiency, and negligible
distinguishing advantage when corruption queries are unavailable (Definition 5.2, p.33). -/
def FBE.SemiStaticSecure (E : FBE) : Prop :=
  E.Efficient ∧ E.Correct ∧ E.Compact ∧ ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((fbeGame false E A lam) true).toReal - 1 / 2|

/-- Adaptive FBE security, including the correctness and compactness clauses of Definition 5.1. -/
def FBE.AdaptivelySecure (E : FBE) : Prop :=
  E.Efficient ∧ E.Correct ∧ E.Compact ∧ ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((fbeGame true E A lam) true).toReal - 1 / 2|

/-- Construction 5.3's exact parameter accounting. `crs`, `pk`, `sk`, `ct`, and `ppsSk` are the
respective component lengths; the four equations are the display and following sentence on p.34.
The construction therefore doubles each SSFBE object at most and adds a polynomial in `λ`. -/
def FBE.Construction53Overhead
    (fbeCrs fbePk fbeSk fbeCt ppsCrs ppsCt ppsSk outCrs outPk outSk outCt : ℕ → ℕ → ℕ) : Prop :=
  (∀ lam N, outCt lam N = 2 * fbeCt lam N + ppsSk lam N) ∧
  (∀ lam N, outCrs lam N = fbeCrs lam N + ppsCrs lam N) ∧
  (∀ lam N, outPk lam N = 2 * fbePk lam N + lam + ppsCt lam N) ∧
  (∀ lam N, outSk lam N = 1 + fbeSk lam N)

end PPSLattice.Supplement


