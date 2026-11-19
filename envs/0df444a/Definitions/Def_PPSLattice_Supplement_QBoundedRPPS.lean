-- Prove2me | Definitions.Def_PPSLattice_Supplement_QBoundedRPPS
-- name    : PPSLattice_Supplement_QBoundedRPPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T08:25:43.40605+00:00
-- url     : https://prove2.me/theorems/09bac798-28c9-4ca0-a54d-1135e1c23ff3
-- title:
--   Q-bounded robust PPS and Construction A.5
-- statement:
--   A $Q$-bounded robust PPS exposes unary $Q$ at setup, allows at most $Q$ set-key queries, and permits ciphertext size to depend polynomially on $Q$. Construction A.5 is the explicit $QR$-instance PPS construction with independent Shamir sharing in every bucket; it has public parameters and ciphertexts linear in $Q$, compact keys, and decoder locality independent of $Q$, with $R=\lambda^2(\lambda+1)^2$, threshold $\lambda+1$, and field width $\lceil\log_2(R+1)\rceil$.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition A.1, Construction A.5, and Definition A.8, pp.66–70

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_Supplement_RPPS
import Definitions.Def_PPSLattice_Supplement_EvolvingCSS
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decSet
import Definitions.Def_PPSLattice_encSet
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- A Q-bounded robust PPS, whose setup also receives `Q` (Definition A.1, p.66). -/
structure QBoundedRPPS where
  setup : ℕ → ℕ → ℕ → PMF (Str × Str)
  pkEnc : ℕ → ℕ → ℕ → Str → ℕ → PMF Str
  kgen : ℕ → ℕ → ℕ → Str → Str → Finset ℕ → PMF Str
  skEnc : ℕ → ℕ → ℕ → Str → Str → ℕ → Str → PMF Str
  decode : ℕ → ℕ → ℕ → Str → Finset ℕ → Str → ℕ → Str → Option Str

/-- Uniform polynomial-time syntax for Q-bounded robust PPS. `N` is binary and `Q` is unary. -/
def QBoundedRPPS.Efficient (E : QBoundedRPPS) : Prop :=
  PPTSampler (fun x : ℕ × ℕ × ℕ => BeyondDS.tup [encNat x.1, encBin x.2.1, encNat x.2.2])
    (fun x => (E.setup x.1 x.2.1 x.2.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × Str × ℕ =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, encNat x.2.2.1, x.2.2.2.1,
        encBin x.2.2.2.2])
    (fun x => E.pkEnc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × Str × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, encNat x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.1, encSet x.2.2.2.2.2])
    (fun x => E.kgen x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × Str × Str × ℕ × Str =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, encNat x.2.2.1, x.2.2.2.1,
        x.2.2.2.2.1, encBin x.2.2.2.2.2.1, x.2.2.2.2.2.2])
    (fun x => E.skEnc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
      x.2.2.2.2.2.1 x.2.2.2.2.2.2) ∧
  PolyTimeOn (fun x : ℕ × ℕ × ℕ × Str × Finset ℕ × Str × ℕ × Str =>
      BeyondDS.tup [encNat x.1, encBin x.2.1, encNat x.2.2.1, x.2.2.2.1,
        encSet x.2.2.2.2.1, x.2.2.2.2.2.1, encBin x.2.2.2.2.2.2.1,
        x.2.2.2.2.2.2.2])
    (fun x => match E.decode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2 with
      | none => [] | some mu => mu)

def appendixR (lam : ℕ) : ℕ := lam ^ 2 * (lam + 1) ^ 2
def appendixH (lam : ℕ) : ℕ := Nat.clog 2 (appendixR lam + 1)
def AppendixFieldMessage (lam : ℕ) : Set Str := {m | m.length = appendixH lam}
/-- The source's canonical embeddings of field elements `0` and `1` into the `h`-bit model. -/
def appendixBit (lam : ℕ) (b : Bool) : Str :=
  (List.range (appendixH lam)).map fun j => b && decide (j = 0)

/-- PPS correctness for an arbitrary explicitly supplied string message family. -/
def PPS.CorrectFor (E : PPS) (Message : ℕ → Set Str) : Prop :=
  ∀ lam N : ℕ, 1 ≤ lam → N ≤ 2 ^ lam → ∀ S ⊆ Finset.Icc 1 N, ∀ i ∈ S,
    ∀ mu ∈ Message lam, ((E.gsetup lam N).bind fun crs => (E.mskgen lam N crs).bind fun msk =>
      (E.skEnc lam N crs msk i mu).bind fun ct => (E.kgen lam N crs msk S).map fun sk =>
        decide (E.decode lam N crs S sk i ct = some mu)) true = 1

/-- Full PPS compactness for an arbitrary message family. -/
def PPS.FullyCompactFor (E : PPS) (Message : ℕ → Set Str) : Prop :=
  ∃ c : ℕ, ∀ lam N : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    ∀ crs ∈ (E.gsetup lam N).support, crs.length ≤ (lam + Nat.clog 2 N + 2) ^ c ∧
      ∀ msk ∈ (E.mskgen lam N crs).support,
        (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N crs i).support,
          ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        (∀ i ∈ Finset.Icc 1 N, ∀ mu ∈ Message lam,
          ∀ ct ∈ (E.skEnc lam N crs msk i mu).support,
            ct.length ≤ (lam + Nat.clog 2 N + 2) ^ c) ∧
        ∀ S ⊆ Finset.Icc 1 N, ∀ sk ∈ (E.kgen lam N crs msk S).support,
          sk.length ≤ (lam + Nat.clog 2 N + 2) ^ c

def PPS.IsSchemeForPostKey (E : PPS) (Message : ℕ → Set Str) : Prop :=
  E.Efficient ∧ PPSLattice.Supplement.PPS.CorrectFor E Message ∧
    PPSLattice.Supplement.PPS.FullyCompactFor E Message ∧
    PPSLattice.Supplement.PPS.PostKeyPayloadHiding E Message

def QBoundedRPPS.Correct (E : QBoundedRPPS) (Message : ℕ → Set Str) : Prop :=
  ∃ nu : ℕ → ℝ, NoisyOWMPC.Negligible nu ∧ ∀ lam N Q : ℕ,
    1 ≤ lam → 1 ≤ Q → N ≤ 2 ^ lam →
    ∀ S ⊆ Finset.Icc 1 N, ∀ i ∈ S, ∀ mu ∈ Message lam,
      1 - nu lam ≤ (((E.setup lam N Q).bind fun z =>
        (E.kgen lam N Q z.1 z.2 S).bind fun sk =>
          (E.skEnc lam N Q z.1 z.2 i mu).map fun ct =>
            decide (E.decode lam N Q z.1 S sk i ct = some mu)) true).toReal

/-- Definition A.1 compactness: keys remain `poly(λ,log N)`, while ciphertexts may grow by an
arbitrary polynomial in the unary setup bound `Q`. Public-parameter size is not part of
Definition 6.14 compactness and is recorded separately for Construction A.5. -/
def QBoundedRPPS.Compact (E : QBoundedRPPS) (Message : ℕ → Set Str) : Prop :=
  ∃ c : ℕ, ∀ lam N Q : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam →
    1 ≤ Q → ∀ z ∈ (E.setup lam N Q).support,
      (∀ S ⊆ Finset.Icc 1 N, ∀ sk ∈ (E.kgen lam N Q z.1 z.2 S).support,
        sk.length ≤ (lam + Nat.clog 2 N + Nat.clog 2 Q + 3) ^ c) ∧
      (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N Q z.1 i).support,
        ct.length ≤ (lam + Nat.clog 2 N + Q + 3) ^ c) ∧
      ∀ i ∈ Finset.Icc 1 N, ∀ mu ∈ Message lam,
        ∀ ct ∈ (E.skEnc lam N Q z.1 z.2 i mu).support,
          ct.length ≤ (lam + Nat.clog 2 N + Q + 3) ^ c

open Classical in
/-- Bounded-adaptive-robustness interaction, counting KGen queries while allowing arbitrary
interleaving with encryption queries. -/
noncomputable def qbrppsRun (E : QBoundedRPPS) (Message : ℕ → Set Str)
    (A : RestrictedDec.Adversary) (lam N Q : ℕ) (pp msk : Str) (istar : ℕ) (b : Bool) :
    ℕ → ℕ → Str → Str → PMF Bool
  | 0, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, keyCount, st, input => (A.activate lam st input).bind fun r =>
      match decRPPSMove r.2 with
      | .enc i mu =>
          if i ∈ Finset.Icc 1 N ∧ i ≠ istar ∧ mu ∈ Message lam then
            (E.skEnc lam N Q pp msk i mu).bind fun ct =>
              qbrppsRun E Message A lam N Q pp msk istar b fuel keyCount r.1 ct
          else qbrppsRun E Message A lam N Q pp msk istar b fuel keyCount r.1 []
      | .key S =>
          if keyCount < Q ∧ S ⊆ Finset.Icc 1 N ∧ istar ∉ S then
            (E.kgen lam N Q pp msk S).bind fun sk =>
              qbrppsRun E Message A lam N Q pp msk istar b fuel (keyCount + 1) r.1 sk
          else PMF.uniformOfFintype Bool
      | .guess b' => PMF.pure (decide (b' = b))

open Classical in
/-- The adversary chooses `(N,Q,i*,μ0,μ1)` before setup; the challenge is always a secret-key
encryption of `μ_b`, as in Definition A.1. -/
noncomputable def qbrppsGame (E : QBoundedRPPS) (Message : ℕ → Set Str)
    (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let N := decBin (fs.getD 0 [])
    let Q := BeyondDS.decNat (fs.getD 1 [])
    let istar := decBin (fs.getD 2 [])
    let mu0 := fs.getD 3 []
    let mu1 := fs.getD 4 []
    if 1 ≤ Q ∧ istar ∈ Finset.Icc 1 N ∧ mu0 ∈ Message lam ∧ mu1 ∈ Message lam then
      (PMF.uniformOfFintype Bool).bind fun b => (E.setup lam N Q).bind fun z =>
        (E.skEnc lam N Q z.1 z.2 istar (if b then mu1 else mu0)).bind fun ct =>
          qbrppsRun E Message A lam N Q z.1 z.2 istar b (A.p.eval lam + 1) 0 r0.1
            (BeyondDS.tup [z.1, ct])
    else PMF.uniformOfFintype Bool

def QBoundedRPPS.BoundedAdaptiveRobust (E : QBoundedRPPS) (Message : ℕ → Set Str) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((qbrppsGame E Message A lam) true).toReal - 1 / 2|

/-- Locality of Construction A.5: Decode reads no public-parameter bits and at most a polynomial
in `(λ,log N)` ciphertext bits, independently of `Q` and `|S|`. The two natural-valued functions
are an explicit random-access cost certificate for the deterministic decoder. -/
def QBoundedRPPS.Local (readPP readCT : ℕ → ℕ → ℕ → ℕ) : Prop :=
  (∀ lam N Q, readPP lam N Q = 0) ∧
  ∃ c : ℕ, ∀ lam N Q, readCT lam N Q ≤ (lam + Nat.clog 2 N + 2) ^ c

/-- A finite-field Shamir interface at the Appendix-A parameters. Field elements are their exact
`h`-bit encodings. -/
structure ShamirFamily where
  share : ℕ → Str → PMF (List Str)
  recon : ℕ → Finset ℕ → List Str → Option Str

private def selectedShares (Gamma : Finset ℕ) (shares : List Str) : List Str :=
  (Gamma.sort (· ≤ ·)).map fun r => shares.getD (r - 1) []

/-- The correctness, perfect privacy, field-width, and polynomial-time properties of the Shamir
scheme invoked in Lemma A.2. -/
def ShamirFamily.Valid (H : ShamirFamily) : Prop :=
  PPTSampler (fun x : ℕ × Str => BeyondDS.tup [encNat x.1, x.2])
      (fun x => (H.share x.1 x.2).map BeyondDS.tup) ∧
  PolyTimeOn (fun x : ℕ × Finset ℕ × List Str =>
      BeyondDS.tup [encNat x.1, encSet x.2.1, BeyondDS.tup x.2.2])
      (fun x => (H.recon x.1 x.2.1 x.2.2).getD []) ∧
  (∀ lam mu, 1 ≤ lam → mu ∈ AppendixFieldMessage lam →
    ∀ shares ∈ (H.share lam mu).support,
      shares.length = appendixR lam ∧ ∀ y ∈ shares, y ∈ AppendixFieldMessage lam) ∧
  (∀ lam mu, 1 ≤ lam → mu ∈ AppendixFieldMessage lam →
    ∀ Gamma ⊆ Finset.Icc 1 (appendixR lam), lam + 1 ≤ Gamma.card →
      ∀ shares ∈ (H.share lam mu).support,
        H.recon lam Gamma (selectedShares Gamma shares) = some mu) ∧
  ∀ lam mu0 mu1, 1 ≤ lam → mu0 ∈ AppendixFieldMessage lam →
    mu1 ∈ AppendixFieldMessage lam → ∀ Gamma ⊆ Finset.Icc 1 (appendixR lam),
      Gamma.card < lam + 1 →
      (H.share lam mu0).map (selectedShares Gamma) =
        (H.share lam mu1).map (selectedShares Gamma)

private noncomputable def sampleN {α : Type} : (n : ℕ) → (ℕ → PMF α) → PMF (List α)
  | 0, _ => PMF.pure []
  | n + 1, D => (D 0).bind fun a =>
      (sampleN n fun j => D (j + 1)).map fun as => a :: as

private noncomputable def uniformFinsetOrDefault {α : Type} [DecidableEq α] [Inhabited α]
    (s : Finset α) : PMF α :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.pure default

private def a5At (xs : List Str) (R k r : ℕ) : Str :=
  xs.getD ((k - 1) * R + (r - 1)) []

private def sequenceOptions {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some a :: rest => (sequenceOptions rest).map fun as => a :: as

open Classical in
/-- The actual algorithms of Construction A.5. There are exactly `Q*R` independent PPS
instances; keys choose a uniform bucket and a uniform `(λ+1)`-subset, and secret-key encryption
Shamir-shares the message independently in every bucket. -/
noncomputable def constructionA5 (E : PPS) (H : ShamirFamily) : QBoundedRPPS where
  setup lam N Q :=
    (sampleN (Q * appendixR lam) fun _ =>
      (E.gsetup lam N).bind fun crs => (E.mskgen lam N crs).map fun msk => (crs, msk)).map
        fun zs => (BeyondDS.tup (zs.map Prod.fst), BeyondDS.tup (zs.map Prod.snd))
  pkEnc lam N Q pp i :=
    let crss := BeyondDS.untup pp
    (sampleN (Q * appendixR lam) fun j => E.pkEnc lam N (crss.getD j []) i).map BeyondDS.tup
  kgen lam N Q pp mskCode S :=
    let R := appendixR lam
    let crss := BeyondDS.untup pp
    let msks := BeyondDS.untup mskCode
    (uniformFinsetOrDefault (Finset.Icc 1 Q)).bind fun k =>
      (uniformFinsetOrDefault ((Finset.Icc 1 R).powersetCard (lam + 1))).bind fun Gamma =>
        let rs := Gamma.sort (· ≤ ·)
        (sampleN rs.length fun j =>
          let r := rs.getD j 0
          let crs := a5At crss R k r
          (E.kgen lam N crs (a5At msks R k r) S).map fun sk => BeyondDS.tup [crs, sk]).map
            fun pairs => BeyondDS.tup [encBin k, encSet Gamma, BeyondDS.tup pairs]
  skEnc lam N Q pp mskCode i mu :=
    let R := appendixR lam
    let crss := BeyondDS.untup pp
    let msks := BeyondDS.untup mskCode
    (sampleN Q fun k0 => (H.share lam mu).bind fun shares =>
      (sampleN R fun r0 =>
        E.skEnc lam N (a5At crss R (k0 + 1) (r0 + 1))
          (a5At msks R (k0 + 1) (r0 + 1)) i (shares.getD r0 []))).map
      fun buckets => BeyondDS.tup buckets.flatten
  decode lam N _ _ S skCode i ctCode :=
    if i ∈ S then
      let fs := BeyondDS.untup skCode
      let k := decBin (fs.getD 0 [])
      let Gamma := decSet (fs.getD 1 [])
      let pairs := BeyondDS.untup (fs.getD 2 [])
      let cts := BeyondDS.untup ctCode
      let R := appendixR lam
      let ys := (Gamma.sort (· ≤ ·)).mapIdx fun j r =>
        let pair := BeyondDS.untup (pairs.getD j [])
        E.decode lam N (pair.getD 0 []) S (pair.getD 1 []) i (a5At cts R k r)
      (sequenceOptions ys).bind fun shares => H.recon lam Gamma shares
    else none

/-- The exact linear public-parameter and ciphertext bounds proved for Construction A.5. -/
def QBoundedRPPS.ConstructionA5Linear (E : QBoundedRPPS)
    (Message : ℕ → Set Str) : Prop :=
  ∃ c : ℕ, ∀ lam N Q : ℕ, 1 ≤ lam → 1 ≤ N → N ≤ 2 ^ lam → 1 ≤ Q →
    ∀ z ∈ (E.setup lam N Q).support,
      z.1.length ≤ Q * (lam + Nat.clog 2 N + 2) ^ c ∧
      (∀ i ∈ Finset.Icc 1 N, ∀ ct ∈ (E.pkEnc lam N Q z.1 i).support,
        ct.length ≤ Q * (lam + Nat.clog 2 N + 2) ^ c) ∧
      ∀ i ∈ Finset.Icc 1 N, ∀ mu ∈ Message lam,
        ∀ ct ∈ (E.skEnc lam N Q z.1 z.2 i mu).support,
          ct.length ≤ Q * (lam + Nat.clog 2 N + 2) ^ c

/-- The exact Construction-A.5 object, tied definitionally to the algorithms above, together with
the correctness, compactness, linear-size, efficiency, and random-access locality conclusions
proved on pp.67--68. -/
structure ConstructionA5 (E : PPS) where
  shamir : ShamirFamily
  shamir_valid : shamir.Valid
  scheme : QBoundedRPPS
  scheme_eq : scheme = constructionA5 E shamir
  readPP : ℕ → ℕ → ℕ → ℕ
  readCT : ℕ → ℕ → ℕ → ℕ
  efficient : scheme.Efficient
  correct : PPSLattice.Supplement.QBoundedRPPS.Correct scheme AppendixFieldMessage
  compact : PPSLattice.Supplement.QBoundedRPPS.Compact scheme AppendixFieldMessage
  linear : PPSLattice.Supplement.QBoundedRPPS.ConstructionA5Linear scheme AppendixFieldMessage
  locality : PPSLattice.Supplement.QBoundedRPPS.Local readPP readCT

open Classical in
/-- Construction 6.17 instantiated with a Q-bounded RPPS, using `N=2^λ`. By Appendix-A
locality the public share is empty; `pp` is retained only in the private dealer state and in the
secret keys produced by Construction A.5. -/
noncomputable def construction617Q (E : QBoundedRPPS) : EvolvingCSS where
  setup lam Q _ s := (E.setup lam (2 ^ lam) Q).map fun z =>
    ([], BeyondDS.tup [z.1, z.2, [s], encBin Q])
  addVertex lam Q _ t st S :=
    let fs := BeyondDS.untup st
    let pp := fs.getD 0 []
    let msk := fs.getD 1 []
    let s := (fs.getD 2 []).headD false
    (E.kgen lam (2 ^ lam) Q pp msk S).bind fun sk =>
      (E.skEnc lam (2 ^ lam) Q pp msk t (appendixBit lam s)).map fun ct =>
        (BeyondDS.tup [encBin Q, sk, ct], st)
  recon lam G A _ shares :=
    if G.ContainsEdge A then
      let p := firstEdge G A
      let vf := BeyondDS.untup (shares.getD (p.2 - 1) [])
      let uf := BeyondDS.untup (shares.getD (p.1 - 1) [])
      let Q := decBin (vf.getD 0 [])
      (E.decode lam (2 ^ lam) Q [] (G.getD (p.2 - 1) ∅) (vf.getD 1 []) p.1
        (uf.getD 2 [])).map fun mu => mu.headD false
    else none

def EvolvingCSS.NoPublicShare (C : EvolvingCSS) : Prop :=
  ∀ lam Q D s z, z ∈ (C.setup lam Q D s).support → z.1 = []

/-- With collusion bound `Q` and unbounded degree, each vertex share has size
`Q·poly(λ)` (Theorem A.11). -/
def EvolvingCSS.QLinearSharesUnboundedDegree (C : EvolvingCSS) : Prop :=
  C.EfficientWithBounds encNat encBin ∧
    ∃ c : ℕ, ∀ lam Q : ℕ, 1 ≤ lam → 1 ≤ Q → ∀ s,
      ∀ z ∈ (C.setup lam Q (2 ^ lam) s).support, ∀ t st S,
        S ⊆ Finset.Icc 1 (t - 1) → ∀ out ∈ (C.addVertex lam Q (2 ^ lam) t st S).support,
          out.1.length ≤ Q * (lam + 2) ^ c

end PPSLattice.Supplement


