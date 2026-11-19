-- Prove2me | Definitions.Def_PPSLattice_Supplement_PSPRG
-- name    : PPSLattice_Supplement_PSPRG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T07:59:01.925128+00:00
-- url     : https://prove2.me/theorems/3c9867f4-c635-452a-a7f8-776b04b204dc
-- title:
--   Publicly sampleable projective pseudorandom generator
-- statement:
--   A PSPRG has polynomial-time setup, public sampling, secret projection, and indexed evaluation algorithms. Its properties require both evaluations to return the same actual bit (not two failures), projected-key compactness, sampling indistinguishability, and adaptive pseudorandomness with at most one projection query and the final condition $I\cap T=\varnothing$.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 6.1 and Construction 6.2, pp.43–45

import Mathlib
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decSet
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- A publicly sampleable projective pseudorandom generator (PSPRG), Definition 6.1, pp.43--44
of Goyal--Yadugiri (manuscript sha256 7f9c493f...). -/
structure PSPRG where
  setup : ℕ → ℕ → PMF (Str × Str)
  samp : ℕ → ℕ → Str → Finset ℕ → PMF Str
  project : ℕ → ℕ → Str → Str → Finset ℕ → PMF Str
  eval : ℕ → ℕ → Str → Finset ℕ → Str → ℕ → Option Bool

/-- The four PSPRG algorithms are uniform polynomial time; `ell` is encoded in unary, as in
Definition 6.1. -/
def PSPRG.Efficient (G : PSPRG) : Prop :=
  PPTSampler (fun x : ℕ × ℕ => BeyondDS.tup [encNat x.1, encNat x.2])
    (fun x => (G.setup x.1 x.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1,
        BeyondDS.tup ((x.2.2.2.sort (· ≤ ·)).map encBin)])
    (fun x => G.samp x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
  PPTSampler (fun x : ℕ × ℕ × Str × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1, x.2.2.2.1,
        BeyondDS.tup ((x.2.2.2.2.sort (· ≤ ·)).map encBin)])
    (fun x => G.project x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∧
  PolyTimeOn (fun x : ℕ × ℕ × Str × Finset ℕ × Str × ℕ =>
      BeyondDS.tup [encNat x.1, encNat x.2.1, x.2.2.1,
        BeyondDS.tup ((x.2.2.2.1.sort (· ≤ ·)).map encBin), x.2.2.2.2.1,
        encBin x.2.2.2.2.2])
    (fun x => match G.eval x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 with
      | none => [] | some b => [b])

/-- Perfect consistency of a projected key with the full projected key (Definition 6.1). -/
def PSPRG.Correct (G : PSPRG) : Prop :=
  ∀ lam ell : ℕ, 1 ≤ lam → 1 ≤ ell → ∀ S ⊆ Finset.Icc 1 ell, ∀ i ∈ S,
    (G.setup lam ell).bind (fun z =>
      (G.project lam ell z.1 z.2 (Finset.Icc 1 ell)).bind fun skAll =>
        (G.project lam ell z.1 z.2 S).map fun sk =>
          decide ((G.eval lam ell z.1 (Finset.Icc 1 ell) skAll i = some false ∧
              G.eval lam ell z.1 S sk i = some false) ∨
            (G.eval lam ell z.1 (Finset.Icc 1 ell) skAll i = some true ∧
              G.eval lam ell z.1 S sk i = some true))) true = 1

/-- Projected-key compactness `poly(λ, log ℓ_out)`, uniformly on every output support. -/
def PSPRG.Compact (G : PSPRG) : Prop :=
  ∃ c : ℕ, ∀ lam ell : ℕ, 1 ≤ lam → 1 ≤ ell →
    ∀ z ∈ (G.setup lam ell).support, ∀ S ⊆ Finset.Icc 1 ell,
      (∀ sk ∈ (G.samp lam ell z.1 S).support, sk.length ≤ (lam + Nat.clog 2 ell + 2) ^ c) ∧
      ∀ sk ∈ (G.project lam ell z.1 z.2 S).support,
        sk.length ≤ (lam + Nat.clog 2 ell + 2) ^ c

/-- Moves in the adaptive PSPRG experiment. -/
inductive PSPRGMove
  | project (S : Finset ℕ)
  | eval (i : ℕ)
  | guess (b : Bool)

/-- `00,S`; `01,i`; or a final guess. -/
def decPSPRGMove (w : Str) : PSPRGMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => .project (decSet (fs.getD 1 []))
  | [false, true] => .eval (decBin (fs.getD 1 []))
  | _ => .guess ((fs.getD 1 []).headD false)

/-- Sampling indistinguishability: `Samp(S)` and `Project(msk,S)` cannot be distinguished for an
adaptively chosen admissible `S` (Definition 6.1, p.44). -/
noncomputable def psprgSamplingGame (G : PSPRG) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let ell := BeyondDS.decNat r0.2
    (G.setup lam ell).bind fun z =>
      (A.activate lam r0.1 z.1).bind fun r1 =>
        let S := decSet r1.2
        if S ⊆ Finset.Icc 1 ell then
          (PMF.uniformOfFintype Bool).bind fun b =>
            (if b then G.project lam ell z.1 z.2 S else G.samp lam ell z.1 S).bind fun sk =>
              (A.activate lam r1.1 sk).map fun r2 =>
                match decPSPRGMove r2.2 with | .guess b' => decide (b' = b) | _ => false
        else PMF.uniformOfFintype Bool

/-- Recursive adaptive-pseudorandomness interaction. At most one Project query is accepted;
admissibility `I ∩ T = ∅` is checked only when the adversary guesses, exactly as printed. -/
noncomputable def psprgAdaptiveRun (G : PSPRG) (A : RestrictedDec.Adversary) (lam ell : ℕ)
    (pp msk skAll y : Str) : ℕ → Bool → Finset ℕ → Finset ℕ → Str → Str → PMF Bool
  | 0, _, _, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, projected, I, T, st, input =>
      (A.activate lam st input).bind fun r =>
        match decPSPRGMove r.2 with
        | .project S =>
            if !projected ∧ S ⊆ Finset.Icc 1 ell then
              (G.project lam ell pp msk S).bind fun sk =>
                psprgAdaptiveRun G A lam ell pp msk skAll y fuel true I (T ∪ S) r.1 sk
            else PMF.uniformOfFintype Bool
        | .eval i =>
            if i ∈ Finset.Icc 1 ell then
              let honest := (G.eval lam ell pp (Finset.Icc 1 ell) skAll i).getD false
              let random := y.getD i false
              psprgAdaptiveRun G A lam ell pp msk skAll y fuel projected (insert i I) T r.1
                [if y.headD false then random else honest]
            else psprgAdaptiveRun G A lam ell pp msk skAll y fuel projected I T r.1 []
        | .guess b' =>
            if Disjoint I T then PMF.pure (decide (b' = y.headD false))
            else PMF.uniformOfFintype Bool

/-- Adaptive pseudorandomness game. The first bit of `y` stores the challenge bit and the remaining
`ell` bits are the independent random output vector. -/
noncomputable def psprgAdaptiveGame (G : PSPRG) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let ell := BeyondDS.decNat r0.2
    (G.setup lam ell).bind fun z =>
      (G.project lam ell z.1 z.2 (Finset.Icc 1 ell)).bind fun skAll =>
        (PMF.uniformOfFintype Bool).bind fun b =>
          (AvgPHETH.uniformDist ell).bind fun bits =>
            psprgAdaptiveRun G A lam ell z.1 z.2 skAll (b :: bits) (A.p.eval lam + 1)
              false ∅ ∅ r0.1 z.1

def PSPRG.SamplingIndistinguishable (G : PSPRG) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((psprgSamplingGame G A lam) true).toReal - 1 / 2|

def PSPRG.AdaptivelyPseudorandom (G : PSPRG) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((psprgAdaptiveGame G A lam) true).toReal - 1 / 2|

/-- The complete PSPRG interface of Definition 6.1. -/
def PSPRG.IsScheme (G : PSPRG) : Prop :=
  G.Efficient ∧ G.Correct ∧ G.Compact ∧ G.SamplingIndistinguishable ∧ G.AdaptivelyPseudorandom

/-- Construction 6.2 from a bit-message PPS (p.45). The public parameters are the PPS CRS and
one encryption of an independent random bit per output position. -/
noncomputable def construction62 (E : PPS) : PSPRG where
  setup lam ell :=
    (E.gsetup lam ell).bind fun crs => (E.mskgen lam ell crs).bind fun msk =>
      (List.range ell).foldr
        (fun j acc => (PMF.uniformOfFintype Bool).bind fun b =>
          (E.skEnc lam ell crs msk (j + 1) [b]).bind fun ct => acc.map fun cts => ct :: cts)
        (PMF.pure []) |>.map fun cts => (BeyondDS.tup (crs :: cts), BeyondDS.tup [crs, msk])
  samp lam ell pp S :=
    let fs := BeyondDS.untup pp
    let crs := fs.getD 0 []
    (E.mskgen lam ell crs).bind fun msk => E.kgen lam ell crs msk S
  project lam ell pp mskCode S :=
    let fs := BeyondDS.untup mskCode
    E.kgen lam ell (fs.getD 0 []) (fs.getD 1 []) S
  eval lam ell pp S sk i :=
    if i ∈ S then
      let fs := BeyondDS.untup pp
      (E.decode lam ell (fs.getD 0 []) S sk i (fs.getD i [])).bind List.head?
    else none

end PPSLattice.Supplement


