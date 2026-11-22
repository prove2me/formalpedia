-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_Losses5OfLossHypD
-- name    : Formalism_SizeWindowBrackets_Losses5OfLossHypD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:11.838866+00:00
-- url     : https://prove2.me/theorems/947ce874-6c4f-446c-93a3-723f4041667e
-- title:
--   Losses5 Of Loss Hyp D
-- statement:
--   Definitions and structural lemmas for Losses5 Of Loss Hyp D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/Losses5OfLossHypD.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain7
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}
abbrev PlAllD (Fm : ∀ u0, Fam (W u0) m) : Type := Σ u0 : H, slopeLatticeData.FinPl (Fm u0).K
def plEmbD (Fm : ∀ u0, Fam (W u0) m) (u0 : H) : slopeLatticeData.FinPl (Fm u0).K ↪ PlAllD Fm :=
  Function.Embedding.sigmaMk (β := fun u0 => slopeLatticeData.FinPl (Fm u0).K) u0
def ldOfD (D : ArithData H) (N : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m) (u0 : H) :
    PrimeWindowSizeBounds.LD (PlAllD Fm) (Fin m) H where
  W := (Fm u0).S.map (plEmbD Fm u0)
  below := fun z => prBelow z.2
  l := fun z => lE z.2
  cl := (Lp u0).cl
  TTp := (Lp u0).TTp
  Iex := fun _ _ p => (Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))
  at_ := a
  wz := fun j t p i => w u0 j (partner t (i • D.frob p))
  Id := fun _ _ => Finset.Icc 1 N
  wd := fun j t i => w u0 j (partner t (gD D i))
  gainW := fun j z => (Fm z.1).gain j z.2
  tauW := fun z => (Fm z.1).tauR z.2
  gain := (Lp u0).gainP
  tau := (Lp u0).tauP
  lo := (Lp u0).lo
  fl := (Lp u0).fl
  L₁ := (Lp u0).L₁
def LdIdentD : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m) (u0 : H),
    (ldOfD D N a w Fm Lp u0).ASK D.d (inertPs D N) Finset.univ TT
      = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j) ∧
    (ldOfD D N a w Fm Lp u0).Ga Finset.univ = (Fm u0).Ga
def LossHypD (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ) : Prop :=
  P.x = G.x ∧ P.ε = G.ε ∧ P.k = G.k ∧ P.d = D.d ∧ P.Cord = Cord ∧
  SmallOrderPrimeLosses.WindowsD P eW KW ∧
  SmallOrderPrimeLosses.PrimeClassLossHypotheses P (inertPs D N) cand PR (Finset.univ : Finset (Fin m)) TT BAD Sig
    (fun u0 p => (Fm u0).iop p) (ldOfD D N a w Fm Lp) ∧
  (∀ u0, (∀ p ∈ (Fm u0).Pr, p ∉ cand → (Fm u0).iop p = 0) ∧ ∀ p ∈ cand, 0 ≤ (Fm u0).iop p) ∧
  3 * P.C + 13 ≤ C.cLoss ∧ 0 ≤ C.eLoss
variable [∀ u0, Fintype (W u0)]
def LossesOfD : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ),
    LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW → 1 ≤ G.x →
    SmallOrderPrimeLosses.ExcessAndPrimeLogSumUnitBounds P (inertPs D N) cand (Finset.univ : Finset (Fin m)) TT (fun u0 p => (Fm u0).iop p)
      (ldOfD D N a w Fm Lp) →
    LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
end Loss
def Losses5OfLossHypD : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
      (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
      (TT T2 : Finset H) (a : H → ℝ)
      (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
      (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ),
      G.ε = ε → x₁ ≤ G.x → LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW →
      LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C
def Chain6Core7 (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂
def Core7ToCore2 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ c' : ℝ, 0 < c' → HostAn c' → ∀ ε A K cHH eK eW KW : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x →
      Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x → Chain2Core eD eL K cHH eK CL ε x
def Chain6_7 : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At7 : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def Chain6_7Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At7Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
section Comp
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}
def LossHypDOfEmpty : Prop :=
  ∀ (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → Unit → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (BAD : ℕ → H → Prop) (Sig : ℕ → Unit → ℝ) (Cord eW KW : ℝ), 0 ≤ G.x →
    LossHyp (W := fun _ => W) D G C N TT (fun _ : Unit => a) (fun _ => w) (fun _ => Fm) Lp P (fun _ => 1) ∅ ∅ BAD Sig
      Cord eW KW →
    LossHypD D G C N TT a w Fm (fun u0 => Lp u0 ()) P ∅ ∅ BAD (fun p => Sig p ()) Cord eW KW
end Comp
def LossCompletionD : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H), HostFacts D →
    ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (G : Glob) (C : Consts) (cT : ℝ) (T : H → ℕ)
    (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ),
    CompletionSigns G C cT m → LChain2.LevelWindow G C w T → TopAtLevel D ell G C N TT T2 a w T →
    LossSide D G C N TT a w P Cord eW KW →
    ∃ (Mw : ℕ) (Fm : H → Fam (Fin Mw) m) (Lp : H → LossP H m),
      0 < Mw ∧ (Mw : ℝ) < G.x ^ C.cHH + 1 ∧ (∀ u0 u, (Fm u0).T u = T u0) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧
      LossHypD (W := fun _ => Fin Mw) D G C N TT a w Fm Lp P ∅ ∅ (fun _ _ => False) (fun _ => 0) Cord eW KW
section Clr
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}
def LossHypDClr : Prop :=
  ∀ (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW β s₀ : ℝ),
    LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW ↔
      LossHypD D G C N TT a w Fm Lp { P with β := β, s₀ := s₀ } cand PR BAD Sig Cord eW KW
end Clr
def Chain6Core7' (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    (∀ u0, Fam6.GainIn (Fc u0).toFam (inertPs (hostData e q d) N) (Lp u0).cl (TT.card : ℝ) (aTx x ε)) ∧
    Inputs6d' (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂
def Core7'ToCore7 : Prop :=
  ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ, ∀ A Cord eD eL K cHH eK CL x : ℝ, x₁ ≤ x →
    Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x
def Chain6_7' : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At7' : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def Chain6_7'Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain6At7'Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)
def Chain6Core7OfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 2 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core7 A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x
def Chain6Core7'OfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 3 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core7' A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x
end Formalism.LFunctionChainParameters.LChain7


