-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
-- name    : Formalism_SizeWindowBrackets_SBrDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:01:03.175065+00:00
-- url     : https://prove2.me/theorems/6db084c6-1102-45c6-923a-f6381dd3ded3
-- title:
--   SBr Div
-- statement:
--   Definitions and structural lemmas for SBr Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SBrDiv.lean

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
section Defs1
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
def DivFree (D : Data U0 W Top m f) (C : Consts) (logOm : ℝ) : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
def Per (D : Data U0 W Top m f) (logOm : ℝ) : Prop :=
  logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL
def PerLe (D : Data U0 W Top m f) (logOm : ℝ) : Prop :=
  D.gam + Real.log (Real.pi / D.v) - D.LpL ≤ logOm
def CountFree (D : Data U0 W Top m f) (C : Consts) (logOm : ℝ) : Prop :=
  ∀ u0 (u : W u0),
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, (Real.log (D.w u0 j ρ) + (D.gam - D.LpL - logOm)))
        + (m : ℝ) * D.lg - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)
def CountRest (D : Data U0 W Top m f) (C : Consts) : Prop :=
  ∀ u0 (u : W u0), Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k
def withV (D : Data U0 W Top m f) (v : ℝ) : Data U0 W Top m f := { D with v := v }
end Defs1
def PerMean {Pl Emb : Type} [Fintype Emb] (logOmτ : Pl → Emb → ℝ) (logOm : ℝ) : Prop :=
  ∀ ρ, (∑ s, logOmτ ρ s) / (Fintype.card Emb : ℝ) = logOm
def PerText {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) {Pl Emb : Type} [Fintype Emb]
    (logOmτ : Pl → Emb → ℝ) : Prop :=
  ∀ ρ, (∑ s, logOmτ ρ s) / (Fintype.card Emb : ℝ) = D.gam + Real.log (Real.pi / D.v) - D.LpL
def PerOfText : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) (D : Data U0 W Top m f) (Pl Emb : Type) [Fintype Emb]
    [Nonempty Pl] (logOmτ : Pl → Emb → ℝ) (logOm : ℝ), PerText D logOmτ →
    (PerMean logOmτ logOm → Per D logOm) ∧ PerMean logOmτ D.logOm
def DivIffFree : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts),
    D.DIV C ↔ DivFree D C D.logOm
def DivOfFree : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm : ℝ), DivFree D C logOm → Per D logOm → D.DIV C
def DivOfFreeLe : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm : ℝ), (∀ t, 0 ≤ D.aT t) → DivFree D C logOm → PerLe D logOm → D.DIV C
def DivMainShift : Prop :=
  ∀ (Top : Type) [Fintype Top] (m : ℝ) (aT : Top → ℝ) (logT Om Om' : ℝ),
    (∑ t, (m * (ph (aT t) - aT t * Om') - aT t * logT))
      = (∑ t, (m * (ph (aT t) - aT t * Om) - aT t * logT)) - m * (∑ t, aT t) * (Om' - Om)
def DivFreeShift : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm logOm' : ℝ), DivFree D C logOm ↔
      ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
        (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm') - D.aT t * Real.log (D.T u0 u)))
          + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
          + (m : ℝ) * D.sumA * (logOm' - logOm)
def OmSizeOfPer : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) (D : Data U0 W Top m f) (logOm A B : ℝ),
    Per D logOm → |D.gam| ≤ 1 → |Real.log (Real.pi / D.v)| ≤ A → |D.LpL| ≤ B → 1 + A + B ≤ D.La →
    |logOm| ≤ D.La
def PerIffV : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) (D : Data U0 W Top m f) (logOm : ℝ), 0 < D.v →
    (Per D logOm ↔ D.v = Real.pi * Real.exp (D.gam - D.LpL - logOm))
def PerSolvable : Prop :=
  ∀ gam LpL logOm : ℝ, ∃ v : ℝ, 0 < v ∧ logOm = gam + Real.log (Real.pi / v) - LpL
def CountFreeOfCount : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm : ℝ), 0 < D.v → (∀ u0 j ρ, 0 < D.w u0 j ρ) → Per D logOm →
    (CountFree D C logOm ↔ ∀ u0 (u : W u0),
      (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u))
def VElim : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts),
    (∀ u0 j ρ, 0 < D.w u0 j ρ) →
    ((∃ v : ℝ, 0 < v ∧ (withV D v).DIV C ∧ Count5 (withV D v) C) ↔
      ∃ logOm : ℝ, DivFree D C logOm ∧ CountFree D C logOm ∧ CountRest D C)
def ThmDiv : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)

    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 : ℝ)

    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 1 ≤ dC →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def ThmConcl {Pl : Type} (TT : Finset Pl) (aT : Pl → ℝ)
    (muC hu Fo logT logOm m a La B0 Nc xe C0 : ℝ) : Prop :=
  muC + hu - 2 * Fo ≤
    ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
    (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def DivOfConcl : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm C0 : ℝ) (Pl : Type) (e : Top ↪ Pl) (aP : Pl → ℝ) (FoP : U0 → ℝ),
    (∀ t, aP (e t) = D.aT t) → (∀ u0, D.Fo u0 = 2 * FoP u0) →
    50 * C0 + 10 ≤ C.cDiv → 0 ≤ D.a → 0 ≤ D.La → 0 ≤ D.B0 + D.Nc → 0 ≤ D.x →
    (∀ u0 (u : W u0), ThmConcl (Finset.univ.map e) aP (D.muCC u0) (D.h u0 u) (FoP u0)
      (Real.log (D.T u0 u)) logOm (m : ℝ) D.a D.La D.B0 D.Nc (D.x ^ (C.eDiv * D.ε)) C0) →
    DivFree D C logOm
structure StepNums (J Pl : Type) where

  mu0 : ℝ

  FoP : ℝ

  hP : ℝ

  mlam : ℝ

  hK : J → ℝ

  phν : J → Pl → ℝ

  nν : J → Pl → ℝ

  fa : J → Pl → ℝ
  Lpass : ℝ
  Eb : ℝ
  e6 : ℝ
  eP : ℝ
  eK : J → ℝ

  pq : J → ℝ

  w : J → Pl → ℝ
  eE : J → Pl → ℝ
  δ : J → Pl → ℝ
structure ParNums where

  rd : ℝ

  f : ℝ
  N : ℝ
  S : ℝ
  tt : ℝ
  η : ℝ
  w'' : ℝ
  dC : ℝ
  lam0 : ℝ
  C0 : ℝ
section Defs2
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
def ParHyp (D : Data U0 W Top m f) (P : ParNums) (logOm xe nPl : ℝ) : Prop :=
  1 ≤ D.x ∧ 0 < D.ε ∧ D.L = D.x ^ D.ε ∧ D.b = Real.exp D.L ∧ D.a = D.x * D.b ∧
  1 ≤ P.rd ∧ Real.log P.rd ≤ D.L ∧ Real.log D.x ≤ D.L ∧ D.La = Real.log (D.a * P.rd) ∧
  D.B0 = P.f * (m : ℝ) * D.b * D.x ^ D.ε ∧ 0 ≤ D.Nc ∧ D.x ^ D.ε ≤ xe ∧
  nPl ≤ P.f ∧ 1 ≤ (m : ℝ) ∧ 1 ≤ P.f ∧
  1 ≤ D.k ∧ 1 ≤ P.N ∧ 0 ≤ P.S ∧ 0 ≤ P.tt ∧ 0 ≤ P.η ∧ 1 ≤ P.dC ∧
  |logOm| ≤ D.La ∧
  P.lam0 ≤ D.b ∧ P.N ^ 2 * P.dC ≤ D.b ∧ (m : ℝ) ^ 3 * P.N ^ 2 * D.L ≤ D.b ∧
  (m : ℝ) * P.η * P.N * D.L ≤ D.b ∧ D.k * P.N ≤ D.b ∧
  D.k * P.S ≤ P.w'' ∧ (m : ℝ) * (P.tt + 1) * P.η ≤ P.w'' ∧ P.N * P.w'' ≤ D.b ∧ D.b' * P.N ≤ D.a ∧
  (m : ℝ) * D.k * D.b' ≤ D.a ∧ 0 ≤ P.C0
def StepHyp (D : Data U0 W Top m f) (P : ParNums) (logOm xe : ℝ) {Pl : Type} [Fintype Pl] (TT : Finset Pl)
    [DecidablePred (· ∈ TT)] (aP : Pl → ℝ) (u0 : U0) (u : W u0) (St : StepNums (Fin m) Pl) : Prop :=
  D.muCC u0 ≤ St.mu0 + St.Lpass ∧
  St.mu0 ≤ (∑ j, ∑ ρ, St.pq j * St.w j ρ * logOm) + 2 * St.FoP + St.Eb ∧
  D.h u0 u = St.hP + (∑ j, St.hK j) - St.mlam ∧
  (∀ j, St.hK j ≤ (∑ ρ, (St.phν j ρ - St.nν j ρ * logOm)) + St.eK j) ∧
  (∑ j, ∑ ρ, St.fa j ρ) - St.e6 ≤ St.mlam ∧
  St.hP ≤ -(∑ t ∈ TT, aP t * Real.log (D.T u0 u)) + St.eP ∧
  (∀ j ρ, St.phν j ρ - St.fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aP ρ) else 0) + St.eE j ρ) ∧
  (∀ j ρ, St.nν j ρ = (if ρ ∈ TT then aP ρ else 0) + D.k * St.w j ρ + St.δ j ρ) ∧
  (∀ j ρ, 0 ≤ St.w j ρ ∧ St.w j ρ ≤ 2 * D.b) ∧
  (∀ j, |St.pq j - D.k| ≤ (m : ℝ)) ∧
  St.Lpass ≤ 1 + P.C0 * P.lam0 ∧
  St.Eb ≤ P.C0 * (m : ℝ) * xe * (D.B0 + D.Nc) ∧
  (∀ j, St.eK j ≤ P.C0 * (P.f * P.N ^ 2 * (D.La + P.dC) + P.f * (m : ℝ) ^ 3 * P.N ^ 2 * D.L)) ∧
  St.e6 ≤ P.C0 * (m : ℝ) * P.f * P.N ^ 2 * D.La ∧
  St.eP ≤ P.C0 * ((TT.card : ℝ) * D.b' * P.N + P.f * ((m : ℝ) * P.η + P.S) * P.N + P.f * P.N ^ 2) * D.La ∧
  (∀ j ρ, St.eE j ρ ≤ P.C0 * (St.w j ρ + P.S + P.N ^ 2 + (m : ℝ) * (P.tt + 1) * P.η) * D.La) ∧
  (∀ j ρ, |St.δ j ρ| ≤
    P.C0 * (St.w j ρ + D.k * (P.N + P.S) + (m : ℝ) * (P.tt + 1) * P.η + (if ρ ∈ TT then D.k * D.b' else 0)))
end Defs2
def DivOfThm : Prop :=
  ThmDiv →
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (P : ParNums) (logOm : ℝ) (Pl : Type) [Fintype Pl] (e : Top ↪ Pl)
    [DecidablePred (· ∈ (Finset.univ.map e : Finset Pl))] (aP : Pl → ℝ)
    (St : ∀ u0, W u0 → StepNums (Fin m) Pl),
    (∀ t, aP (e t) = D.aT t) → (∀ u0 (u : W u0), D.Fo u0 = 2 * (St u0 u).FoP) →
    C.cDiv = 50 * P.C0 + 10 →
    ParHyp D P logOm (D.x ^ (C.eDiv * D.ε)) (Fintype.card Pl : ℝ) →
    (∀ u0 (u : W u0), StepHyp D P logOm (D.x ^ (C.eDiv * D.ε)) (Finset.univ.map e) aP u0 u (St u0 u)) →
    DivFree D C logOm
def XeOfEDiv : Prop :=
  ∀ x ε eDiv : ℝ, 1 ≤ x → 0 < ε → 1 ≤ eDiv → x ^ ε ≤ x ^ (eDiv * ε)
def MkParDefs : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m),
    (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε ∧
    (mkData G cHH D ell N TT T2 a w Fm).b = Real.exp (mkData G cHH D ell N TT T2 a w Fm).L ∧
    (mkData G cHH D ell N TT T2 a w Fm).a = G.x * (mkData G cHH D ell N TT T2 a w Fm).b ∧
    (mkData G cHH D ell N TT T2 a w Fm).B0
      = (2 * (Fintype.card H : ℝ)) * (m : ℝ) * (mkData G cHH D ell N TT T2 a w Fm).b * G.x ^ G.ε ∧
    ((PhiSet (H := H)).card : ℝ) = 2 * (Fintype.card H : ℝ) ∧
    (0 ≤ G.x → 0 ≤ G.k → 0 ≤ (mkData G cHH D ell N TT T2 a w Fm).Nc) ∧
    (mkData G cHH D ell N TT T2 a w Fm).nT = (TT.card : ℝ)
def TypePrimeCostDeviationBound {J Pl : Type} [Fintype J] (TT : Finset Pl) (aT : Pl → ℝ) (sE : J → ℝ) (lg m B0 C0 : ℝ) : Prop :=
  (∀ j, |2 * sE j - (∑ t ∈ TT, aT t) * lg| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
  |2 * (∑ j, sE j) - m * ((∑ t ∈ TT, aT t) * lg)| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)
def TypePrimeCostOfDeviationBound : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (C0 : ℝ) (Pl : Type) (e : Top ↪ Pl) (aP : Pl → ℝ) (sE : ∀ u0, W u0 → Fin m → ℝ),
    (∀ t, aP (e t) = D.aT t) → (∀ u0 (u : W u0) j, D.EeJ u0 u j = 2 * sE u0 u j) →
    9 * C0 ^ 2 + 6 * C0 + 20 ≤ C.cE → 0 ≤ D.B0 →
    (∀ u0 (u : W u0), TypePrimeCostDeviationBound (Finset.univ.map e) aP (sE u0 u) D.lg (m : ℝ) D.B0 C0) →
    D.EComp C ∧ EComp5 D C
def CorrectedHeightVariationBound {U Pl : Type} (TT : Finset Pl) (hu logT : U → ℝ) (aT : U → Pl → ℝ) (a La B0 m C0 : ℝ) : Prop :=
  ∀ u u', |(hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u')| ≤
    (7 * C0 ^ 2 + 18) * ((TT.card : ℝ) * a * La + m * B0)
def HeightVariationOfCorrectedHeightBound : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (C0 : ℝ) (Pl : Type) (e : Top ↪ Pl) (aP : Pl → ℝ),
    (∀ t, aP (e t) = D.aT t) → 7 * C0 ^ 2 + 18 ≤ C.cH → 0 ≤ D.a → 0 ≤ D.La → 0 ≤ D.B0 →
    (∀ u0, CorrectedHeightVariationBound (Finset.univ.map e) (D.h u0) (fun u => Real.log (D.T u0 u)) (fun _ => aP)
      D.a D.La D.B0 (m : ℝ) C0) →
    D.HComp C
section Defs3
variable {U0 : Type} {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} {m f : ℕ}
def FunBound (D : Data U0 W Top m f) (C : Consts) (muMaxRR : U0 → ℝ) : Prop :=
  ∀ u0, muMaxRR u0 + D.s u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b
def RowDuality (D : Data U0 W Top m f) (muMaxRR : U0 → ℝ) : Prop :=
  ∀ u0, -muMaxRR u0 ≤ D.muMinCC u0
def shiftRows (D : Data U0 W Top m f) (c : U0 → ℝ) : Data U0 W Top m f :=
  { D with
    muCC := fun u0 => D.muCC u0 + c u0
    muMinCC := fun u0 => D.muMinCC u0 + c u0
    h := fun u0 u => D.h u0 u - c u0 }
end Defs3
def HHOfFun : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) [∀ u0, Fintype (W u0)] (Top : Type) (m f : ℕ) (D : Data U0 W Top m f)
    (C : Consts) (muMaxRR : U0 → ℝ), FunBound D C muMaxRR → RowDuality D muMaxRR → D.HHBound C
def FunOfParts : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) [∀ u0, Fintype (W u0)] (Top : Type) (m f : ℕ) (D : Data U0 W Top m f)
    (C : Consts) (muMaxRR c : U0 → ℝ) (p1 p2 : ℝ), 0 < D.x → 0 < D.b →
    (∀ u0, muMaxRR u0 + c u0 ≤ p1 * D.b) → (∀ u0, D.s u0 - c u0 ≤ p2 * D.b) → p1 + p2 ≤ D.x ^ C.cHH →
    (∀ u0, D.HH u0 = D.x ^ C.cHH * D.b) → FunBound D C muMaxRR
def ScaleFree : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) [∀ u0, Fintype (W u0)] (Top : Type) [Fintype Top] (m f : ℕ)
    (D : Data U0 W Top m f) (C : Consts) (c : U0 → ℝ) (logOm : ℝ), (∀ u0 (u : W u0), 0 < D.d u0 u) →
    (∀ u0, Nonempty (W u0)) →
    (DivFree (shiftRows D c) C logOm ↔ DivFree D C logOm) ∧ ((shiftRows D c).DIV C ↔ D.DIV C) ∧
    ((shiftRows D c).HComp C ↔ D.HComp C) ∧ ((shiftRows D c).HHBound C ↔ D.HHBound C) ∧
    (∀ u0, (shiftRows D c).s u0 = D.s u0 + c u0)
section Defs4
variable {K : Type} [Field K] [NumberField K]
def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)
def lcv [StarRing K] {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L)
def plOf (w : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩
end Defs4
def DualSlopes : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      muDef b.dualBasis (dualFrame X) (dualLat A) = -muDef b X A ∧
      muMinDef b.dualBasis (dualFrame X) (dualLat A) = -muMaxDef b X A ∧
      muMaxDef b.dualBasis (dualFrame X) (dualLat A) = -muMinDef b X A
def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      muDef (Pi.basisFun K (Fin D)) X R = -(lcv X R / D)
def RowsAreDual {I : Type} {m : ℕ} (F : Fam I m) {D : ℕ} (XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ)
    (R : Submodule (𝓞 F.K) (Fin D → F.K)) (ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd) : Prop :=
  Function.Injective ψ ∧
  (∀ v x, Formalism.HermitianLatticesTheory.normAt F.b' F.X' v (ψ x)
    = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) v x) ∧
  F.cc = (dualLat R).map (ψ.restrictScalars (𝓞 F.K))
def MuCCOfRows : Prop :=
  ∀ (I : Type) (m : ℕ) (F : Fam I m) (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace F.K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) → (∀ v, IsUnit (F.X' v).det) →
    ∀ R : Submodule (𝓞 F.K) (Fin D → F.K), Submodule.IsLattice F.K R →
    ∀ ψ : Module.Dual F.K (Fin D → F.K) →ₗ[F.K] F.Wd, RowsAreDual F XE R ψ →
      muDef F.b' F.X' F.cc = lcv XE R / D ∧
      muMinDef F.b' F.X' F.cc = -muMaxDef (Pi.basisFun F.K (Fin D)) XE R
def SumOverPlaces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Finset (slopeLatticeData.FinPl K)) (φ : slopeLatticeData.FinPl K → ℝ),
    (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0).Finite ∧
    ∑ w ∈ S, lE w * φ w
      = ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)
def FoOfPlaces : Prop :=
  ∀ (I : Type) (m : ℕ) (F : Fam I m),
    F.Fo = 2 * ∑ j, ∑ᶠ w : HeightOneSpectrum (𝓞 F.K),
      lw w * (if plOf w ∈ F.S then ramE (plOf w) * F.Fj j (plOf w) else 0)
def EeJOfPlaces : Prop :=
  ∀ (I : Type) (m : ℕ) (F : Fam I m) (u : I) (j : Fin m),
    F.EeJ u j = 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 F.K),
      lw w * (if plOf w ∈ F.S then ramE (plOf w) * F.Ej u j (plOf w) else 0)
def PerMk {H : Type} [AddCommGroup H] (G : Glob) (ell : AddChar (E0 × H) ℂ → ℂ) (logOm : ℝ) : Prop :=
  logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / G.v) - (ell chC).re
def MkDivOfFree : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (logOm : ℝ),
    DivFree (mkData G C.cHH D ell N TT T2 a w Fm) C logOm → PerMk G ell logOm →
    (mkData G C.cHH D ell N TT T2 a w Fm).DIV C
def DivFreeIsDivAt : Prop :=
  ∀ (U0 : Type) (W : U0 → Type) (Top : Type) [Fintype Top] (m f : ℕ) (D : Data U0 W Top m f) (C : Consts)
    (logOm : ℝ), DivFree D C logOm ↔ DivAt D C logOm
def PerMkOfHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (G : Glob) (logOm : ℝ), G.v = hostV e q d →
    (PerHost e q d logOm ↔ PerMk G (hostEll e q d) logOm)
def topEmb (H : Type) [AddCommGroup H] : H ↪ E0 × H := ⟨topPl, fun _ _ h => congrArg Prod.snd h⟩
def MkDivOfConcl : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (logOm C0 : ℝ)
    (Dd : H → ℕ) (XE : ∀ u0, InfinitePlace (Fm u0).K → Matrix (Fin (Dd u0)) (Fin (Dd u0)) ℂ)
    (R : ∀ u0, Submodule (𝓞 (Fm u0).K) (Fin (Dd u0) → (Fm u0).K))
    (ψ : ∀ u0, Module.Dual (Fm u0).K (Fin (Dd u0) → (Fm u0).K) →ₗ[(Fm u0).K] (Fm u0).Wd),
    (∀ u0, 0 < Dd u0) → (∀ u0 v, IsUnit (XE u0 v).det) → (∀ u0 v, IsUnit ((Fm u0).X' v).det) →
    (∀ u0, Submodule.IsLattice (Fm u0).K (R u0)) → (∀ u0, RowsAreDual (Fm u0) (XE u0) (R u0) (ψ u0)) →
    50 * C0 + 10 ≤ C.cDiv → 0 ≤ G.x → 0 ≤ G.k → 0 ≤ G.La →
    (∀ u0 (u : W u0), ThmConcl (TT.map (topEmb H)) (fun ρ => a ρ.2)
      (lcv (XE u0) (R u0) / (Dd u0 : ℝ)) ((Fm u0).h u)
      (∑ j, ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Fj j (plOf z) else 0))
      (Real.log ((Fm u0).T u : ℝ)) logOm (m : ℝ) (G.x * Real.exp (G.x ^ G.ε)) G.La
      ((2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (G.x ^ G.ε) * G.x ^ G.ε)
      (mkData G C.cHH D ell N TT T2 a w Fm).Nc (G.x ^ (C.eDiv * G.ε)) C0) →
    DivFree (mkData G C.cHH D ell N TT T2 a w Fm) C logOm
def TypePrimeCostOfDeviationBoundArith : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (C0 : ℝ) (g : Fin 2 → ℕ),
    G.lg = Real.log ((g 0 : ℝ) * (g 1 : ℝ)) → 9 * C0 ^ 2 + 6 * C0 + 20 ≤ C.cE → 0 ≤ G.x →
    (∀ u0 (u : W u0), TypePrimeCostDeviationBound (TT.map (topEmb H)) (fun ρ => a ρ.2)
      (fun j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u j (plOf z) else 0))
      (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) (m : ℝ)
      ((2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (G.x ^ G.ε) * G.x ^ G.ε) C0) →
    (mkData G C.cHH D ell N TT T2 a w Fm).EComp C ∧ EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C
def HeightVariationOfCorrectedHeightBoundArith : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (C0 : ℝ),
    7 * C0 ^ 2 + 18 ≤ C.cH → 0 ≤ G.x → 0 ≤ G.La →
    (∀ u0, CorrectedHeightVariationBound (TT.map (topEmb H)) (Fm u0).h (fun u => Real.log ((Fm u0).T u : ℝ)) (fun _ ρ => a ρ.2)
      (G.x * Real.exp (G.x ^ G.ε)) G.La
      ((2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (G.x ^ G.ε) * G.x ^ G.ε) (m : ℝ) C0) →
    (mkData G C.cHH D ell N TT T2 a w Fm).HComp C
def MkHHOfFun : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (Dd : H → ℕ) (XE : ∀ u0, InfinitePlace (Fm u0).K → Matrix (Fin (Dd u0)) (Fin (Dd u0)) ℂ)
    (R : ∀ u0, Submodule (𝓞 (Fm u0).K) (Fin (Dd u0) → (Fm u0).K))
    (ψ : ∀ u0, Module.Dual (Fm u0).K (Fin (Dd u0) → (Fm u0).K) →ₗ[(Fm u0).K] (Fm u0).Wd),
    (∀ u0, 0 < Dd u0) → (∀ u0 v, IsUnit (XE u0 v).det) → (∀ u0 v, IsUnit ((Fm u0).X' v).det) →
    (∀ u0, Submodule.IsLattice (Fm u0).K (R u0)) → (∀ u0, RowsAreDual (Fm u0) (XE u0) (R u0) (ψ u0)) →
    (∀ u0, muMaxDef (Pi.basisFun (Fm u0).K (Fin (Dd u0))) (XE u0) (R u0)
      + (mkData G C.cHH D ell N TT T2 a w Fm).s u0 ≤ G.x ^ C.cHH * bTx G.x G.ε) →
    ∀ u0, (mkData G C.cHH D ell N TT T2 a w Fm).s u0 - muMinDef (Fm u0).b' (Fm u0).X' (Fm u0).cc
      ≤ G.x ^ C.cHH * bTx G.x G.ε
end Formalism.LFunctionChainParameters.LBrDiv


