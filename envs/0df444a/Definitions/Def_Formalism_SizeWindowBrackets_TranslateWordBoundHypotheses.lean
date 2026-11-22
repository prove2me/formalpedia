-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
-- name    : Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:06.257016+00:00
-- url     : https://prove2.me/theorems/57f582c5-f08f-4100-b81a-63565c5b69fd
-- title:
--   Translate Word Bound Hypotheses
-- statement:
--   Definitions and structural lemmas for Translate Word Bound Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/TranslateWordBoundHypotheses.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioUpperBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
noncomputable section
section Z
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f)
def ZiiR (cZ Sc LZ logT : ℝ) : ℝ :=
  -((∑ t, D.aT t / D.k) * logT) - cZ * D.nT * D.a * Real.log D.k
    - cZ * (f : ℝ) * D.k * (D.b' + Sc) * Real.log D.k - cZ * (f : ℝ) * Sc * logT
    - cZ * (f : ℝ) * D.k ^ 2 * LZ
def ZiiiR (cZ Sc LZ logT : ℝ) : ℝ :=
  cZ * D.nT * D.a * Real.log (D.k * D.v)
    + cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + logT)
    + cZ * (f : ℝ) * D.k ^ 2 * LZ
def PropZ (cZ Sc LZ : ℝ) : Prop :=
  ∀ u0 (u : W u0), ZiiR D cZ Sc LZ (Real.log (D.T u0 u)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ ZiiiR D cZ Sc LZ (Real.log (D.T u0 u))
def LogTUp (cU : ℝ) : Prop :=
  ∀ u0 (u : W u0), Real.log (D.T u0 u) ≤ cU * (m : ℝ) * D.L
def ZWindows (cZ cL cU Sc LZ : ℝ) : Prop :=
  0 ≤ cZ ∧ 0 ≤ cL ∧ 0 ≤ cU ∧ 0 ≤ D.a ∧ 1 ≤ D.k ∧ (m : ℝ) ≤ D.k ∧ 0 ≤ D.b' ∧ 0 ≤ Sc ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.L ∧ D.L ≤ D.La ∧ Real.log D.k ≤ D.La ∧ Real.log (D.k * D.v) ≤ D.La ∧ LZ ≤ cL * D.La ∧
  (f : ℝ) * D.k * (D.b' + Sc) ≤ D.nT * D.a ∧ (f : ℝ) * D.k ^ 2 ≤ D.nT * D.a
def unitZ : ℝ := D.nT * D.a * D.La
end Z
def cSlopeZ (cZ cL cU : ℝ) : ℝ := cZ * (2 + cL + cU) + 2 * cU
def ZTerms : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (cZ cL cU Sc LZ logT : ℝ), ZWindows D cZ cL cU Sc LZ → logT ≤ cU * (m : ℝ) * D.L →
    (∑ t, D.aT t / D.k) * logT ≤ 2 * cU * (unitZ D * ((m : ℝ) / D.k)) ∧
    cZ * D.nT * D.a * Real.log D.k ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * D.k * (D.b' + Sc) * Real.log D.k ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * Sc * logT ≤ cZ * cU * (unitZ D * ((m : ℝ) / D.k)) ∧
    cZ * (f : ℝ) * D.k ^ 2 * LZ ≤ cZ * cL * unitZ D ∧
    cZ * D.nT * D.a * Real.log (D.k * D.v) ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v)) ≤ cZ * unitZ D ∧
    cZ * (f : ℝ) * (D.b' + Sc) * logT ≤ cZ * cU * unitZ D
def ZToSlopes : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (cZ cL cU Sc LZ : ℝ), ZWindows D cZ cL cU Sc LZ → LogTUp D cU → PropZ D cZ Sc LZ →
    cSlopeZ cZ cL cU ≤ C.cSlope → D.Slopes C
section Count
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)
def mainCount (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
def BoundedBy' (c5 : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0),
    mainCount D u0 - c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) ≤ Real.log (X u0 u) ∧
    Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L
def Variation5 (c5 : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u u' : W u0), |Real.log (X u0 u) - Real.log (X u0 u')| ≤ c5 * Real.log D.k
def LevelWindow (Gam : ℝ) (X : ∀ u0, W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0), 0 < X u0 u ∧
    X u0 u * Gam ^ (-(2 / ((f : ℝ) * D.k))) ≤ D.T u0 u ∧
    D.T u0 u ≤ X u0 u * Gam ^ (-(2 / ((f : ℝ) * D.k))) * (1 + 1 / ((f : ℝ) * D.k))
def CountWindows (c5 Gam : ℝ) : Prop :=
  0 ≤ c5 ∧ 0 < f ∧ 1 ≤ D.k ∧ 1 ≤ Gam ∧ D.logGam = Real.log Gam ∧
  D.logGam / ((f : ℝ) * D.k) ≤ 1 ∧ 0 ≤ D.L ∧ D.L ≤ D.La ∧ 1 ≤ D.La ∧ 1 ≤ (m : ℝ) * D.L ∧
  1 ≤ Real.log D.k
end Count
def Prop5ToCount : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (C : Consts)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X →
    LevelWindow D Gam X → C.cCount = c5 + 1 → D.Count C
def Prop5ToCount5 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (C : Consts)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X →
    LevelWindow D Gam X → c5 + 3 ≤ C.cCount → Count5 D C
def Prop5ToLogTUp : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X →
    LevelWindow D Gam X → LogTUp D (c5 + 1)
def LevelLowerOfCount : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ), CountWindows D c5 Gam → BoundedBy' D c5 X →
    LevelWindow D Gam X → (∀ u0 j ρ, 1 ≤ D.w u0 j ρ * D.v / π) → 16 * D.L ≤ D.lg →
    (m : ℝ) ^ 2 ≤ D.k → 1 ≤ D.L → 2 * c5 + 2 ≤ 15 * (m : ℝ) →
    ∀ u0 (u : W u0), (m : ℝ) * D.L / 2 ≤ Real.log (D.T u0 u)
open Formalism.LogVandermondeBounds.StandardLattice Finset in

def TranslateWordBoundHypotheses (C₀ C₃ ε x : ℝ) (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
    (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ) : Prop :=
  1 ≤ f ∧ 2 ≤ m ∧ Even m ∧ 2 ≤ k ∧ (m : ℝ) ^ 2 * x ^ ε ≤ k ∧ (k : ℝ) ≤ x ^ C₀ ∧
  Real.pi ≤ vE ∧ Real.log vE ≤ x ^ ε ∧ 1 ≤ Δ ∧ 1 ≤ g₁ ∧ 1 ≤ g₂ ∧
  Real.log g₁ ≤ C₀ * x ^ ε ∧ Real.log g₂ ≤ C₀ * x ^ ε ∧
  (∀ ρ, ρ < f → PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
    (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) ∧
  0 < massk ∧ 0 < massr ∧ 0 < Isig ∧ 0 < Ipi ∧
  (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) ∧
  (massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
    ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) ∧
  (((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) ∧
  (Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)) ∧
  ((2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ≤ Dstar) ∧
  (Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) ∧
  (∀ ρ, ρ < f → 0 < dsig ρ ∧ dsig ρ ≤ 4 * dTau k m (rowPar k (v ρ) (b ρ)) *
    (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
      (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) ∧
  (dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k)
def CountBoundsFromHypotheses : Prop :=
  ∀ (ε C₀ C₃ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → 1 ≤ C₃ → ∃ c5 : ℝ, 0 ≤ c5 ∧
    ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
      (X : ∀ u0, W u0 → ℝ) (x : ℝ) (k : ℕ) (Δ g₁ g₂ : ℝ),
      1 ≤ x → D.L = x ^ ε → D.k = (k : ℝ) → D.lg = Real.log g₁ + Real.log g₂ →
      (∀ u0 (u : W u0), ∃ (uu v b w : ℕ → ℕ → ℝ) (Dstar dstar massk massr Isig Ipi : ℝ)
          (Lval dsig : ℕ → ℝ),
        TranslateWordBoundHypotheses C₀ C₃ ε x f m k D.v Δ g₁ g₂ uu v b w Dstar dstar massk massr Isig Ipi Lval dsig ∧
        (∀ (j : Fin m) (ρ : Fin f), D.w u0 j ρ = w ρ j) ∧
        0 < X u0 u ∧ X u0 u ^ (f * k) = Dstar / dstar) →
      BoundedBy' D c5 X
def LevelSizes : Prop :=
  ∀ (f m : ℕ) (b T N : ℝ), 1 ≤ f → 6 ≤ m → 8 * (f : ℝ) ≤ b → b ^ ((m : ℝ) / 2) ≤ T →
    2 * (f : ℝ) * N + 1 < T → 2 ≤ N →
    2 < T ∧ 4 * (f : ℝ) ≤ T ∧ 2 * (f : ℝ) / T ≤ 1 / 2 ∧
    4 * (f : ℝ) / T * b ^ 2 + (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1
def PowOfLog : Prop :=
  ∀ (mR b T : ℝ), 0 < b → 0 < T → (mR * Real.log b / 2 ≤ Real.log T ↔ b ^ (mR / 2) ≤ T)
def DefectBound : Prop :=
  ∀ (f : ℕ) (T : ℝ), 2 ≤ T → 1 - (1 - 1 / (T - 1)) ^ f ≤ 2 * (f : ℝ) / T
def RankRatio : Prop :=
  ∀ (f : ℕ) (T : ℝ), 2 * (f : ℝ) + 2 ≤ T → ((1 - 1 / (T - 1)) ^ f)⁻¹ ≤ 1 + 2 * (f : ℝ) / T
def RankOfCount : Prop :=
  ∀ (r X h f : ℕ) (T : ℝ), 1 ≤ h → T - 1 = (h : ℝ) → r * h ^ f = X * (h - 1) ^ f →
    (r : ℝ) = (X : ℝ) * (1 - 1 / (T - 1)) ^ f
section Level
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)
def LevelLowerBound (N : ℝ) : Prop :=
  ∀ u0 (u : W u0), D.b ^ ((m : ℝ) / 2) ≤ D.T u0 u ∧ 2 * (f : ℝ) * N + 1 < D.T u0 u
def LevelClauses : Prop :=
  ∀ u0 (u : W u0), 2 < D.T u0 u ∧ 4 * (f : ℝ) ≤ D.T u0 u ∧
    4 * (f : ℝ) / D.T u0 u * D.b ^ 2
      + (f : ℝ) * Real.log (D.T u0 u - 1) / (D.T u0 u - 2) ≤ 1
end Level
def LevelToClauses : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (N : ℝ),
    1 ≤ f → 6 ≤ m → 8 * (f : ℝ) ≤ D.b → 2 ≤ N → LevelLowerBound D N → LevelClauses D
def HypPrimHasClauses : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} {ι : Type} [DecidableEq ι] (D : Data U0 W Top m f)
    (Q : ∀ u0, W u0 → PPrim ι m), HypPrim D Q → LevelClauses D
section T5
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f)
def lambdaIndex (aM : ℝ) (VV : Finset Top) (Wt bt : Top → ℝ) : ℝ :=
  (m : ℝ) * (∑ t ∈ VV, (aM / D.k + 2 * Wt t + D.k)) + (m : ℝ) * (∑ t ∈ VV, bt t)
def IndexWindows (aM : ℝ) (Wt bt : Top → ℝ) : Prop :=
  0 < D.k ∧ D.k ≤ D.b' ∧ 0 ≤ D.a ∧ aM ≤ 2 * D.a ∧ (∀ t, Wt t ≤ 2 * D.b') ∧ (∀ t, bt t ≤ 2 * D.b')
def unitT : ℝ := D.nT * (m : ℝ) * (D.a / D.k + D.b')
def Price1 (aM Wtop T : ℝ) : ℝ :=
  D.nT * (m : ℝ) * (aM / D.k + 3 * Wtop + D.k) * (1 + 2 * (f : ℝ) / T) * Real.log T
def Price2 (c6 N T : ℝ) (Wp : Fin f → ℝ) : ℝ :=
  c6 * (m : ℝ) * ((∑ τ, Wp τ) + (f : ℝ) * (m : ℝ) * N + D.nT * (m : ℝ) * (D.b' + N)) * Real.log T
def Price2SumW (c6 T : ℝ) (Wp : Fin f → ℝ) : ℝ := c6 * (m : ℝ) * (∑ τ, Wp τ) * Real.log T
def Price2Rest (c6 N T : ℝ) : ℝ :=
  c6 * (m : ℝ) * ((f : ℝ) * (m : ℝ) * N + D.nT * (m : ℝ) * (D.b' + N)) * Real.log T
def RestWindows (N : ℝ) : Prop :=
  (f : ℝ) * (m : ℝ) * N ≤ D.nT * (D.a / D.k) ∧ (m : ℝ) * D.b' ≤ D.a / D.k ∧ (m : ℝ) * N ≤ D.a / D.k
end T5
def IndexToLengthBound : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (aM : ℝ) (VV : Finset Top) (Wt bt : Top → ℝ), IndexWindows D aM Wt bt →
    lambdaIndex D aM VV Wt bt ≤ 7 * D.nT * (m : ℝ) * (D.a / D.k + D.b')
def LamClause {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} {ι : Type}
    (D : Data U0 W Top m f) (cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m) : Prop :=
  ∀ u0 (u : W u0), (Q u0 u).lam ≤ cT * D.nT * (m : ℝ) * (D.a / D.k + D.b')
def LambdaBoundOfIndexWindows : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} {ι : Type}
    (D : Data U0 W Top m f) (Q : ∀ u0, W u0 → PPrim ι m) (aM : ℝ) (Wt bt : Top → ℝ),
    IndexWindows D aM Wt bt →
    (∀ u0 (u : W u0), ∃ VV : Finset Top, (Q u0 u).lam ≤ lambdaIndex D aM VV Wt bt) → LamClause D 7 Q
def SizesPrimHasLam : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} {ι : Type} [DecidableEq ι] (D : Data U0 W Top m f)
    (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m), SizesPrim D C Xpp cT Q → LamClause D cT Q
def Price1Covered : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (aM Wtop T : ℝ), 0 < D.k → D.k ≤ D.b' → 0 ≤ D.a → aM ≤ 2 * D.a → Wtop ≤ 2 * D.b' →
    0 < T → 2 * (f : ℝ) / T ≤ 1 / 2 → 0 ≤ Real.log T →
    Price1 D aM Wtop T ≤ 21 / 2 * (unitT D * Real.log T)
def Price2Split : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (c6 N T : ℝ) (Wp : Fin f → ℝ), Price2 D c6 N T Wp = Price2SumW (m := m) c6 T Wp + Price2Rest D c6 N T
def Price2RestCovered : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (c6 N T : ℝ), 0 ≤ c6 → 0 ≤ D.b' → RestWindows D N → 0 ≤ Real.log T →
    Price2Rest D c6 N T ≤ 3 * c6 * (unitT D * Real.log T)
def Price2SumWNotCovered : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (c6 cT Xp T : ℝ) (Wp : Fin f → ℝ), 0 < D.b → D.a = D.x * D.b → D.b' = D.a / Xp → 1 ≤ m →
    0 < Real.log T → (∀ τ, 0 ≤ Wp τ) → (∃ τ, D.b ≤ Wp τ) → 0 ≤ c6 →
    cT * D.nT * (D.x / D.k + D.x / Xp) < c6 →
    cT * (unitT D * Real.log T) < Price2SumW (m := m) c6 T Wp
def SmallText : Prop :=
  ∀ ε e cT c6 : ℝ, 0 < ε → 0 ≤ e → 0 < c6 → ∃ x₀ : ℝ, ∀ x k nT : ℝ, x₀ ≤ x → 0 ≤ nT → nT ≤ x ^ e →
    0 < k → nT * x ^ 2 ≤ k → cT * nT * (x / k + x / XpTx x ε) < c6
def WeightedPriceInBudget : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (c6 cU T : ℝ) (Wp : Fin f → ℝ), 0 ≤ c6 → 0 ≤ cU → 0 ≤ D.b → (∀ τ, Wp τ ≤ 2 * D.b) →
    0 ≤ Real.log T → Real.log T ≤ cU * (m : ℝ) * D.L → (f : ℝ) * (m : ℝ) * D.b * D.L ≤ D.B0 →
    Price2SumW (m := m) c6 T Wp ≤ 2 * c6 * cU * ((m : ℝ) * D.B0)
def BudgetWindows {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (N : ℝ) : Prop :=
  D.nT ≤ (f : ℝ) ∧ (m : ℝ) * N ≤ D.b ∧ (m : ℝ) * D.b' ≤ D.b
def SecondPriceInBudget : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (c6 cU N T : ℝ) (Wp : Fin f → ℝ), 0 ≤ c6 → 0 ≤ cU → 0 ≤ D.b → (∀ τ, Wp τ ≤ 2 * D.b) → BudgetWindows D N →
    0 ≤ Real.log T → Real.log T ≤ cU * (m : ℝ) * D.L → (f : ℝ) * (m : ℝ) * D.b * D.L ≤ D.B0 →
    Price2 D c6 N T Wp ≤ 5 * c6 * cU * ((m : ℝ) * D.B0)
def PriceTotal : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (c6 cU aM Wtop N T : ℝ) (Wp : Fin f → ℝ), 0 ≤ c6 → 0 ≤ cU → 0 < D.k → D.k ≤ D.b' → 0 ≤ D.a → aM ≤ 2 * D.a →
    Wtop ≤ 2 * D.b' → 0 < T → 2 * (f : ℝ) / T ≤ 1 / 2 → 0 ≤ Real.log T → RestWindows D N →
    0 ≤ D.b → (∀ τ, Wp τ ≤ 2 * D.b) → Real.log T ≤ cU * (m : ℝ) * D.L →
    (f : ℝ) * (m : ℝ) * D.b * D.L ≤ D.B0 →
    Price1 D aM Wtop T + Price2 D c6 N T Wp
      ≤ (21 / 2 + 3 * c6) * (unitT D * Real.log T) + 2 * c6 * cU * ((m : ℝ) * D.B0)
def SlopeCountJoint : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (cZ cL Sc LZ c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ),
    ZWindows D cZ cL (c5 + 1) Sc LZ → PropZ D cZ Sc LZ →
    CountWindows D c5 Gam → BoundedBy' D c5 X → Variation5 D c5 X → LevelWindow D Gam X →
    cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope → c5 + 3 ≤ C.cCount → D.Slopes C ∧ Count5 D C
def ExponentialPowerWindows : Prop :=
  ∀ ε e : ℝ, 0 < ε → 0 ≤ e → ∃ x₀ : ℝ, ∀ x k fR mR nT N Sc lrd v : ℝ, x₀ ≤ x →
    1 ≤ k → k ≤ x ^ e → 1 ≤ fR → fR ≤ x ^ e → 1 ≤ mR → mR ≤ x ^ e → 1 ≤ N → N ≤ x ^ e → 1 ≤ nT →
    0 ≤ Sc → Sc ≤ bpTx x ε → 0 < v → Real.log v ≤ lrd → 0 ≤ lrd →
    Real.log k ≤ Real.log (aTx x ε) + lrd ∧ Real.log (k * v) ≤ Real.log (aTx x ε) + lrd ∧
    Real.log (aTx x ε * v) ≤ Real.log (aTx x ε) + lrd ∧
    Real.log (bTx x ε) ≤ Real.log (aTx x ε) + lrd ∧ 1 ≤ Real.log (bTx x ε) ∧
    fR * k * (bpTx x ε + Sc) ≤ nT * aTx x ε ∧ fR * k ^ 2 ≤ nT * aTx x ε ∧
    k ≤ bpTx x ε ∧
    fR * mR * N ≤ nT * (aTx x ε / k) ∧ mR * bpTx x ε ≤ aTx x ε / k ∧ mR * N ≤ aTx x ε / k ∧
    8 * fR ≤ bTx x ε ∧ mR * N ≤ bTx x ε ∧ mR * bpTx x ε ≤ bTx x ε
section Exact
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
variable (D : Data U0 W Top m f)
def exactMain (bN : U0 → Fin m → Fin f → ℝ) (u0 : U0) : ℝ :=
  (((m : ℝ) - 1) + (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π)
    - (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v)
    + ((m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg
    + ((D.k - 1) / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ))
def ExactCoeff5 (cE : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ) : Prop :=
  ∀ u0 (u : W u0), exactMain D bN u0 - cE * D.L - 1 ≤ Real.log (X u0 u)
def ExactWindows (bN : U0 → Fin m → Fin f → ℝ) : Prop :=
  0 < f ∧ 1 ≤ m ∧ (m : ℝ) ≤ D.k ∧ (m : ℝ) ≤ D.x ∧ 1 ≤ D.L ∧ 0 < D.v ∧
  0 ≤ Real.log (D.v / π) ∧ Real.log (D.v / π) ≤ D.L ∧ Real.log (2 * D.v) ≤ D.L ∧ 0 ≤ D.lg ∧
  ∀ u0 j ρ, 0 < bN u0 j ρ ∧ 0 < D.w u0 j ρ ∧ D.w u0 j ρ ≤ bN u0 j ρ * (1 + 1 / D.x) ∧
    Real.log (bN u0 j ρ) ≤ 2 * D.L
end Exact
def ExactCoeffPrice : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ∀ u0, mainCount D u0 ≤ exactMain D bN u0 + 7 / 2 * D.L + 1
def ExactCoeffToProp5 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (cE c5 : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ExactCoeff5 D cE X bN → (∀ u0 (u : W u0), Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L) →
    0 ≤ c5 → cE + 6 ≤ c5 → BoundedBy' D c5 X
def ExactCoeffToCount5 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f) (C : Consts)
    (cE c5 Gam : ℝ) (X : ∀ u0, W u0 → ℝ) (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ExactCoeff5 D cE X bN → (∀ u0 (u : W u0), Real.log (X u0 u) ≤ c5 * (m : ℝ) * D.L) →
    cE + 6 ≤ c5 → CountWindows D c5 Gam → Variation5 D c5 X → LevelWindow D Gam X →
    c5 + 3 ≤ C.cCount → Count5 D C
def ExactCoeffDiff : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ} (D : Data U0 W Top m f)
    (bN : U0 → Fin m → Fin f → ℝ), ExactWindows D bN →
    ∀ u0, mainCount D u0 - exactMain D bN u0 =
      (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π)
      + (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v)
      - ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg
      + (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))
      + (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ))
def CostAtT : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (c cU pol : ℝ) (Wp : Fin f → ℝ) (EeOff pr : ∀ u0, W u0 → Fin m → ℝ),
    0 ≤ cU → 0 ≤ D.b → 0 ≤ D.B0 → (∀ τ, Wp τ ≤ 2 * D.b) → (f : ℝ) * (m : ℝ) * D.b * D.L ≤ D.B0 → pol ≤ D.B0 →
    (∀ u0 (u : W u0), 0 ≤ Real.log (D.T u0 u) ∧ Real.log (D.T u0 u) ≤ cU * (m : ℝ) * D.L) →
    (∀ u0 (u : W u0) j, D.EeJ u0 u j = EeOff u0 u j + pr u0 u j) →
    (∀ u0 (u : W u0) j, |EeOff u0 u j - D.sumA * D.lg| ≤ c * D.B0) →
    (∀ u0 (u : W u0) j, 0 ≤ pr u0 u j ∧ pr u0 u j ≤ 2 * (∑ τ, Wp τ) * Real.log (D.T u0 u) + pol) →
    c + 4 * cU + 1 ≤ C.cE → EComp5 D C
def CostAtTPrice2 : Prop :=
  ∀ {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f)
    (C : Consts) (c c6 cU N : ℝ) (Wp : Fin f → ℝ) (EeOff pr : ∀ u0, W u0 → ℝ),
    0 ≤ c6 → 0 ≤ cU → 0 ≤ D.b → 0 ≤ D.B0 → (∀ τ, Wp τ ≤ 2 * D.b) → BudgetWindows D N →
    (f : ℝ) * (m : ℝ) * D.b * D.L ≤ D.B0 →
    (∀ u0 (u : W u0), 0 ≤ Real.log (D.T u0 u) ∧ Real.log (D.T u0 u) ≤ cU * (m : ℝ) * D.L) →
    (∀ u0 (u : W u0), D.Ee u0 u = EeOff u0 u + pr u0 u) →
    (∀ u0 (u : W u0), |EeOff u0 u - (m : ℝ) * D.sumA * D.lg| ≤ c * (m : ℝ) * D.B0) →
    (∀ u0 (u : W u0), 0 ≤ pr u0 u ∧ pr u0 u ≤ Price2 D c6 N (D.T u0 u) Wp) →
    c + 5 * c6 * cU ≤ C.cE → EComp5 D C
def PriceModelExample : Prop :=
  ∃ (D : Data Unit (fun _ => Fin 2) Unit 6 2) (cZ cL Sc LZ c5 Gam N aM : ℝ)
    (X : ∀ _ : Unit, Fin 2 → ℝ) (Wt bt : Unit → ℝ) (Wp : Fin 2 → ℝ) (bN : Unit → Fin 6 → Fin 2 → ℝ),
    0 < cZ ∧ 0 < cL ∧ 0 < c5 ∧ 0 < Sc ∧ 0 < LZ ∧ 1 < Gam ∧ 2 ≤ N ∧
    ZWindows D cZ cL (c5 + 1) Sc LZ ∧ PropZ D cZ Sc LZ ∧
    CountWindows D c5 Gam ∧ BoundedBy' D c5 X ∧ Variation5 D c5 X ∧ LevelWindow D Gam X ∧
    8 * ((2 : ℕ) : ℝ) ≤ D.b ∧ LevelLowerBound D N ∧
    IndexWindows D aM Wt bt ∧ RestWindows D N ∧ BudgetWindows D N ∧ (∀ τ, 0 ≤ Wp τ ∧ Wp τ ≤ 2 * D.b) ∧ (∃ τ, D.b ≤ Wp τ) ∧
    ((2 : ℕ) : ℝ) * ((6 : ℕ) : ℝ) * D.b * D.L ≤ D.B0 ∧ D.L = Real.log D.b ∧
    (∀ u0 u, D.muM u0 u = ZiiR D cZ Sc LZ (Real.log (D.T u0 u))) ∧
    (∀ u0 u, D.muMaxM u0 u = ZiiiR D cZ Sc LZ (Real.log (D.T u0 u))) ∧
    D.T () 0 ≠ D.T () 1 ∧
    ExactWindows D bN ∧ ExactCoeff5 D 5 X bN ∧ 5 + 6 ≤ c5
end
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer


