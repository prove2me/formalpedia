-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
-- name    : Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:33.453969+00:00
-- url     : https://prove2.me/theorems/d1765f01-5bed-4155-b48d-8a1ac7e9b809
-- title:
--   Prime Class Loss Hypotheses Satisfiable
-- statement:
--   Definitions and structural lemmas for Prime Class Loss Hypotheses Satisfiable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
noncomputable section
def clr (P : Par) : Par := { P with β := 0, s₀ := 0 }
def WindowsD (P : Par) (e K : ℝ) : Prop :=
  0 < P.ε ∧ P.ε ≤ 1 ∧ 0 ≤ e ∧ 1 ≤ K ∧
  (P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂ ∧ (2 : ℝ) ^ P.e₂ ≤ P.n) ∧ P.n ≤ P.x ^ e ∧
  P.x ^ 2 ≤ P.k ∧ P.k ≤ P.x ^ e ∧
  0 ≤ P.N ∧ P.N ≤ P.x ^ e ∧ 0 ≤ P.t ∧ P.t ≤ P.x ^ e ∧
  P.x ^ 4 + 1 ≤ (P.p₀ : ℝ) ∧ (P.p₀ : ℝ) ≤ P.x ^ e ∧
  0 ≤ P.La ∧ P.La ≤ P.x ^ (2 * P.ε) ∧
  0 ≤ P.rG ∧ P.rG ≤ P.x ^ e ∧
  0 ≤ P.Sc ∧ P.Sc ≤ Real.exp (P.x ^ (P.ε / 4)) ∧ 0 ≤ P.η ∧ P.η ≤ Real.exp (P.x ^ (P.ε / 4)) ∧
  0 ≤ P.ρ ∧ P.ρ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.th ∧ P.th ≤ P.x⁻¹ ∧
  P.x ^ 2 ≤ P.K₀ ∧ P.x ^ 2 ≤ (P.d : ℝ) ∧
  0 ≤ P.C ∧ P.C ≤ K ∧ 0 ≤ P.Cord ∧ P.Cord ≤ K ∧
  1 ≤ P.Y ∧ P.Y ≤ 2 * P.Xp ∧
  0 ≤ P.bo ∧ P.bo ≤ Real.exp (P.x ^ P.ε / 2)
def WindowsDIff : Prop :=
  ∀ (P : Par) (e K : ℝ), WindowsD P e K ↔ Windows (clr P) e K
def WindowsDOf : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → WindowsD P e K
variable {ι κ τ : Type}
def lhsW (cand : Finset ℕ) (θ : ℝ) (Sig : ℕ → ℝ) : ℝ :=
  ∑ p ∈ cand, Real.log p / p * ((if θ < Sig p then 2 else 0) + 4 * Sig p)
def badPrimeLogWeightedCount (PR : Finset ℕ) (TT : Finset τ) (BAD : ℕ → τ → Prop) : ℝ :=
  ∑ p ∈ PR, Real.log p / p * ((TT.filter fun t => BAD p t).card : ℝ)
def OutD : Prop :=
  ∀ (τ : Type) (Ps PR : Finset ℕ) (cl : ℕ → PClass) (TT : Finset τ) (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop)
    (m a R : ℝ), 0 ≤ m → 0 ≤ a → badPrimeLogWeightedCount PR TT BAD ≤ R →
    (∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ PR ∧ BAD p t) →
    ∑ p ∈ Ps.filter (fun p => cl p = PClass.served), 4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      4 * a * m * R
def SecondD : Prop :=
  ∀ (Ps cand : Finset ℕ) (cl : ℕ → PClass) (Sig : ℕ → ℝ) (θ m T a R : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a →
    (∀ p ∈ cand, 0 ≤ Sig p) → lhsW cand θ Sig ≤ R →
    (∀ p ∈ Ps, cl p = PClass.second → p ∈ cand ∧ θ < Sig p) →
    4 * m * T * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤ 2 * a * m * T * R
def IoD : Prop :=
  ∀ (cand : Finset ℕ) (Sig io : ℕ → ℝ) (θ m T a R : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a → lhsW cand θ Sig ≤ R →
    (∀ p ∈ cand, io p ≤ 2 * Sig p * (2 * (m * T * a) / p)) →
    ∑ p ∈ cand, Real.log p * io p ≤ a * m * T * R
def tOutD (P : Par) (m T : ℝ) : ℝ := 4 * P.a * m * (T * P.x ^ (-2 + P.ε))
def tSecondD (P : Par) (m T : ℝ) : ℝ := 2 * P.a * m * T * (P.x ^ 9)⁻¹
def tIoD (P : Par) (m T : ℝ) : ℝ := P.a * m * T * (P.x ^ 9)⁻¹
def SizeOutD : Prop :=
  ∀ (P : Par) (e K m T : ℝ), WindowsD P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tOutD P m T ≤ sg P K * unitU P m T
def SizeSecondD : Prop :=
  ∀ (P : Par) (e K m T : ℝ), WindowsD P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tSecondD P m T ≤ sg P K * unitU P m T
def SizeIoD : Prop :=
  ∀ (P : Par) (e K m T : ℝ), WindowsD P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tIoD P m T ≤ sg P K * unitU P m T
def tDetD (P : Par) (m T : ℝ) : ℝ :=
  tFloors P m + tCp P m T + tPrLow P m T + tPrHigh P m T + tOr P m T + tOutD P m T + tOrders P m T
    + tBand P m T + tHigh P m T + tD P m T + tSecondD P m T
def ExplicitSizeBoundUnderWindows : Prop :=
  ∀ (P : Par) (e K m T : ℝ), WindowsD P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tDetD P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T
def PrimeClassLossHypotheses (P : Par) {U : Type} (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  TT.Nonempty ∧ (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) ∧ (∀ p ∈ cand, 0 ≤ Sig p) ∧
  lhsW cand P.θ Sig ≤ (P.x ^ 9)⁻¹ ∧
  badPrimeLogWeightedCount PR TT BAD ≤ (TT.card : ℝ) * P.x ^ (-2 + P.ε) ∧
  (∀ υ, ∀ p ∈ cand, io υ p ≤ 2 * Sig p * (2 * ((J.card : ℝ) * TT.card * P.a) / p)) ∧
  (∀ υ, ParametersHyp P Ps J TT (D υ) ∧ FirstHyp P Ps (D υ).cl ∧
    (∀ p ∈ Ps, (D υ).cl p = PClass.second → p ∈ cand ∧ P.θ < Sig p) ∧
    (∀ p ∈ Ps, (D υ).cl p = PClass.served → ∀ t ∈ TT \ (D υ).TTp p, p ∈ PR ∧ BAD p t))
def ExcessAndPrimeLogSumUnitBounds (P : Par) {U : Type} (Ps cand : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  (∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤ (3 * P.C + 13) * unitU P J.card TT.card) ∧
  ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ unitU P J.card TT.card
def ExplicitLossAndPrimeLogSumBounds (P : Par) (K : ℝ) {U : Type} (Ps cand : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  (∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P J.card TT.card) ∧
  ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ sg P K * unitU P J.card TT.card
def ExplicitLossBoundsUnderSizeWindows : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → WindowsD P e K → LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D → ExplicitLossAndPrimeLogSumBounds P K Ps cand J TT io D
def LossBoundsUnderSizeWindows : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → WindowsD P e K → LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D → ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D
def LossBoundsEventually : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ,
    ∀ (P : Par), P.ε = ε → P.Cord = Cord → x₀ ≤ P.x → WindowsD P e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D → ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds in

def LossBoundsOfD : Prop :=
  ∀ (P : Par) (ι κ τ U U0 : Type) (Ps cand : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → ℝ) (D : U → LD ι κ τ) (sel : U0 → U)
    {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (Cc : Consts),
    ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D → 1 ≤ P.x → 0 ≤ P.ε → 0 ≤ P.C →
    Dd.x = P.x → Dd.ε = P.ε → Dd.b = P.b → Fintype.card Top = TT.card → m = J.card →
    (∀ u0, Dd.ASK u0 = (D (sel u0)).ASK P.d Ps J TT) → (∀ u0, Dd.Ga u0 = (D (sel u0)).Ga J) →
    (∀ u0, Dd.IO u0 = ∑ p ∈ cand, Real.log p * io (sel u0) p) →
    3 * P.C + 13 ≤ Cc.cLoss → 0 ≤ Cc.eLoss →
    LossBounds Dd Cc
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds in

def DLossesLeadingTermForm : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ,
    ∀ (P : Par), P.ε = ε → P.Cord = Cord → x₀ ≤ P.x → WindowsD P e K →
    ∀ (ι κ τ U U0 : Type) (Ps cand PR : Finset ℕ) (J : Finset κ)
      (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
        ∀ (sel : U0 → U) {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
          (Dd : Data U0 W Top m f) (Cc : Consts),
          Dd.x = P.x → Dd.ε = P.ε → Dd.b = P.b → Fintype.card Top = TT.card → m = J.card →
          (∀ u0, Dd.ASK u0 = (D (sel u0)).ASK P.d Ps J TT) → (∀ u0, Dd.Ga u0 = (D (sel u0)).Ga J) →
          (∀ u0, Dd.IO u0 = ∑ p ∈ cand, Real.log p * io (sel u0) p) →
          3 * P.C + 13 ≤ Cc.cLoss → 0 ≤ Cc.eLoss →
          LossBounds Dd Cc
def PrimeClassLossHypothesesSatisfiable : Prop :=
  ∀ (P : Par) (e K : ℝ), WindowsD P e K → LargeX P.x P.ε e K →
    ∃ (Ps cand PR : Finset ℕ) (J : Finset Unit) (TT : Finset Unit) (BAD : ℕ → Unit → Prop)
      (Sig : ℕ → ℝ) (io : Unit → ℕ → ℝ) (D : Unit → LD ℕ Unit Unit),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D ∧ J.card = 1 ∧ TT.card = 1 ∧
      (∀ p ∈ PR, p.Prime ∧ (p : ℝ) < P.Xp) ∧ cand ⊆ PR ∧ PR ⊆ Ps ∧
      (∀ p ∈ Ps, (D ()).cl p ≠ PClass.served → io () p = 0) ∧
      0 < (D ()).ASK P.d Ps J TT ∧
      (∃ p ∈ Ps, (D ()).cl p = PClass.second) ∧
      (∃ p ∈ cand, (D ()).cl p = PClass.served ∧ 0 < Sig p ∧ Sig p ≤ P.θ ∧ 0 < io () p ∧
          (TT \ (D ()).TTp p).Nonempty) ∧
      (∃ p ∈ Ps, (D ()).cl p = PClass.served ∧ (D ()).TTp p = TT ∧ 0 < (D ()).vonMangoldtClassSum () () p)
end
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses


