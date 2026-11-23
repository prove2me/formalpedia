-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:31.766076+00:00
-- url     : https://prove2.me/theorems/e4773375-d7d0-45db-89ef-d26f33045f3f
-- title:
--   Eisenstein S2 Limit Formula
-- statement:
--   Definitions and structural lemmas for Eisenstein S2 Limit Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/EisensteinS2LimitFormula.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy MaximalUnramifiedExtension cW wpNum wpDen uSer IsGoodModel)
namespace Formalism.L2.Th1.F
def pOf {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 2) (wpNum g2 g3)
def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K := ⟨0, 0, 0, -g2 / 4, -g3 / 4⟩
def POfIsWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K), Formalism.L2.Th1.B.IsWp g2 g3 (pOf g2 g3)
def WpNumDen : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    wpNum g2 g3 = 1 + PowerSeries.X ^ 2 * pOf g2 g3 ∧
    wpDen g2 g3 = 1 - PowerSeries.C (1 / 2 : K) * PowerSeries.X ^ 3
      * PowerSeries.derivative K (pOf g2 g3)
def POfLattice : Prop := ∀ L : PeriodPair, pSeries L = pOf L.g₂ L.g₃
def EisensteinRecursion : Prop :=
  ∀ (L : PeriodPair) (k : ℕ), 2 ≤ k → (2 * (k : ℂ) - 1) * L.G (2 * k) = cW L.g₂ L.g₃ k
def USerLattice : Prop :=
  ∀ L : PeriodPair,
    AnalyticAt ℂ (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z) 0 ∧
    taylor0 (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z) = uSer L.g₂ L.g₃
def USerExp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    Formalism.L2.Th1.A.expSer (shortW g2 g3) = uSer g2 g3 ∧
    Formalism.L2.Th1.A.g₂ (shortW g2 g3) = g2 ∧ Formalism.L2.Th1.A.g₃ (shortW g2 g3) = g3
def HasCMByStable : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), HasCMBy d L → ∀ m n : ℤ,
    MulStable L ((m : ℂ) + (n : ℂ) * omegaK d) ∧
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4)
def HasCMByScale : Prop :=
  ∀ (d : ℕ) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0), HasCMBy d L → HasCMBy d (scalePair L c hc)
def CmPairHasCMBy : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd b →
    HasCMBy d (cmPair a b d ha hd)
def HasCMByIsogeny : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), HasCMBy d L → ∀ m n : ℤ, (m, n) ≠ (0, 0) → 0 < d →
    ∃ S : Finset ℂ, IsKerReps L ((m : ℂ) + (n : ℂ) * omegaK d) S ∧
      ((S.card : ℝ) + 1 = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4)) ∧
      Formalism.L2.Th1.C.IsogenyFormula (pSeries L) (s2 L) (fun P : S => L.weierstrassP (P : ℂ))
        ((m : ℂ) + (n : ℂ) * omegaK d) ∧
      (((m : ℂ) + (n : ℂ) * omegaK d) ^ 2
          - (Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d) : ℂ)) * s2 L
        = ∑ P ∈ S, L.weierstrassP P
def SeriesScale : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 lam : K),
    (∀ k, cW (lam ^ 4 * g2) (lam ^ 6 * g3) k = lam ^ (2 * k) * cW g2 g3 k) ∧
    wpNum (lam ^ 4 * g2) (lam ^ 6 * g3) = PowerSeries.rescale lam (wpNum g2 g3) ∧
    wpDen (lam ^ 4 * g2) (lam ^ 6 * g3) = PowerSeries.rescale lam (wpDen g2 g3) ∧
    pOf (lam ^ 4 * g2) (lam ^ 6 * g3) = PowerSeries.C (lam ^ 2) * PowerSeries.rescale lam (pOf g2 g3) ∧
    PowerSeries.C lam * uSer (lam ^ 4 * g2) (lam ^ 6 * g3) = PowerSeries.rescale lam (uSer g2 g3)
def SigmaScale : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K) (s lam : K),
    PowerSeries.C lam * Formalism.L2.Th1.B.sigma (PowerSeries.C (lam ^ 2) * PowerSeries.rescale lam P)
      = PowerSeries.rescale lam (Formalism.L2.Th1.B.sigma P) ∧
    PowerSeries.C lam
        * Formalism.L2.Th1.B.sgStar (lam ^ 2 * s) (PowerSeries.C (lam ^ 2) * PowerSeries.rescale lam P)
      = PowerSeries.rescale lam (Formalism.L2.Th1.B.sgStar s P)
def SeriesMap : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (φ : K →+* K') (g2 g3 s : K)
    (P : PowerSeries K),
    PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) ∧
    PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) ∧
    PowerSeries.map φ (pOf g2 g3) = pOf (φ g2) (φ g3) ∧
    PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) ∧
    PowerSeries.map φ (Formalism.L2.Th1.B.sigma P) = Formalism.L2.Th1.B.sigma (PowerSeries.map φ P) ∧
    PowerSeries.map φ (Formalism.L2.Th1.B.sgStar s P) = Formalism.L2.Th1.B.sgStar (φ s) (PowerSeries.map φ P)
def GoodModelLattice : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]),
    IsGoodModel l L ι g2 g3 → ∃ (c : ℂ) (hc : c ≠ 0),
      g2 = ι (scalePair L c hc).g₂ ∧ g3 = ι (scalePair L c hc).g₃ ∧
      PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries (scalePair L c hc)) = pOf g2 g3 ∧
      PowerSeries.map (ι : ℂ →+* ℂ_[l]) (taylor0 (wSigma (scalePair L c hc)))
        = Formalism.L2.Th1.B.sigma (pOf g2 g3) ∧
      PowerSeries.map (ι : ℂ →+* ℂ_[l]) (taylor0 (sgStar (scalePair L c hc)))
        = Formalism.L2.Th1.B.sgStar (ι (s2 (scalePair L c hc))) (pOf g2 g3) ∧
      PowerSeries.map (ι : ℂ →+* ℂ_[l])
          (taylor0 (fun z => -2 * (scalePair L c hc).weierstrassP z
            / (scalePair L c hc).derivWeierstrassP z))
        = uSer g2 g3
def IotaExists : Prop := ∀ (l : ℕ) [Fact l.Prime], Nonempty (ℂ ≃+* ℂ_[l])
def JInvScale : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (hc : c ≠ 0),
    Formalism.L2.Th1.CM.jInv (scalePair L c hc) = Formalism.L2.Th1.CM.jInv L
def EisensteinS2LimitFormula : Prop :=
  ∀ L : PeriodPair, Filter.Tendsto
    (fun s : ℝ => ∑' ω : L.lattice, ((ω : ℂ) ^ 2)⁻¹ * ((‖(ω : ℂ)‖ ^ (-(2 * s)) : ℝ) : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (s2 L))
end Formalism.L2.Th1.F


