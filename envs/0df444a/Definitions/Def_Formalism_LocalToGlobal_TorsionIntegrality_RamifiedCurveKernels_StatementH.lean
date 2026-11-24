-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:40.324911+00:00
-- url     : https://prove2.me/theorems/d7ea46ba-d4e6-41e1-9fbc-86e1498608f0
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementH.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_FormalGroupLog_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
def JetsIn {K : Type} [Field K] {ι : Type} (R : Subring K) (f : MvPowerSeries ι K) : Prop :=
  ∀ κ : ι →₀ ℕ, ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ f ∈ R
def JetsIn1 {K : Type} [Field K] (R : Subring K) (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, ((n.factorial : ℕ) : K) * PowerSeries.coeff n f ∈ R
def inBlock {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K) :
    MvPowerSeries (B × ι) K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) f
def tens4 {K : Type} [Field K] {ι : Type} (f : MvPowerSeries ι K) : MvPowerSeries (Fin 4 × ι) K :=
  ∏ k : Fin 4, inBlock k f
def JetsInNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : MvPowerSeries ι K),
    JetsIntegral f ↔ JetsIn (Formalism.G.unitBall K) f
def JetsRing : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (ι : Type),
    (∀ c ∈ R, JetsIn R (MvPowerSeries.C c : MvPowerSeries ι K)) ∧
    (∀ i : ι, JetsIn R (MvPowerSeries.X i : MvPowerSeries ι K)) ∧
    (∀ f g : MvPowerSeries ι K, JetsIn R f → JetsIn R g → JetsIn R (f + g)) ∧
    (∀ f : MvPowerSeries ι K, JetsIn R f → JetsIn R (-f)) ∧
    (∀ f g : MvPowerSeries ι K, JetsIn R f → JetsIn R g → JetsIn R (f * g))
def IntJets : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (ι : Type) (f : MvPowerSeries ι K),
    Formalism.L2.Th1.C.IntMv R f → JetsIn R f
def JetsDeriv : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (ι : Type) (f : MvPowerSeries ι K),
    JetsIn R f ↔ MvPowerSeries.constantCoeff f ∈ R ∧ ∀ i, JetsIn R (MvPowerSeries.pderiv K i f)
def JetsDivPow : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (ι : Type) (a : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff a = 0 → JetsIn R a →
    ∀ m : ℕ, JetsIn R (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m)
def JetsSubstOne : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (ι : Type) (f : PowerSeries K)
    (a : MvPowerSeries ι K), JetsIn1 R f → MvPowerSeries.constantCoeff a = 0 → JetsIn R a →
    JetsIn R (PowerSeries.subst a f)
def JetsSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (ι κ : Type) [Fintype ι]
    (f : MvPowerSeries ι K) (a : ι → MvPowerSeries κ K), JetsIn R f →
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, JetsIn R (a i)) →
    JetsIn R (MvPowerSeries.subst a f)
def JetsExp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (ι : Type) (a : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff a = 0 → JetsIn R a → JetsIn R (Formalism.L2.Th1.C.mvExp a)
def JetsFourth : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (ι : Type) [Fintype ι] (f : MvPowerSeries ι K),
    (∀ c : K, c ^ 4 ∈ R → c ∈ R) → JetsIn R (tens4 f) → JetsIn R f
def JetsOfDJets : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv f : PowerSeries K),
    Formalism.L2.Th1.C.IsLogPair l linv →
    ((∀ i : ℕ, Formalism.L2.Th1.C.jet l f i ∈ R) ↔ JetsIn1 R (PowerSeries.subst linv f))
def IntDJets : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (l f : PowerSeries K),
    Formalism.L2.Th1.C.IsOneUnit R (PowerSeries.derivative K l) → Formalism.L2.Th1.C.IntPS R f →
    ∀ i : ℕ, Formalism.L2.Th1.C.jet l f i ∈ R
def IntMvZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv : PowerSeries K),
    Formalism.L2.Th1.C.IsLogPair l linv → Formalism.L2.Th1.C.IsOneUnit R (PowerSeries.derivative K l) →
    ∀ (n : Type) [Fintype n] (G : MvPowerSeries n K), Formalism.L2.Th1.C.IntMv R G →
    JetsIn R (MvPowerSeries.subst
      (fun i : n => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv :
        MvPowerSeries n K)) G)
end Formalism.L2.Th1.G


