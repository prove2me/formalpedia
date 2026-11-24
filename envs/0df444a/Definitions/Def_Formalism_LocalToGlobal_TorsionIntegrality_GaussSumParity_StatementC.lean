-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:54.873804+00:00
-- url     : https://prove2.me/theorems/028dc0de-1345-4c16-ad83-829111b9685d
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
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
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob UnrOK IsLawOfLog)
section Defs
variable {K : Type} [Field K]
def IsHom (F FE : MvPowerSeries (Fin 2) K) (θ : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff θ = 0 ∧
  PowerSeries.subst F θ = MvPowerSeries.subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] FE
def mulS (K : Type) [Field K] (l : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l)
def combS {κ : Type} [Fintype κ] (l : ℕ) (c : κ → K) : MvPowerSeries κ K :=
  PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * at1 j (lgF K l)) (expF K l)
end Defs
def NormRel {K : Type} [NormedField K] [CharZero K] (l : ℕ) (σ : K →+* K) (ph : PowerSeries K)
    (α : K) : Prop :=
  Simeq (PowerSeries.subst (mulS K l α) ph : MvPowerSeries Unit K)
    (MvPowerSeries.C (α * σ α) * ph)
def SigmaIsom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ a : K, ‖σ a‖ = ‖a‖
def FixedIsLimit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∀ k : ℕ, ∃ n : ℕ, ‖x - n‖ ≤ ((l : ℝ) ^ k)⁻¹
def SimeqClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : ℕ → MvPowerSeries τ K) (g : MvPowerSeries τ K),
    (∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n g))) →
    (∀ k, Simeq (f k) 0) → Simeq g 0
def SimeqFixed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : MvPowerSeries τ K) (c : K), ‖c‖ ≤ 1 → σ c = c →
    Simeq f 0 → Simeq (MvPowerSeries.C c * f) 0
def CoboundaryCocycleTransportAlongHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ (FE : MvPowerSeries (Fin 2) K) (θ phE ph : PowerSeries K),
      MvPowerSeries.constantCoeff FE = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) → IsHom F FE θ →
      F1 FE (cob FE phE) → Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      F1 F (cob F ph)
def TransportNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (θ phE ph eE : PowerSeries K) (α : K),
      PowerSeries.constantCoeff θ = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) →
      PowerSeries.constantCoeff eE = 0 →
      ‖α‖ ≤ 1 → σ (σ α) = α →
      PowerSeries.subst (mulS K l α) θ = PowerSeries.subst θ eE →
      Simeq (PowerSeries.subst eE phE : MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * phE) →
      Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      NormRel l σ ph α
def FixedLinear : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 → ∀ n : K, ‖n‖ ≤ 1 → σ n = n →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.X 0, at1 (1 : Fin 2) (mulS K l n)] be0)
        (MvPowerSeries.C n * be0)
def NormUnits : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (ph : PowerSeries K), PowerSeries.constantCoeff ph = 0 →
    ∀ S : Set K, (∀ α ∈ S, NormRel l σ ph α) →
      ∀ α : K, (∀ ε : ℝ, 0 < ε → ∃ a ∈ S, ‖a - α‖ < ε) → NormRel l σ ph α
def SecondLevelOfNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ ph : PowerSeries K, PowerSeries.constantCoeff ph = 0 → F1 F (cob F ph) →
    (∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) →
      F2 l σ (cob F ph) ∧
      (∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → NormRel l σ ph α) ∧
      Simeq (MvPowerSeries.C (2 : K) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) (cob F ph))
def SplitPh : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ ph : PowerSeries K, PowerSeries.constantCoeff ph = 0 → F1 F (cob F ph) →
    (∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) →
    ∀ (κ E : Type) [Fintype κ] [Fintype E] [DecidableEq E] (c : κ → Bool × E → K),
      (∀ k x, ‖c k x‖ ≤ 1 ∧ σ (σ (c k x)) = c k x) →
      (∀ x x' : Bool × E, ∑ k, c k x * σ (c k x') = if x.1 ≠ x'.1 ∧ x.2 = x'.2 then 1 else 0) →
      Simeq (∑ k, PowerSeries.subst (combS l (c k)) ph)
        (∑ e : E, MvPowerSeries.subst
          (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
            MvPowerSeries (Bool × E) K)) (cob F ph))
def UnramTop : Prop :=
  ∀ (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K), UnrOK K l σ →
    Formalism.DworkPowerSeriesWeights.Unram l (⊤ : Subfield K)
def FOfBetaHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, Formalism.InvariantFactorPaths.G7.BetaHyp l F be0 → F1 F be0 ∧ F2 l σ be0
def EigenEven : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → ∀ (ι : Type) [Fintype ι]
    (om oms : ι → K) (a : K) (c : ι → ι → K), (∀ r r', σ (σ (c r' r)) = c r' r) →
    (∀ r, a * om r = ∑ r', c r' r * om r') → ∀ s : ZMod d, s.val % 2 = 0 →
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = false then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (false, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] a) * zXY l σ om oms s
end Formalism.L2.Th1.D


