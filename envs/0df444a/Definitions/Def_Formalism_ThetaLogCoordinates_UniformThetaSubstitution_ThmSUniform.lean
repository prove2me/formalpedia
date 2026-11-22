-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:51:40.985388+00:00
-- url     : https://prove2.me/theorems/013a000b-ed0c-49af-87c2-9fccf0bdc44b
-- title:
--   Thm SUniform
-- statement:
--   Definitions and structural lemmas for Thm SUniform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/ThmSUniform.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
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
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def ThmSUniform : Prop :=
  ∀ (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [CompleteSpace K0] (p : ℕ)
    (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∃ c : K0, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧ Simeq be (Gser p c (σ c)) ∧
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K)
      (ν r0 r1 : ℕ) [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) →
    ∀ (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (MvPowerSeries.map j be)) →
      InClass (p : K) (hhS p (uS (j c) (j (σ c))))
        (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) (mvExp (-Φ) * U0))
def GcIsBeta : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ c : K, ‖c‖ ≤ 1 → σ (σ c) = c → BetaHyp p F (Gser p c (σ c))
def GcUnique : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ c d : K, σ (σ c) = c → σ (σ d) = d → Simeq (Gser p c (σ c)) (Gser p d (σ d)) → c = d
def LogCoord : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) (ϖ : K) (μ : PowerSeries K), 2 ≤ p → (p : K) ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X →
    (PowerSeries.subst (PowerSeries.C ϖ * μ) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * PowerSeries.X
def OmBridge : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (ν : ℕ)
    [NeZero ν] (b : Module.Basis (Fin ν) F L) (φ : L ≃+* L) (g : L ≃ₐ[F] L),
    (∀ x, φ (φ x) = g x) → orderOf g = ν →
    ∀ s s' : ZMod (2 * ν), s.val % 2 = s'.val % 2 →
      ∑ r, (φ ^ s.val) ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) *
        (φ ^ s'.val) (b r) = if s = s' then 1 else 0
def HhModP : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 E D : ℕ) [NeZero ν]
    (u : ZMod (2 * ν) → K), p.Prime → 2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) →
    D < p ^ (2 * E) →
    ∃ Y : MvPowerSeries (ZV ν r0 r1) K, Integral Y ∧
      ∀ n : ZV ν r0 r1 →₀ ℕ, n.degree ≤ D →
        MvPowerSeries.coeff n (hhS (r0 := r0) (r1 := r1) p u) = MvPowerSeries.coeff n
          (∑ s : ZMod (2 * ν), ∑ l : Fin E, ∑ l' : Fin E, ∑ ab : Fin r0 × Fin r1,
            MvPowerSeries.C (u s * (-1) ^ (l.val + l'.val)) *
              ((MvPowerSeries.X (s - 2 * (l.val : ZMod (2 * ν)), ab) :
                  MvPowerSeries (ZV ν r0 r1) K) ^ (p ^ (1 + 2 * l.val)) *
                MvPowerSeries.X (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab) ^ (p ^ (2 * l'.val))) +
            MvPowerSeries.C (p : K) * Y)
def ThmSPlaces : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype Pl] [DecidableEq Pl]
    (p r0 r1 : ℕ) (ν : Pl → ℕ) [∀ v, NeZero (ν v)]
    (om oms : ∀ v, Fin (ν v) → ZMod (2 * ν v) → K) (c c' : Pl → K) (ϖ : K) (μ : PowerSeries K)
    (U : MvPowerSeries (Σ v, Bool × EV (ν v) r0 r1) K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ v, OmOK p (ν v) (om v) (oms v)) →
    (∀ v, ‖c v‖ ≤ 1) → (∀ v, ‖c' v‖ ≤ 1) → PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U →
    ∃ V : MvPowerSeries (Σ v, ZV (ν v) r0 r1) K, Integral V ∧
      MvPowerSeries.subst
          (fun x : Σ v, Bool × EV (ν v) r0 r1 =>
            atPlace (ι := fun v => ZV (ν v) r0 r1) x.1
              (MvPowerSeries.C ϖ * sSub (om x.1) (oms x.1) μ x.2))
          ((∏ v, atPlace (ι := fun v => Bool × EV (ν v) r0 r1) v
            (mvExp (-(Gtot (E := EV (ν v) r0 r1) p (c v) (c' v) 1)))) * U) =
        (∏ v, atPlace (ι := fun v => ZV (ν v) r0 r1) v
          (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hhS p (uS (c v) (c' v)))))) * V
end Formalism.InvariantFactorPaths.G7


