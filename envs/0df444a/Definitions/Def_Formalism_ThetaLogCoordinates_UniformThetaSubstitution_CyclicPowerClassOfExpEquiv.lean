-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:55.086875+00:00
-- url     : https://prove2.me/theorems/2874fdfb-3f4e-4ced-a581-e92c04a7c4ad
-- title:
--   Cyclic Power Class Of Exp Equiv
-- statement:
--   Definitions and structural lemmas for Cyclic Power Class Of Exp Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/CyclicPowerClassOfExpEquiv.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
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
def DworkMv : Prop :=
  ∀ (K ι : Type) [Finite ι] [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ)
    (σ : K →+* K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    (∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) →
    ∀ Ψ : MvPowerSeries ι K, MvPowerSeries.constantCoeff Ψ = 0 →
      (Integral (mvExp Ψ) ↔
        ∀ n, ‖MvPowerSeries.coeff n
          (frobVar p (MvPowerSeries.map σ Ψ) - MvPowerSeries.C (p : K) * Ψ)‖ ≤ (p : ℝ)⁻¹)
def Simeq {K ι : Type} [NormedField K] [CharZero K] (f g : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ Integral (mvExp (f - g))
def SimeqRules : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K],
    (∀ f : MvPowerSeries ι K, Simeq f f) ∧
    (∀ f g : MvPowerSeries ι K, Simeq f g → Simeq g f) ∧
    (∀ f g h : MvPowerSeries ι K, Simeq f g → Simeq g h → Simeq f h) ∧
    (∀ f g f' g' : MvPowerSeries ι K, Simeq f g → Simeq f' g' → Simeq (f + f') (g + g')) ∧
    (∀ (κ : Type) [Finite ι] (f g : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) → Simeq f g →
      Simeq (MvPowerSeries.subst φ f) (MvPowerSeries.subst φ g))
def lamF {K : Type} [Field K] (p : ℕ) (ϖ : K) : PowerSeries K :=
  PowerSeries.mk fun n => ϖ ^ (n - 1) * PowerSeries.coeff n (lgF K p)
def altF (K : Type) [Field K] (p : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ l ∈ range (n + 1), if n = (p ^ 2) ^ l then (-1 : K) ^ l else 0
def LogRescale : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ) (ϖ : K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    (PowerSeries.subst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) (lgF K p) : PowerSeries K) =
        PowerSeries.C ϖ * lamF p ϖ ∧
      (∀ n, ‖PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2))‖ ≤
        (p : ℝ)⁻¹) ∧
      ∃ μ : PowerSeries K, PowerSeries.constantCoeff μ = 0 ∧ (∀ n, ‖PowerSeries.coeff n μ‖ ≤ 1) ∧
        (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X ∧
        (PowerSeries.subst (lamF p ϖ) μ : PowerSeries K) = PowerSeries.X ∧
        ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹
def LogRescaleUnique : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) (ϖ : K) (μ μ' : PowerSeries K), 2 ≤ p → (p : K) ≠ 0 →
    PowerSeries.constantCoeff μ = 0 → PowerSeries.constantCoeff μ' = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X →
    (PowerSeries.subst μ' (lamF p ϖ) : PowerSeries K) = PowerSeries.X → μ = μ'
def TraceDual : Prop :=
  ∀ (F L ι : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F L) (σ τ : L ≃ₐ[F] L),
    (σ = τ → ∑ r, σ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) * τ (b r) = 1) ∧
    (σ ≠ τ → ∑ r, σ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) * τ (b r) = 0)
section Coord
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
abbrev ZV (ν r0 r1 : ℕ) : Type := ZMod (2 * ν) × Fin r0 × Fin r1
abbrev EV (ν r0 r1 : ℕ) : Type := Fin ν × Fin r0 × Fin r1
def zLin [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν),
    if x.1 = false then
      (if s.val % 2 = 0 then MvPowerSeries.C (oms x.2.1 s) * MvPowerSeries.X (s, x.2.2) else 0)
    else
      (if s.val % 2 = 1 then MvPowerSeries.C (om x.2.1 s) * MvPowerSeries.X (s, x.2.2) else 0)
def sPos (p : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) : MvPowerSeries (ZV ν r0 r1) K :=
  fun n => ∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l else 0
def hhS [NeZero ν] (p : ℕ) (u : ZMod (2 * ν) → K) : MvPowerSeries (ZV ν r0 r1) K :=
  ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) *
    ∑ ab : Fin r0 × Fin r1, sPos p s ab ^ p * sPos p (s + 1) ab
def uS (c c' : K) (s : ZMod (2 * ν)) : K := if s.val % 2 = 0 then -c' else c
end Coord
def OmOK {K : Type} [NormedField K] (p ν : ℕ) (om oms : Fin ν → ZMod (2 * ν) → K) : Prop :=
  (∀ r s, ‖om r s‖ ≤ 1 ∧ ‖oms r s‖ ≤ 1) ∧
  (∀ r s, ‖om r (s + 1) - om r s ^ p‖ ≤ (p : ℝ)⁻¹ ∧ ‖oms r (s + 1) - oms r s ^ p‖ ≤ (p : ℝ)⁻¹) ∧
  (∀ a b : ZMod (2 * ν), a.val % 2 = b.val % 2 →
    ∑ r, oms r a * om r b = if a = b then 1 else 0)
def sSub {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K)
    (μ : PowerSeries K) (x : Bool × EV ν r0 r1) : MvPowerSeries (ZV ν r0 r1) K :=
  PowerSeries.subst (zLin om oms x) μ
def TwoSums : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (c c' : K) (μ : PowerSeries K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → OmOK p ν om oms → ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    PowerSeries.constantCoeff μ = 0 → (∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) →
    ∃ Y : MvPowerSeries (ZV ν r0 r1) K, Integral Y ∧ MvPowerSeries.constantCoeff Y = 0 ∧
      MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c') =
        hhS p (uS c c') + MvPowerSeries.C (p : K) * Y
def ThmSCore : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (c c' ϖ : K) (μ : PowerSeries K)
    (U : MvPowerSeries (Bool × EV ν r0 r1) K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms → ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U →
    InClass (p : K) (hhS p (uS c c'))
      (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x)
        (mvExp (-(Gtot (E := EV ν r0 r1) p c c' 1)) * U))
def CyclicPowerClassOfExpEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (c c' ϖ : K) (μ : PowerSeries K)
    (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K) (be : MvPowerSeries (Fin 2) K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms → ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
    MvPowerSeries.constantCoeff Φ = 0 →
    Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
      (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
        MvPowerSeries (Bool × EV ν r0 r1) K)) be) →
    Simeq be (Gser p c c') →
    InClass (p : K) (hhS p (uS c c'))
      (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) (mvExp (-Φ) * U0))
end Formalism.InvariantFactorPaths.G7


