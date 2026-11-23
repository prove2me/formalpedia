-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:04.866696+00:00
-- url     : https://prove2.me/theorems/54f7eaff-8949-4e9f-bdca-1b4b0c5773fb
-- title:
--   Good Height Exists
-- statement:
--   Definitions and structural lemmas for Good Height Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/GoodHeightExists.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormula
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
open Complex
section defs
variable {N : ℕ} [NeZero N]
abbrev mult (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
open Classical in

def eps0 (χ : DirichletCharacter ℂ N) : ℂ := if χ.Even ∧ χ ≠ 1 then 1 else 0
open Classical in

def del1 (χ : DirichletCharacter ℂ N) : ℂ := if χ = 1 then 1 else 0
def psiRaw (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)
def zsum (χ : DirichletCharacter ℂ N) (T u : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ ZerosBelow χ T, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)
def S1 (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑ᶠ ρ ∈ ZerosBelow χ 1, (mult χ ρ : ℝ) / ‖ρ‖
def NoOrdinate (χ : DirichletCharacter ℂ N) (T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≠ T'
def GoodHeight (χ : DirichletCharacter ℂ N) (κ T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
    1 / (κ * Real.log (N * T')) ≤ |(|ρ.im|) - T'|
end defs
def cLine (u : ℝ) : ℝ := 1 + 1 / Real.log u
def Err (N : ℕ) (u T : ℝ) : ℝ := u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u)
def rectInt (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f (x + y₀ * I)) - (∫ x : ℝ in x₀..x₁, f (x + y₁ * I)) +
    I • (∫ y : ℝ in y₀..y₁, f (x₁ + y * I)) - I • ∫ y : ℝ in y₀..y₁, f (x₀ + y * I)
def rect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := Set.Icc x₀ x₁ ×ℂ Set.Icc y₀ y₁
def perronK (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
def kb (T y : ℝ) : ℝ := if T * |Real.log y| ≤ 1 then 2 else 1 / (T * |Real.log y|)
def vertInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u T' : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T')..T',
    (-logDeriv (DirichletCharacter.LFunction χ) ((cLine u : ℂ) + t * I)) *
      ((u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I))
def PerronL (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u T T' : ℝ), 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 →
    ‖psiRaw χ u - vertInt χ u T'‖ ≤ C * Err N u T
def ShiftBound (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → GoodHeight χ κ T' →
      ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ ≤ C * (Err N u T + S1 χ)
def GoodHeightExists (κ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ GoodHeight χ κ T'
def TruncChange (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 →
      ‖zsum χ T' u - zsum χ T u‖ ≤ C * Err N u T
def ZerosFinite : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, (ZerosBelow χ T).Finite
def PerronKernel : Prop :=
  ∀ y c T : ℝ, 0 < y → 0 < c → 0 < T →
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ 2 * y ^ c ∧
    T * |Real.log y| * ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c
def PerronSumBound (C : ℝ) : Prop :=
  ∀ u T : ℝ, 2 ≤ u → 2 ≤ T →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)) ∧
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n) ≤
      C * (u * Real.log u ^ 2 / T + Real.log u)
def PerronTrunc (C : ℝ) : Prop :=
  ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) → ∀ u T : ℝ, 2 ≤ u → 2 ≤ T →
    ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) - (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T,
        LSeries a ((cLine u : ℂ) + t * I) *
          ((u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I))‖ ≤
      C * (u * Real.log u ^ 2 / T + Real.log u)
def RectCauchy : Prop :=
  ∀ (x₀ x₁ y₀ y₁ : ℝ) (h : ℂ → ℂ) (w : ℂ), x₀ < w.re → w.re < x₁ → y₀ < w.im → w.im < y₁ →
    DifferentiableOn ℂ h (rect x₀ x₁ y₀ y₁) →
    rectInt (fun s => h s / (s - w)) x₀ x₁ y₀ y₁ = 2 * Real.pi * I * h w
def RectResidue : Prop :=
  ∀ (x₀ x₁ y₀ y₁ : ℝ) (H : ℂ → ℂ) (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ) (u : ℝ), 0 < u →
    x₀ < 0 → 0 < x₁ → y₀ < 0 → 0 < y₁ → DifferentiableOn ℂ H (rect x₀ x₁ y₀ y₁) →
    (∀ ρ ∈ Z, ρ ≠ 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁) →
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * ((u : ℂ) ^ s / s)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (H 0 + (∑ ρ ∈ Z, wt ρ * (((u : ℂ) ^ ρ - 1) / ρ)) + e * Real.log u)
def ZeroLocus : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -3 / 2 ≤ s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s = 0 →
      (0 < s.re ∧ s.re < 1) ∨ (s = 0 ∧ χ.Even ∧ χ ≠ 1) ∨ (s = -1 ∧ χ.Odd)
def IsRegPart {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x₁ T' : ℝ) (H : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ H (rect (-1 / 2) x₁ (-T') T') ∧
  ∀ s ∈ rect (-1 / 2) x₁ (-T') T', DirichletCharacter.LFunction χ s ≠ 0 → s ≠ 1 →
    logDeriv (DirichletCharacter.LFunction χ) s =
      H s + (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / (s - ρ)) + eps0 χ / s - del1 χ / (s - 1)
def RegularPart : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ x₁ T' : ℝ, 1 < x₁ → 0 < T' →
    NoOrdinate χ T' → ∃ H : ℂ → ℂ, IsRegPart χ x₁ T' H
def LocalAbstract : Prop :=
  ∀ r R' R : ℝ, 0 < r → r < R' → R' < R → ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ), AnalyticOnNhd ℂ f (Metric.closedBall s₀ R) → f s₀ ≠ 0 → 0 ≤ M →
      (∀ s ∈ Metric.closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) →
      ({ρ | ρ ∈ Metric.closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ Metric.closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ Metric.closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ C * M
def LGrowth (A C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 →
    ‖(1 + del1 χ * (s - 2)) * DirichletCharacter.LFunction χ s‖ ≤ C * (N * (|s.im| + 2)) ^ A
def LocalLemma (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 →
    DirichletCharacter.LFunction χ s ≠ 0 → s ≠ 1 →
    ‖logDeriv (DirichletCharacter.LFunction χ) s -
        (∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)) - eps0 χ / s + del1 χ / (s - 1)‖ ≤
      C * Real.log (N * (|s.im| + 2))
def LogDerivHoriz (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T' : ℝ, 2 ≤ T' →
    GoodHeight χ κ T' → ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T' * I)‖ ≤ C * Real.log (N * T') ^ 2 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (-T' : ℝ) * I)‖ ≤ C * Real.log (N * T') ^ 2
def LogDerivLeft (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      C * Real.log (N * (|t| + 2))
def RegAtZero (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (x₁ T' : ℝ) (H : ℂ → ℂ), 1 < x₁ →
    2 ≤ T' → IsRegPart χ x₁ T' H →
      ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0‖ ≤ C * Real.log (2 * N) + S1 χ
def ContourIdentity : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (u T' : ℝ) (H : ℂ → ℂ), 2 ≤ u →
    2 ≤ T' → NoOrdinate χ T' → IsRegPart χ (cLine u) T' H →
      rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
          (-1 / 2) (cLine u) (-T') T' =
        2 * Real.pi * I * (H 0 + zsum χ T' u - (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          eps0 χ * Real.log u - del1 χ * (u - 1))
def SidesBound (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → GoodHeight χ κ T' →
      ‖rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
          (-1 / 2) (cLine u) (-T') T' + 2 * Real.pi * I * vertInt χ u T'‖ ≤ C * Err N u T
end PI.EF


