-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
-- name    : Formalism_FlagUnipotentLattices_ConductorCharacterLeakBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:19.015457+00:00
-- url     : https://prove2.me/theorems/1428568b-cc3a-416a-8976-722e94fd0975
-- title:
--   Conductor Character Leak Bound
-- statement:
--   Definitions and structural lemmas for Conductor Character Leak Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/ConductorCharacterLeakBound.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_GramSubmersionSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.S4
open Finset
def WeightedAmplitudeSqSumBoundTwoTypeClasses : Prop :=
  ∀ (k r q : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ) (isBe : Ty → Prop),
    4 * r + 7 ≤ k → 2 ≤ q → 1 ≤ H → (Nonempty Ty → (q : ℝ) ≤ H) → 0 ≤ nn →
    (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H ^ (r + 2) →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t d, ¬ isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (be t / q) ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    (∀ t d, isBe t → ‖amp t d‖ ≤ 7 * (q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2
      ≤ H ^ (39 * (r + 1) ^ 2) * (q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) * nn
def NonGenericBoundLargeHeight : Prop :=
  ∀ (k r : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ),
    2 ≤ H → 0 ≤ nn → (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ H ^ (39 * (r + 1) ^ 2) * nn
def GeomPowers : Prop :=
  ∀ (q k N : ℕ), 2 ≤ q → 2 ≤ k →
    ∑ i ∈ range (N + 1), ((q : ℝ) ^ i) ^ (k - 1) ≤ 2 * ((q : ℝ) ^ N) ^ (k - 1)
def TypeCount : Prop :=
  ∀ (r a q : ℕ) (H : ℝ), 2 ≤ q → 1 ≤ a → (q : ℝ) ^ a ≤ H →
    ((r * (a + 1) ^ 2 + a : ℕ) : ℝ) ≤ H ^ (r + 2)
def CongruenceGroupIndexBound : Prop :=
  ∀ (q A S : ℝ) (r vth : ℕ), 1 ≤ q → 0 ≤ S → (vth : ℝ) + S ≤ A →
    q ^ ((r : ℝ) * (r + 1) * vth) * q ^ ((5 / 2 : ℝ) * (r + 1) * S) ≤ (q ^ A) ^ (9 * ((r : ℝ) + 1) ^ 2)
def GaussSumZeroCountBound : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    (∀ ψ, cond ψ = 0 ↔ ψ = 0) →
    (∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    ∑ u, χ u = 0 →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * χ u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    |((univ.filter fun u => Q u = 0).card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) ∧
    ‖∑ u ∈ univ.filter (fun u => Q u = 0), χ u‖
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)
def CondCountLe : Prop :=
  ∀ (o T : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [AddCommGroup T] [Fintype T]
    [DecidableEq T] (ϖ : o) (red : o →+ T) (cond : AddChar T ℂ → ℕ) (q a : ℕ),
    Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Function.Surjective red → (∀ x, red x = 0 ↔ ϖ ^ a ∣ x) →
    (∀ ψ i, cond ψ ≤ i ↔ ∀ x, ψ (red (ϖ ^ i * x)) = 1) →
    ∀ j, ((univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ j).card : ℝ) ≤ (q : ℝ) ^ j
def ConductorCharacterLeakBound : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (cond : AddChar T ℂ → ℕ) (q a ρ j : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    ((univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ j).card : ℝ) ≤ (q : ℝ) ^ j →
    (∀ i, j < i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    (∀ ψ : AddChar T ℂ,
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ ((cond ψ - j) * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    ((univ.filter fun u => Q u = 0).card : ℝ)
      ≤ 8 / 7 * (q : ℝ) ^ j * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)
def TwistedRowSumsBound : Prop :=
  ∀ (B U Pl X Mv : Type) [Fintype B] [Fintype U] [Fintype Pl] [Fintype X]
    [Fintype Mv] [DecidableEq B] [DecidableEq U] [DecidableEq X]
    (vol : B → ℝ) (Z : Finset U) (UP : Pl → Finset U) (jj : Pl → ℕ) (χ : B → U → ℂ)
    (bb : Mv → B) (uu : Mv → U) (tgt : Mv → Option X) (μ : Mv → ℝ) (ω : X → ℂ) (ω₀ : ℂ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card Pl ≤ 2 → (∀ P, 1 ≤ jj P) → 0 < Fintype.card U →
    (∀ b, 0 ≤ vol b) → 0 < ∑ b, vol b → (∀ m, 0 ≤ μ m) →
    (∀ b u, ∑ m ∈ univ.filter (fun m => bb m = b ∧ uu m = u), μ m
      = if u ∈ Z then vol b / ((∑ b', vol b') * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)) else 0) →
    |(Z.card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) →
    (∀ b, ‖∑ u ∈ Z, χ b u‖ ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)) →
    (∀ b u, ‖χ b u‖ = 1) →
    (∀ P, ((UP P).card : ℝ) = (Fintype.card U : ℝ) / (q : ℝ) ^ (jj P * ρ)) →
    (∀ P, ((Z ∩ UP P).card : ℝ) ≤ 8 / 7 * (q : ℝ) ^ jj P * (((UP P).card : ℝ) / (q : ℝ) ^ a)) →
    (∀ m, tgt m = none → ∃ P, uu m ∈ UP P) →
    (∀ m x, tgt m = some x → ω x = ω₀ * χ (bb m) (uu m)) →
    |(∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m) - 1| ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
    ‖∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x‖
        ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ‖ω₀‖
def KernelAvg7 : Prop :=
  ∀ (ι : Type) (μ : ι → ℝ) (M : ι → ι → ℝ) (ω : ι → ℂ) (q ρ : ℕ),
    (∀ i, 0 ≤ μ i) → Summable μ → (∀ i j, 0 ≤ M i j) → (∀ i, Summable (M i)) →
    (∀ i j, μ i * M i j = μ j * M j i) → (∀ i, ‖ω i‖ = 1) →
    (∀ i, |(∑' j, M i j) - 1| ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) →
    (∀ i, ‖∑' j, (M i j : ℂ) * ω j‖ ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) →
    ‖∑' i, (μ i : ℂ) * ω i‖ ≤ 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ∑' i, μ i
def TotientSqrt : Prop := ∀ w : ℕ, w ≤ 2 * Nat.totient w ^ 2
def NormalCount6 : Prop :=
  ∀ (f T T' NG : ℕ), 1 ≤ f → 3 ≤ T → 3 ≤ T' → 1 ≤ NG →
    (8 * f ^ 2) ^ 2 * (T ^ f * NG) ^ 2 * (T' ^ f * NG) ^ 2 ≤ (NG * (T * T') ^ f) ^ 6
end Formalism.HermitianLatticeCounting.S4


