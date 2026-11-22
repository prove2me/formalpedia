-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementN
-- name    : Formalism_GaussJetBounds_StatementN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:32.025978+00:00
-- url     : https://prove2.me/theorems/f1f81a54-2a9f-49b0-b2dc-a9cdd192458a
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementN.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementI
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
universe u
namespace Formalism.DworkPowerSeriesWeights
def linForm {K : Type u} [Field K] {ι : Type} [Fintype ι] (L : ι → K) : MvPolynomial ι K :=
  ∑ x, MvPolynomial.C (L x) * MvPolynomial.X x
def quadSer {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → ι → K) : MvPowerSeries ι K :=
  ∑ x, ∑ y, MvPowerSeries.C (c x y) * MvPowerSeries.X x * MvPowerSeries.X y
def polar {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → ι → K) (L L' : ι → K) : K :=
  ∑ x, ∑ y, c x y * (L x * L' y + L y * L' x)
def Matchings : Prop :=
  ∀ (K : Type u) [NormedField K] [CharZero K] (ι : Type) [Fintype ι] (c : ι → ι → K) (S : K)
    (sg : MvPowerSeries ι K) (n : ℕ) (L : Fin n → ι → K),
    jetPair (∏ i, linForm (L i)) (mvExp ((-S) • quadSer c) * sg) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) *
          jetPair (∏ i ∈ Finset.univ.filter (fun i => σ i = i), linForm (L i)) sg
def JetsIntegral {K : Type u} [NormedField K] {ι : Type} (sg : MvPowerSeries ι K) : Prop :=
  ∀ κ : ι →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ sg‖ ≤ 1
def PairJet : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (ι : Type) [Fintype ι] (S : K) (u : ι → K), ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) → (∀ i, ‖u i‖ ≤ 1) →
    ∀ sg : MvPowerSeries (Bool × ι) K, JetsIntegral sg → ∀ κ : (Bool × ι) →₀ ℕ,
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
            MvPowerSeries.X (true, i)) * sg)‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ))
def OneRowBasis : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (N0 : ℕ) (h0 : 0 < N0) (x1 : Fin N0 → K),
    (∀ a, ‖x1 a‖ ≤ 1) → (∃ a, ‖x1 a‖ = 1) →
    ∃ f : Matrix (Fin N0) (Fin N0) K, (∀ a a', ‖f a a'‖ ≤ 1) ∧ ‖f.det‖ = 1 ∧
      ∀ a, (∑ a', x1 a' * f a a') = if a = ⟨0, h0⟩ then 1 else 0
def OneRow : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (N0 N1 C : ℕ)
    (f : Matrix (Fin N0) (Fin N0) K), (∀ a a', ‖f a a'‖ ≤ 1) → ‖f.det‖ = 1 →
    ∀ (x : Fin N0 → Fin N0 → K), (∀ i a, ‖x i a‖ ≤ 1) → ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
      (I : ∀ c, Fin (p c) → Fin N1),
    ∃ Q : MvPolynomial (Fin N0 × Fin N1) K, (∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) ∧
      minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a, MvPolynomial.C (x i a) * MvPolynomial.X (a, b) : MvPolynomial (Fin N0 × Fin N1) K))
          p hp I =
        MvPolynomial.aeval (fun y : Fin N0 × Fin N1 =>
          (∑ a', MvPolynomial.C (f y.1 a') * MvPolynomial.X (a', y.2) :
            MvPolynomial (Fin N0 × Fin N1) K)) Q ∧
      ∀ mono ∈ Q.support, ∀ a : Fin N0, (∑ b : Fin N1, mono (a, b)) ≤ C
def ThmB : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (S : K) (u : H → K),
      ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) → (∀ t, ‖u t‖ ≤ 1) →
    ∀ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K, JetsIntegral sg →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (mvExp ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
              MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) * sg)‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
def SizesB : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (TT : Finset H) (c wt wt' : H → ℝ) (f k b b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b → 0 ≤ b' →
    (∀ t, t ∉ TT → c t ≤ 4 * k * b') → (∀ t, t ∈ TT → c t ≤ 4 * k * b' + 2 * b) →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    (∑ t, c t) ≤ 2 * (TT.card : ℝ) * b + 2 * f * k * b' ∧
      |-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)| ≤ f * k * b'
end Formalism.DworkPowerSeriesWeights


