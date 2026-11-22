-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
-- name    : Formalism_GL3MeanSquares_ConcavityEquidistribution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:48:57.671148+00:00
-- url     : https://prove2.me/theorems/1edbe37a-952c-43cb-b242-8042aa56fdf3
-- title:
--   Concavity Equidistribution
-- statement:
--   Definitions and structural lemmas for Concavity Equidistribution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/ConcavityEquidistribution.lean

import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
noncomputable def mean {σ : Type} [Fintype σ] (F : σ → ℝ) : ℝ := (∑ s, F s) / (Fintype.card σ : ℝ)
noncomputable def topTerm (A logOm : ℝ) : ℝ := A * Real.log A - A - A * logOm
noncomputable def placeTerm {N : ℕ} (nu : Fin N → ℕ) (logOm : ℝ) : ℝ :=
  Real.log (hookF nu) - (∑ i, (nu i : ℝ)) * logOm
noncomputable def weylDim {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ univ.filter (fun j => i < j),
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
def Wnum {n : ℕ} (lam : Fin (n + 1) → ℤ) : ℤ := lam 0 - lam (Fin.last n) + n + 1
def degZ {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, lam i - ∑ i, nu i
noncomputable def MeanSquareTwistBound {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (logT : ℝ) : ℝ :=
  -(degZ lam nu : ℝ) * logT
    + 2 * (n : ℝ) * Real.log (Wnum lam : ℝ) * (∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ))
    + Real.log (weylDim lam)
def wt {k : ℕ} (lam : Fin k → ℤ) : ℤ := ∑ i, lam i
def plus {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : Fin (κ + 1) → ℤ := fun i => lam i - lam (Fin.last κ)
noncomputable def MeanSquareWeightBound {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : ℝ :=
  (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1)
    + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1)
structure Numbers (C₀ a b' L v logT logg eta S : ℝ) (k m t N : ℕ) : Prop where
  one_le_L : 1 ≤ L
  one_le_v : 1 ≤ v
  log_av : Real.log (a * v) ≤ L
  one_le_b' : 1 ≤ b'
  b'_le_a : b' ≤ a
  logT_nonneg : 0 ≤ logT
  logT_le : logT ≤ C₀ * m * L
  logg_nonneg : 0 ≤ logg
  logg_le : logg ≤ C₀ * L
  one_le_k : 1 ≤ k
  one_le_m : 1 ≤ m
  N_eq : N = k + m * (t + 1)
  eta_nonneg : 0 ≤ eta
  S_nonneg : 0 ≤ S
  small : S + eta + (m : ℝ) * t ≤ b'
  sq : (N : ℝ) ^ 2 * (L + logT) ≤ N * b'
  lin : (N : ℝ) * L + logT ≤ b'
  pow : (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b'
def Ms_arith : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, ∀ (f N : ℕ) (v T L logg R2 logh : ℝ),
    1 ≤ f → 1 ≤ N → 1 ≤ v → 1 ≤ T → 1 ≤ L → 0 ≤ logg →
    Real.log f ≤ L → Real.log N ≤ L → Real.log v ≤ L →
    R2 = C₀ * f * (N : ℝ) ^ 2 * v ^ 2 * T ^ 2 →
    logh ≤ (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) + 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2)
        + (f * N * Real.log T + C₀ * f * (N : ℝ) ^ 2 * logg) →
    logh ≤ C * f * (N : ℝ) ^ 2 * (L + Real.log T + logg)
def Ms_index : Prop :=
  ∀ (f N : ℕ) (y : Fin N → Fin f → ℝ) (R2 : ℝ), 1 ≤ f → (∀ c τ, 0 ≤ y c τ) →
    (∀ c, ∑ τ, y c τ ≤ R2) → (∏ τ, ∏ c, y c τ) ^ 2 ≤ R2 ^ (2 * f * N)
def Minkowski_div : Prop :=
  ∀ n p : ℕ, p.Prime → ∑ i ∈ range (n + 1), n / (p ^ i * (p - 1)) ≤ padicValNat p (2 * n).factorial
def Minkowski_log : Prop :=
  ∃ C : ℝ, ∀ M : ℕ, 2 ≤ M → Real.log ((4 * M).factorial : ℝ) ≤ C * M * Real.log M
def Weight_change : Prop :=
  ∀ (X X' V V' : Type) [Fintype X] [Fintype X'] [NormedAddCommGroup V] [NormedAddCommGroup V']
    (K : (X → V) → (X' → V')) (u : X → ℝ) (u' : X' → ℝ) (D B : ℝ), 1 ≤ D → 0 ≤ B →
    (∀ x, 1 / D ≤ u x ∧ u x ≤ 1) → (∀ x, 1 / D ≤ u' x ∧ u' x ≤ 1) →
    ((∀ φ, ∑ x, ‖K φ x‖ ^ 2 ≤ B * ∑ x, ‖φ x‖ ^ 2) →
      ∀ φ, ∑ x, u' x * ‖K φ x‖ ^ 2 ≤ (B * D) * ∑ x, u x * ‖φ x‖ ^ 2) ∧
    ((∀ φ, ∑ x, u' x * ‖K φ x‖ ^ 2 ≤ B * ∑ x, u x * ‖φ x‖ ^ 2) →
      ∀ φ, ∑ x, ‖K φ x‖ ^ 2 ≤ (B * D) * ∑ x, ‖φ x‖ ^ 2)
def SeparatedSetPackingBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Finset E)
    (r δ : ℝ), 0 < δ → 0 ≤ r → (∀ c ∈ s, ‖c‖ ≤ r) → (∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ Module.finrank ℝ E
def PackingCountBound : Prop :=
  ∀ (f g : ℕ) (u v : ℝ), 1 ≤ f → 0 < v → 0 ≤ u →
    (1 + 2 * Real.sqrt u / Real.sqrt (f / v)) ^ (2 * g) ≤ 2 ^ g * (1 + 4 * u * v) ^ g
def LayerCakeSumBound : Prop :=
  ∀ (Y : Type) (h : Y → ℝ) (g : ℕ) (v : ℝ), 0 ≤ v → (∀ y, 0 ≤ h y) →
    (∀ u : ℝ, 0 ≤ u → {y | h y ≤ u}.Finite ∧
      (({y | h y ≤ u}.ncard : ℕ) : ℝ) ≤ 2 ^ g * (1 + 4 * u * v) ^ g) →
    Summable (fun y => Real.exp (-Real.pi * h y)) ∧
    ∑' y, Real.exp (-Real.pi * h y) ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g ∧
    2 ^ g * ∑' y, Real.exp (-Real.pi * h y) ≤ 4 ^ g * (2 + 8 * g * v) ^ g
def FockMonomialOrthogonality : Prop :=
  ∀ (Om : ℝ) (p q : ℕ), 0 < Om →
    MeasureTheory.Integrable
      (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ)) ∧
    ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
      if p = q then (((p.factorial : ℝ) * Om ^ p * (Real.pi * Om) : ℝ) : ℂ) else 0
def JetsProductBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (g₀ : ℕ) (Th S2 : ℝ), 1 ≤ g₀ → 0 ≤ S2 →
    Th * ∏ τ, ((1 + (if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ))) ^ (n τ + g₀))⁻¹
      ≤ S2 * ∏ τ, ((if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ)) ^ g₀)⁻¹ →
    Th ≤ S2 * ∏ τ, (2 * Real.exp 1 * max 1 ((n τ : ℝ) / g₀)) ^ g₀
def BlockOperatorNormBound : Prop :=
  ∀ (X X' V V' : Type) [Fintype X] [Fintype X'] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (A : X' → X → V →L[ℂ] V') (φ : X → V) (β : ℝ),
    (∀ x' x, ‖A x' x‖ ^ 2 ≤ β) →
    ∑ x', ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x', ∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 ∧
    ∑ x', ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ ((Fintype.card X' : ℝ) * Fintype.card X * β) * ∑ x, ‖φ x‖ ^ 2
def ZetaValueArithmetic : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] (N N' m : ℕ) (n : ι → ℕ)
    (logHook logOm : ι → ℝ) (v L logT logg logK logh logh' lev logBlock logThn logS2 logTh : ℝ),
    1 ≤ Fintype.card ι → 1 ≤ N → N ≤ N' → 1 ≤ m → 1 ≤ v → 1 ≤ L → 0 ≤ logT → 0 ≤ logg →
    Real.log (Fintype.card ι) ≤ L → Real.log N' ≤ L → Real.log v ≤ L →
    (∀ τ, Real.log (max 1 ((n τ : ℝ) / ((N : ℝ) * N'))) ≤ C₀ * L) →
    logK ≤ logh + logh' + lev + logBlock →
    logh ≤ C₀ * Fintype.card ι * (N' : ℝ) ^ 2 * (L + logT + logg) →
    logh' ≤ C₀ * Fintype.card ι * (N' : ℝ) ^ 2 * (L + logT + logg) →
    lev ≤ C₀ * Fintype.card ι * N' * Real.log ((Fintype.card ι : ℝ) * N')
        + C₀ * Fintype.card ι * N' * logT
        + C₀ * Fintype.card ι * ((m : ℝ) ^ 2 * N + (N : ℝ) * N') * logg →
    logBlock ≤ ∑ τ, (logHook τ - n τ * logOm τ) + logThn →
    logThn ≤ logS2 + ∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N'))) →
    logS2 ≤ ((Fintype.card ι : ℝ) * N * N') * Real.log 4
        + ((Fintype.card ι : ℝ) * N * N') * Real.log (2 + 8 * ((Fintype.card ι : ℝ) * N * N') * v) + logTh →
    logK ≤ ∑ τ, (logHook τ - n τ * logOm τ) + logTh
        + C * Fintype.card ι * (m : ℝ) ^ 2 * (N' : ℝ) ^ 2 * (L + logT + logg)
def hookLen {N : ℕ} (nu : Fin N → ℕ) (i : Fin N) (j : ℕ) : ℕ :=
  (nu i - j) + (univ.filter (fun i' : Fin N => i < i' ∧ j < nu i')).card
def hookProd {N : ℕ} (nu : Fin N → ℕ) : ℕ := ∏ i, ∏ j ∈ range (nu i), hookLen nu i j
def HookLengthFormula : Prop :=
  ∀ (N : ℕ) (nu : Fin N → ℕ), Antitone nu → (hookProd nu : ℝ) = hookF nu
def LargestPlaceHookBound : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (R : ℕ) (nu : Fin (R + 1) → ℕ) (A w : ℕ) (a b' L logOm : ℝ),
    Antitone nu → nu 0 = A + w → (w : ℝ) ≤ 2 * b' → (∀ i, i ≠ 0 → (nu i : ℝ) ≤ (2 + C₀) * b') →
    a ≤ A → (A : ℝ) ≤ 2 * a → 1 ≤ b' → b' ≤ a → 1 ≤ L → Real.log a ≤ L → (R : ℝ) + 1 ≤ b' →
    |logOm| ≤ C₀ * L →
    |placeTerm nu logOm - topTerm A logOm| ≤ C * ((R : ℝ) + 1) * b' * L
def ThinPlaceHookBound : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (R : ℕ) (nu : Fin (R + 1) → ℕ) (b' L logOm : ℝ),
    Antitone nu → (∀ i, (nu i : ℝ) ≤ (2 + C₀) * b') → 1 ≤ b' → 1 ≤ L → Real.log b' ≤ L → (R : ℝ) + 1 ≤ b' →
    |logOm| ≤ C₀ * L →
    |placeTerm nu logOm| ≤ C * ((R : ℝ) + 1) * b' * L
def Sqm_from : Prop :=
  ∀ (C₀ L logT logg b' : ℝ) (m N : ℕ), 0 ≤ C₀ → 1 ≤ L → 1 ≤ m → logT ≤ C₀ * m * L → logg ≤ C₀ * L →
    (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b' →
    (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ N * b' * L
def MeanLogNormBound : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [Nonempty σ]
    (TT T2 : Finset ι) (R N m : ℕ) (nu : ι → Fin (R + 1) → ℕ) (A w : ι → ℕ)
    (a b' L logT logg logOm : ℝ) (logOms : ι → σ → ℝ) (logTh logK : σ → ℝ),
    Disjoint TT T2 → R + 1 ≤ N → 1 ≤ L → Real.log a ≤ L → 1 ≤ b' → b' ≤ a → (N : ℝ) * L ≤ b' →
    0 ≤ logT → 0 ≤ logg → (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ N * b' * L →
    (∀ τ, Antitone (nu τ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ (A τ : ℝ) ≤ 2 * a ∧ nu τ 0 = A τ + w τ ∧ (w τ : ℝ) ≤ 2 * b' ∧
      ∀ i, i ≠ 0 → (nu τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ τ, τ ∉ TT → τ ∉ T2 → ∀ i, (nu τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ τ, mean (logOms τ) = logOm) → |logOm| ≤ C₀ * L →
    mean logTh ≤ C₀ * Fintype.card ι * (N : ℝ) ^ 2 * L →
    (∀ s, logK s ≤ ∑ τ, placeTerm (nu τ) (logOms τ s) + logTh s
        + C₀ * Fintype.card ι * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) →
    mean logK ≤ ∑ τ ∈ TT, topTerm (A τ) logOm + ∑ τ ∈ T2, placeTerm (nu τ) logOm
        + C * Fintype.card ι * N * b' * L
def DegreeEqHeadMinusBalance : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ), degZ lam nu = lam 0 - B0 lam nu
def WeylDimensionBounds : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam →
    1 ≤ weylDim lam ∧ Real.log (weylDim lam) ≤ ((n : ℝ) + 1) ^ 2 * Real.log (Wnum lam : ℝ)
def CoordinatesBoundedByBalance : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (X : Finset (Fin n)), Interlace lam nu →
    ∑ i, min (len lam i) (B0 lam nu) ≤ X.card * B0 lam nu + ∑ i ∈ Xᶜ, len lam i
def InjectiveReindexNormLe : Prop :=
  ∀ (X X' V V' : Type) [Fintype X] [Fintype X'] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (e : X' → X) (P : V →L[ℂ] V') (φ : X → V),
    Function.Injective e → ∑ x', ‖P (φ (e x'))‖ ^ 2 ≤ ‖P‖ ^ 2 * ∑ x, ‖φ x‖ ^ 2
def ZetaBoundApplication : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (n : ℕ)
    (lam : ι → Fin (n + 1) → ℤ) (sg : ι → Fin n → ℤ) (A bt : ι → ℝ)
    (b' L logT eta S mt logP : ℝ),
    1 ≤ L → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt →
    (∀ ρ, Interlace (lam ρ) (sg ρ)) → (∀ ρ, Real.log (Wnum (lam ρ) : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b') →
    (∀ ρ ∈ TT, (B0 (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (B0 (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin n), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, A ρ - bt ρ - C₀ * (S + eta + mt) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * mt ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + C * TT.card * b' * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * ((n : ℝ) + 1) ^ 2 * L
def OrthogonalMinorBound : Prop :=
  ∀ (r n : ℕ) (A : Matrix (Fin r) (Fin n) ℂ) (d : Fin n → ℝ) (e : Fin r → Fin n),
    (∀ i, 0 < d i) → Function.Injective e →
    ‖(A.submatrix id e).det‖ ^ 2 * ∏ i, d (e i)
      ≤ (A * Matrix.diagonal (fun i => (d i : ℂ)) * A.conjTranspose).det.re
def AmGmSumLowerBound : Prop :=
  ∀ (f : ℕ) (v : ℝ) (x : Fin f → ℝ), 1 ≤ f → 0 < v → (∀ i, 0 < x i) →
    ((2 * v) ^ (2 * f))⁻¹ ≤ ∏ i, x i → (f : ℝ) / (2 * v) ^ 2 ≤ ∑ i, x i
def LastMinimumSqBoundOfProductBound : Prop :=
  ∀ (f k : ℕ) (v l1 ln : ℝ), 1 ≤ f → 0 < v → 0 ≤ l1 → 0 ≤ ln → ln * l1 ≤ 2 * f * k →
    (f : ℝ) / (2 * v) ^ 2 ≤ l1 ^ 2 → ln ^ 2 ≤ 16 * f * (k : ℝ) ^ 2 * v ^ 2
def ConcavityEquidistribution : Prop :=
  ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [Nonempty σ] (π : σ → ι) (c : ℕ)
    (y : ι → ℝ) (B : ℝ), (∀ τ, (univ.filter (fun s => π s = τ)).card = c) → (∀ τ, 0 < y τ) →
    ∑ τ, y τ ≤ B → mean (fun s => Real.log (y (π s))) ≤ Real.log (B / Fintype.card ι)
def LastColumnBound : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1 + 1) → ℤ) (A bt S : ℤ), 0 ≤ bt → 0 ≤ S →
    lam 0 = A → lam (Fin.last (κ + 1)) = -bt →
    (∀ i, i ≠ 0 → i ≠ Fin.last (κ + 1) → 0 ≤ lam i ∧ lam i ≤ S) →
    wt lam ≤ A + (κ + 2) * S ∧ wt (plus lam) ≤ A + (κ + 2) * (bt + S)
def PropZ_i : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [Nonempty σ]
    (TT T2 : Finset ι) (k m t n : ℕ) (R : Fin m → ℕ)
    (nu : ∀ j : Fin m, ι → Fin (R j + 1) → ℕ) (A : ι → ℕ) (w : Fin m → ι → ℕ) (bt : ι → ℝ)
    (lam : ι → Fin (n + 1) → ℤ) (sg : ι → Fin n → ℤ)
    (a b' L v logT logg eta S logOm : ℝ) (logOms : ι → σ → ℝ) (logTh logK : Fin m → σ → ℝ)
    (logP logPK : σ → ℝ),
    Numbers C₀ a b' L v logT logg eta S k m t (n + 1) →
    Disjoint TT T2 → (∀ j, R j + 1 ≤ n + 1) → (∀ j τ, Antitone (nu j τ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ (A τ : ℝ) ≤ 2 * a ∧ bt τ ≤ 2 * b') →
    (∀ j, ∀ τ ∈ TT, nu j τ 0 = A τ + w j τ ∧ (w j τ : ℝ) ≤ 2 * b' ∧
      ∀ i, i ≠ 0 → (nu j τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ j τ, τ ∉ TT → τ ∉ T2 → ∀ i, (nu j τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ τ, mean (logOms τ) = logOm) → |logOm| ≤ C₀ * L →
    (∀ j, mean (logTh j) ≤ C₀ * Fintype.card ι * ((n : ℝ) + 1) ^ 2 * L) →
    (∀ j s, logK j s ≤ ∑ τ, placeTerm (nu j τ) (logOms τ s) + logTh j s
        + C₀ * Fintype.card ι * (m : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 * (L + logT + logg)) →
    (∀ ρ, Interlace (lam ρ) (sg ρ)) → (∀ ρ, Real.log (Wnum (lam ρ) : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, (B0 (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (B0 (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin n), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, (A ρ : ℝ) - bt ρ - C₀ * (S + eta + (m : ℝ) * t) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * ((m : ℝ) * t) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ s, logP s ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT) →
    (∀ s, logPK s ≤ logP s + ∑ j, logK j s) →
    mean logPK ≤ ∑ _j : Fin m, ∑ τ ∈ TT, topTerm (A τ) logOm - (∑ τ ∈ TT, (A τ : ℝ)) * logT
        + ∑ j : Fin m, ∑ τ ∈ T2, placeTerm (nu j τ) logOm
        + C * Fintype.card ι * m * ((n : ℝ) + 1) * b' * L
def PropZ_ii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muM : ℝ) (muV : X → ℝ) (muDelta muNabla muMaxNabla : ι → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (lam τ) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * S) →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → (wt (lam ρ) : ℝ) ≤ C₀ * ((κ : ℝ) + 1) * S) →
    muM = mean muV →
    (∀ c, muV c = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ : ℝ) + 1) * logT) + ∑ ρ, muDelta ρ) →
    (∀ ρ, muDelta ρ = -muNabla ρ) → (∀ ρ, muNabla ρ ≤ muMaxNabla ρ) →
    (∀ ρ, muMaxNabla ρ ≤ MeanSquareWeightBound (lam ρ)) →
    -(∑ τ ∈ TT, A τ / ((κ : ℝ) + 1) * logT) - C * TT.card * a * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * ((κ : ℝ) + 1) * (b' + S) * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * S * logT - C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L ≤ muM
def PropZ_iii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muMaxM : ℝ) (muMaxV : X → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ τ ∈ TT, |(lam τ (Fin.last κ) : ℝ)| ≤ bt τ) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → |(lam ρ (Fin.last κ) : ℝ)| ≤ C₀ * S) →
    (∃ c, muMaxM ≤ muMaxV c) →
    (∀ c, muMaxV c ≤ ∑ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT)) →
    muMaxM ≤ C * TT.card * a * Real.log (((κ : ℝ) + 1) * v)
        + C * Fintype.card ι * (b' + S) * (((κ : ℝ) + 1) * Real.log (((κ : ℝ) + 1) * v) + logT)
        + C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L
def PropZ_tail : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (f nT k m t N : ℕ) (x b a b' L v logT logg eta S sA : ℝ),
    Numbers C₀ a b' L v logT logg eta S k m t N → 0 < b → a = x * b → 1 ≤ nT → nT ≤ f →
    0 ≤ sA → sA ≤ 2 * a * nT →
    (sA / k * logT + nT * a * Real.log k + f * k * (b' + S) * Real.log k + f * S * logT
        + f * (k : ℝ) ^ 2 * L
        + (nT * a * Real.log (k * v) + f * (b' + S) * (k * Real.log (k * v) + logT)
          + f * (k : ℝ) ^ 2 * L)
        + f * m * N * b' * L) / (nT * m * b)
      ≤ C * (x * L / m + x * L / k + f * N * b' * L / (nT * b))
end Formalism.HermitianLattices.TraceIntegrality


