-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
-- name    : Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:40.789253+00:00
-- url     : https://prove2.me/theorems/54432509-980d-4fec-b836-c501b924b8cc
-- title:
--   Integral Multiple Norm Lower Bound
-- statement:
--   Definitions and structural lemmas for Integral Multiple Norm Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/IntegralMultipleNormLowerBound.lean

import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len Iset ev sep)
open scoped NumberField
def Field_sizes : Prop :=
  ∀ (e : ℕ) (q₁ d v : ℝ), 3 ≤ q₁ → 7 ≤ d → 0 < v →
    (2 * v) ^ 2 = 4 * ((2 : ℝ) ^ e) ^ 2 * (2 : ℝ) ^ (-2 / (2 : ℝ) ^ e) * q₁ * d →
    4 * (2 : ℝ) ^ e ≤ (2 * v) ^ 2 ∧ 2 ≤ v
def T_ideal_norm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : K),
    x ∈ I → x ≠ 0 → FractionalIdeal.absNorm I ≤ |Algebra.norm ℚ x|
def T_amgm : Prop :=
  ∀ (f : ℕ) (A v : ℝ) (x : Fin f → ℝ), 1 ≤ f → 0 < A → 0 < v → (∀ i, 0 < x i) →
    (A ^ (2 * f) * (2 * v) ^ (4 * f))⁻¹ ≤ (∏ i, x i) ^ 2 → (A * (2 * v) ^ 2)⁻¹ ≤ (∑ i, x i) / f
def T_arith : Prop :=
  ∀ (f n : ℕ) (A v l1 ld : ℝ), 1 ≤ f → 0 < A → 0 < v → 0 ≤ l1 → 0 ≤ ld → ld * l1 ≤ 2 * f * n →
    2 * (f : ℝ) / (A * (2 * v) ^ 2) ≤ l1 ^ 2 → ld ^ 2 ≤ 2 * f * (n : ℝ) ^ 2 * A * (2 * v) ^ 2
def Ms_count_mean : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ρ : ℝ), 0 ≤ ρ →
    {x : 𝓞 K | (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (Module.finrank ℚ K : ℝ) ≤ ρ}.Finite ∧
    (({x : 𝓞 K | (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (Module.finrank ℚ K : ℝ) ≤ ρ}.ncard : ℕ) : ℝ)
      ≤ (2 * ρ + 1) ^ Module.finrank ℚ K
def Ms_index_mean : Prop :=
  ∀ (f n : ℕ) (y : Fin n → Fin f → ℝ) (ρ₀ : ℝ), 1 ≤ f → (∀ c τ, 0 ≤ y c τ) →
    (∀ c, (∑ τ, y c τ) / f ≤ ρ₀) → (∏ τ, ∏ c, y c τ) ^ 2 ≤ ρ₀ ^ (2 * f * n)
def Ms_fibres : Prop :=
  ∀ (G : Type) [Group G] (Γ K U : Subgroup G), U ≤ K → U.relIndex K ≠ 0 →
    Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) →
    Finite (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) ∧
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (U : Set G))
      ≤ U.relIndex K * Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
def Ms_GL_card : Prop :=
  ∀ (n p : ℕ) [Fact p.Prime], Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) ≤ p ^ (n ^ 2)
def Ms_explicit : Prop :=
  ∀ (f n N : ℕ) (v T LL logg ρ₀ logh : ℝ), 1 ≤ f → 1 ≤ n → n ≤ N → 1 ≤ 2 * v → 1 ≤ T → 0 ≤ logg →
    Real.log 3 ≤ LL → Real.log n ≤ LL → Real.log (2 * v) ≤ LL → ρ₀ = (n : ℝ) ^ 2 * T * (2 * v) ^ 2 →
    logh ≤ 2 * f * (n : ℝ) ^ 2 * Real.log (2 * ρ₀ + 1) + 2 * f * n * ((n : ℝ) + 1) * Real.log ρ₀
        + (f * n * Real.log T + f * (n : ℝ) ^ 2 * logg) →
    logh ≤ f * (N : ℝ) ^ 2 * (30 * LL + 7 * Real.log T + logg)
def M_log_explicit : Prop :=
  ∀ (f N : ℕ) (LL : ℝ), 1 ≤ f → 1 ≤ N → Real.log 4 ≤ 2 * LL → Real.log f ≤ 2 * LL → Real.log N ≤ LL →
    Real.log ((4 * f * N).factorial : ℝ) ≤ 4 * f * N * Real.log (4 * f * N) ∧
    4 * (f : ℝ) * N * Real.log (4 * f * N) ≤ 20 * f * N * LL
def TranslateNormIdentity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (Th : E → ℂ) (x z : E),
    ‖Th (z - x) * Complex.exp ((Real.pi : ℂ) * inner ℂ x z - (Real.pi : ℂ) * ((‖x‖ ^ 2 / 2 : ℝ) : ℂ))‖ ^ 2
        * Real.exp (-Real.pi * ‖z‖ ^ 2)
      = ‖Th (z - x)‖ ^ 2 * Real.exp (-Real.pi * ‖z - x‖ ^ 2)
def GaussianLatticeSumShiftLe : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (w : E),
    Summable (fun y : Λ => Real.exp (-Real.pi * ‖w + (y : E)‖ ^ 2)) ∧
    ∑' y : Λ, Real.exp (-Real.pi * ‖w + (y : E)‖ ^ 2) ≤ ∑' y : Λ, Real.exp (-Real.pi * ‖(y : E)‖ ^ 2)
def PeriodicUnfolding : Prop :=
  ∀ (E : Type) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] (μ : MeasureTheory.Measure E)
    [μ.IsAddLeftInvariant] (Λ : AddSubgroup E) [Countable Λ] (D : Set E) (φ g : E → ENNReal),
    MeasureTheory.IsAddFundamentalDomain Λ D μ → Measurable φ → Measurable g →
    (∀ (y : Λ) (u : E), φ ((y : E) + u) = φ u) →
    ∫⁻ w, φ w * g w ∂μ = ∫⁻ u in D, φ u * ∑' y : Λ, g ((y : E) + u) ∂μ
def FockMonomialOrthogonalityMulti : Prop :=
  ∀ (G : ℕ) (Om : Fin G → ℝ) (p q : Fin G → ℕ), (∀ i, 0 < Om i) →
    MeasureTheory.Integrable (fun z : Fin G → ℂ =>
      (∏ i, (z i ^ p i * (starRingEnd ℂ (z i)) ^ q i)) * (Real.exp (-∑ i, ‖z i‖ ^ 2 / Om i) : ℂ)) ∧
    ∫ z : Fin G → ℂ,
      (∏ i, (z i ^ p i * (starRingEnd ℂ (z i)) ^ q i)) * (Real.exp (-∑ i, ‖z i‖ ^ 2 / Om i) : ℂ) =
      if p = q then ((∏ i, (((p i).factorial : ℝ) * Om i ^ p i * (Real.pi * Om i)) : ℝ) : ℂ) else 0
def ParsevalOneVariable : Prop :=
  ∀ (F : ℂ → ℂ) (Om : ℝ), Differentiable ℂ F → 0 < Om →
    ∫⁻ z : ℂ, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2 / Om)) =
      ∑' n : ℕ, ENNReal.ofReal (‖iteratedDeriv n F 0 / (n.factorial : ℂ)‖ ^ 2
        * ((n.factorial : ℝ) * Om ^ n * (Real.pi * Om)))
def ParsevalSeveralVariables : Prop :=
  ∀ (G : ℕ) (F : (Fin G → ℂ) → ℂ) (c : (Fin G →₀ ℕ) → ℂ) (Om : Fin G → ℝ), (∀ i, 0 < Om i) →
    (∀ z, HasSum (fun e : Fin G →₀ ℕ => c e * ∏ i, z i ^ e i) (F z)) →
    ∫⁻ z : Fin G → ℂ, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-∑ i, ‖z i‖ ^ 2 / Om i)) =
      ∑' e : Fin G →₀ ℕ, ENNReal.ofReal (‖c e‖ ^ 2 * ∏ i, (((e i).factorial : ℝ) * Om i ^ e i * (Real.pi * Om i)))
def MultinomialExpTermSum : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (n : ℕ),
    ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset ι) n, ∏ i, (x i ^ e i / ((e i).factorial : ℂ))
      = (∑ i, x i) ^ n / (n.factorial : ℂ)
def ParsevalFrame : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ε] (U : ι → ε → ℂ) (P : ε → ℂ) (J : Finset ι),
    (∀ e e', ∑ I, U I e * starRingEnd ℂ (U I e') = if e = e' then 1 else 0) →
    ∑ I, ‖∑ e, P e * starRingEnd ℂ (U I e)‖ ^ 2 = ∑ e, ‖P e‖ ^ 2 ∧
    ∑ I ∈ J, ‖∑ e, P e * starRingEnd ℂ (U I e)‖ ^ 2 ≤ ∑ e, ‖P e‖ ^ 2
def SupJetsExcessBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q N : ℕ) (n : ι → ℕ) (a v LL : ℝ), 1 ≤ Fintype.card ι → 1 ≤ p → 1 ≤ q →
    p ≤ N → q ≤ N → 1 ≤ v → 1 ≤ a → 2 ≤ LL → Real.log (Fintype.card ι) ≤ 2 * LL → Real.log N ≤ LL →
    Real.log v ≤ LL → Real.log (3 * a) ≤ 2 * LL → (∀ τ, (n τ : ℝ) / ((p : ℝ) * q) ≤ 3 * a) →
    ((Fintype.card ι : ℝ) * p * q) * Real.log 4
      + ((Fintype.card ι : ℝ) * p * q) * Real.log (1 + 4 * ((Fintype.card ι : ℝ) * p * q) * v / Real.pi)
      + ((p : ℝ) * q) * ∑ τ, Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((p : ℝ) * q)))
      ≤ 12 * ((Fintype.card ι : ℝ) * p * q) * LL
def WeightedBlockNormBound : Prop :=
  ∀ (X X' V V' : Type) [Fintype X] [Fintype X'] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (A : X' → X → V →L[ℂ] V') (φ : X → V)
    (u : X → ℝ) (u' : X' → ℝ) (c β : ℝ),
    (∀ x, 0 < u x ∧ u x ≤ 1) → (∀ x, 0 < u' x ∧ u' x ≤ 1) → (∀ x' x, ‖A x' x‖ ^ 2 ≤ β) →
    ∑ x', u' x' * ‖(c : ℂ) • ∑ x, (u x : ℂ) • A x' x (φ x)‖ ^ 2
      ≤ (c ^ 2 * (Fintype.card X : ℝ) * Fintype.card X' * β) * ∑ x, u x * ‖φ x‖ ^ 2
def FourierL1Bound : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (Ψ : A → ℂ), (∀ x, ‖Ψ x‖ ≤ 1) →
    (∑ ψ : AddChar A ℂ, ‖∑ x, Ψ x * starRingEnd ℂ (ψ x)‖) / (Fintype.card A : ℝ)
      ≤ Real.sqrt (Fintype.card A)
def Dat_fourier_inv : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (Ψ : A → ℂ) (x : A),
    Ψ x = (Fintype.card A : ℂ)⁻¹ * ∑ ψ : AddChar A ℂ, (∑ y, Ψ y * starRingEnd ℂ (ψ y)) * ψ x
def wG (K s : ℕ) (e : ℕ → ℤ) (j : ℕ) : ℤ := e j - K - (2 * j + 1) * (s + 1)
def colW (K : ℕ) (U : ℕ → ℤ) {k : ℕ} : Fin k → ℤ := fun i => U i - K + i + 1
def nuRow (K s : ℕ) (U e : ℕ → ℤ) (j i : ℕ) : ℤ :=
  if i < 2 * K then (U i - K + i + 1) + wG K s e j else wG K s e j - wG K s e ((i - 2 * K) / (2 * s + 2))
def TwistExponentIdentities : Prop :=
  ∀ (k t i j c q e lam : ℚ),
    (-e + t / 2 - c) - (k + 1) / 2 + (k + (i - 1) * (t + 1) + 1 + c)
      = -(e - k / 2 - (2 * i - 1) * (t + 1) / 2) ∧
    lam - (j - 1) * (t + 1) / 2 + e - (k + j * (t + 1)) / 2
      = lam + (e - k / 2 - (2 * j - 1) * (t + 1) / 2) ∧
    -(e - (k + (j - 1) * (t + 1)) / 2) + ((k + j * (t + 1)) + 1) / 2 - ((k + (j - 1) * (t + 1)) + 1 + q)
      = -e + t / 2 - q
def LayoutGapBounds : Prop :=
  ∀ (K m s : ℕ) (b e : ℕ → ℤ), (∀ j, j < m → (s : ℤ) + 2 ≤ e j - b j) →
    (∀ j, j + 1 < m → (s : ℤ) + 2 ≤ b (j + 1) - e j) →
    ∀ i j, i ≤ j → j < m →
      ((j : ℤ) - i) * (2 * s + 4) ≤ e j - e i ∧ wG K s e i ≤ wG K s e j
def IsPartitionOfLayout : Prop :=
  ∀ (K m s : ℕ) (U b e : ℕ → ℤ), 1 ≤ K → (∀ i, i + 1 < 2 * K → U (i + 1) < U i) →
    (∀ j, j < m → (s : ℤ) + 2 ≤ e j - b j) → (∀ j, j + 1 < m → (s : ℤ) + 2 ≤ b (j + 1) - e j) →
    0 ≤ (U (2 * K - 1) + K) + wG K s e 0 →
    ∀ j, j < m → ∀ i i', i ≤ i' → i' < 2 * K + j * (2 * s + 2) →
      nuRow K s U e j i' ≤ nuRow K s U e j i ∧ 0 ≤ nuRow K s U e j i'
def MaximalWidthBound : Prop :=
  ∀ (x b' bt eta S mt w : ℝ), 3 ≤ x → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt → bt ≤ b' * (1 + (x ^ 2)⁻¹) →
    w ≤ bt + b' / x + eta → S + eta + mt ≤ b' / x → w ≤ 2 * b' ∧ S + w ≤ 2 * b'
def Stirling_elem : Prop :=
  ∀ M : ℕ, 1 ≤ M → ((M : ℝ) / Real.exp 1) ^ M ≤ (M.factorial : ℝ) ∧
    (M.factorial : ℝ) ≤ Real.exp 1 * M * ((M : ℝ) / Real.exp 1) ^ M
def MaximalPlaceHookExplicit : Prop :=
  ∀ (C₃ : ℝ) (R N : ℕ) (nu : Fin (R + 1) → ℕ) (A w : ℕ) (a b' LL logOm : ℝ), 0 ≤ C₃ →
    Antitone nu → nu 0 = A + w → (w : ℝ) ≤ 2 * b' → (∀ i, i ≠ 0 → (nu i : ℝ) ≤ 2 * b') →
    a ≤ A → (A : ℝ) + 3 * b' ≤ 3 * a → R + 1 ≤ N → (N : ℝ) ≤ b' → 3 ≤ b' → 1 ≤ LL →
    Real.log (3 * a) ≤ 2 * LL → |logOm| ≤ C₃ * LL →
    |placeTerm nu logOm - topTerm A logOm| ≤ (7 + 2 * C₃) * N * b' * LL
def ThinPlaceHookExplicit : Prop :=
  ∀ (C₃ : ℝ) (R N : ℕ) (nu : Fin (R + 1) → ℕ) (a b' LL logOm : ℝ), 0 ≤ C₃ →
    Antitone nu → (∀ i, (nu i : ℝ) ≤ b') → R + 1 ≤ N → (N : ℝ) ≤ b' → 2 * b' ≤ 3 * a → 1 ≤ LL →
    Real.log (3 * a) ≤ 2 * LL → |logOm| ≤ C₃ * LL →
    |placeTerm nu logOm| ≤ (4 + 2 * C₃) * N * b' * LL
noncomputable def sepP {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu nu' : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ y ∈ Ioc (nu i) (lam i.succ + min (len lam i) (B0 lam nu)), ev nu' (y - (i : ℤ))
noncomputable def sepM {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu nu' : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ y ∈ Ico (lam i.succ) (nu i), ev nu' (y - (i : ℤ))
def SeparantFactorization : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ), Interlace lam nu →
    (∀ nu' : Fin n → ℤ, sep lam nu nu' = sepP lam nu nu' * sepM lam nu nu') ∧
    sepP lam nu nu ≠ 0 ∧ sepM lam nu nu ≠ 0 ∧
    |sepM lam nu nu| ≤ (Wnum lam) ^ (n * (B0 lam nu).toNat) ∧
    (∀ nu' : Fin n → ℤ, Interlace lam nu' → B0 lam nu' = B0 lam nu → nu' ≠ nu →
      sepP lam nu nu' = 0 ∧ sepM lam nu nu' = 0)
def IntegralMultipleNormLowerBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) (c z : ℤ),
    (c : ℂ) • x ≠ 0 → ‖(c : ℂ) • x‖ ^ 2 = (z : ℝ) → 1 / ‖x‖ ≤ |(c : ℝ)|
def InterlacingLogDegreeBound : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (T c cA kap : ℝ), Interlace lam nu → 1 ≤ T →
    c ≠ 0 → c ^ 2 ≤ |cA| → |cA| ≤ (Wnum lam : ℝ) ^ (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) →
    0 < kap → kap ≤ |c| →
    Real.log (T ^ (-(degZ lam nu)) * (c * kap) ^ 2) ≤ MeanSquareTwistBound lam nu (Real.log T) - Real.log (weylDim lam)
def GapSumTelescoping : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (b : Fin n),
    (nu b - lam b.succ) + ∑ i ∈ univ.filter (fun i => b < i), ((nu i - lam i.succ) + (lam i.castSucc - nu i))
      + lam (Fin.last n) = nu b
def IntegerMultipleBoundTransfer : Prop :=
  ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (P₀ : V →L[ℂ] V') (a : ℤ), a ≠ 0 → ‖P₀‖ ≤ ‖(a : ℂ) • P₀‖
def parL (k s : ℕ) (U e : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i < k then U i else -e ((i - k) / (2 * s + 2)) + s - (((i - k) % (2 * s + 2) : ℕ) : ℤ)
def parR (k s : ℕ) (v b e : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i + 1 < k then v i
  else if (i + 1 - k) % (2 * s + 2) = 0 then -b ((i + 1 - k) / (2 * s + 2))
  else -e ((i + 1 - k) / (2 * s + 2)) + s + 1 - (((i + 1 - k) % (2 * s + 2) : ℕ) : ℤ)
def lamT (k s : ℕ) (U e : ℕ → ℤ) (h : ℤ) {n : ℕ} : Fin (n + 1) → ℤ := fun i => parL k s U e i - h + i + 1
def sgT (k s : ℕ) (v b e : ℕ → ℤ) (h : ℤ) {n : ℕ} : Fin n → ℤ := fun i => parR k s v b e i - h + i + 1
structure Layout (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) : Prop where
  one_le_K : 1 ≤ K
  one_le_m : 1 ≤ m
  chain : ∀ i, i + 1 < 2 * K → v i ≤ U i ∧ U (i + 1) + 1 ≤ v i
  last : -b 0 ≤ U (2 * K - 1)
  gap_eb : ∀ j, j < m → (s : ℤ) + 2 ≤ e j - b j
  gap_be : ∀ j, j + 1 < m → (s : ℤ) + 2 ≤ b (j + 1) - e j
  spread : e (m - 1) - b 0 ≤ eta
  cloud_v : ∀ i, i + 1 < 2 * K → 0 ≤ v i ∧ v i ≤ S
  cloud_u : ∀ i, 1 ≤ i → i + 1 < 2 * K → 0 ≤ U i ∧ U i + 1 ≤ S
def IsTop (K : ℕ) (U : ℕ → ℤ) (A bt : ℤ) : Prop := U 0 = A + K - 1 ∧ U (2 * K - 1) = -bt - K
def IsOff (K : ℕ) (U v : ℕ → ℤ) (S C₁ : ℤ) : Prop :=
  S ≤ U 0 - v 0 ∧ U 0 - v 0 + 1 ≤ C₁ * S ∧ U (2 * K - 1) = v (2 * K - 2) - 1 ∧ 2 * (K : ℤ) ≤ S
def LamTFormula : Prop :=
  ∀ (K m s n : ℕ) (U e : ℕ → ℤ) (h : ℤ), n + 1 = 2 * K + m * (2 * s + 2) →
    ∀ i : Fin (n + 1), lamT (2 * K) s U e h i =
      (if (i : ℕ) < 2 * K then U i - K + i + 1 else -wG K s e (((i : ℕ) - 2 * K) / (2 * s + 2))) + (K - h)
def Use_interlace : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta h : ℤ), Layout K m s U v b e S eta →
    n + 1 = 2 * K + m * (2 * s + 2) →
    Interlace (lamT (2 * K) s U e h (n := n)) (sgT (2 * K) s v b e h)
def BalanceFormula : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta h : ℤ), Layout K m s U v b e S eta →
    n + 1 = 2 * K + m * (2 * s + 2) →
    B0 (lamT (2 * K) s U e h (n := n)) (sgT (2 * K) s v b e h)
      = ∑ i ∈ range (2 * K - 1), (v i - U (i + 1) - 1) + ∑ j ∈ range m, (e j - b j - (s + 1))
def MaximalBalanceDegreeBounds : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta A bt : ℤ), Layout K m s U v b e S eta → IsTop K U A bt →
    n + 1 = 2 * K + m * (2 * s + 2) →
    bt ≤ B0 (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1))) ∧
    B0 (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1)))
      ≤ bt + S + eta ∧
    A - bt - S - eta - m * (s + 1)
      ≤ degZ (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1))) ∧
    degZ (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1)))
      ≤ A - bt - m * (s + 1)
def NonmaximalBalanceDegreeBounds : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta C₁ : ℤ), Layout K m s U v b e S eta → IsOff K U v S C₁ →
    n + 1 = 2 * K + m * (2 * s + 2) →
    0 ≤ B0 (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1))) ∧
    B0 (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1)))
      ≤ S + eta ∧
    -(S + eta) - m * (2 * s + 1)
      ≤ degZ (lamT (2 * K) s U e (K + m * (s + 1)) (n := n)) (sgT (2 * K) s v b e (K + m * (s + 1)))
def MaximalPositionCondition : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta A bt h : ℤ), Layout K m s U v b e S eta → IsTop K U A bt →
    n + 1 = 2 * K + m * (2 * s + 2) →
    (∃ X : Finset (Fin n), X.card ≤ 3 ∧ ∑ i ∈ Xᶜ, len (lamT (2 * K) s U e h (n := n)) i ≤ eta + S) ∧
    ∑ i, min (len (lamT (2 * K) s U e h (n := n)) i)
        (B0 (lamT (2 * K) s U e h (n := n)) (sgT (2 * K) s v b e h)) ≤ 3 * bt + 4 * S + 4 * eta
def LayoutOffLengthBounds : Prop :=
  ∀ (K m s n : ℕ) (U v b e : ℕ → ℤ) (S eta C₁ h : ℤ), Layout K m s U v b e S eta → IsOff K U v S C₁ →
    n + 1 = 2 * K + m * (2 * s + 2) →
    (∀ i : Fin n, (i : ℕ) = 0 → len (lamT (2 * K) s U e h (n := n)) i ≤ (C₁ + 1) * S) ∧
    (∃ X : Finset (Fin n), X.card ≤ 2 ∧ ∑ i ∈ Xᶜ, len (lamT (2 * K) s U e h (n := n)) i ≤ eta + S) ∧
    ∑ i, min (len (lamT (2 * K) s U e h (n := n)) i)
        (B0 (lamT (2 * K) s U e h (n := n)) (sgT (2 * K) s v b e h)) ≤ (C₁ + 3) * S + 2 * eta
def LayoutWeightSpreadFormula : Prop :=
  ∀ (K m s n : ℕ) (U e : ℕ → ℤ) (h : ℤ), 1 ≤ K → 1 ≤ m → n + 1 = 2 * K + m * (2 * s + 2) →
    Wnum (lamT (2 * K) s U e h (n := n)) = U 0 + e (m - 1) + s + 2
def MaximalWeightCondition : Prop :=
  ∀ (K s : ℕ) (U0 em A : ℤ) (a b' eta : ℝ), U0 = A + K - 1 → (A : ℝ) ≤ 2 * a → (em : ℝ) ≤ 3 * b' + eta →
    2 * (K : ℝ) + (2 * s + 1) + eta ≤ 3 * b' → 6 * b' ≤ a → ((U0 + em + s + 2 : ℤ) : ℝ) ≤ 3 * a
def Use_dim : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam →
    Real.log (weylDim lam) ≤ (((n : ℝ) + 1) * n / 2) * Real.log (Wnum lam : ℝ)
def Inj_norm : Prop :=
  ∀ (T hl : ℝ) (z : ℂ), 0 < T → 0 ≤ hl → 1 / T = hl + T * ‖(1 / T : ℝ) + z‖ ^ 2 →
    ‖1 + z * T‖ ≤ 1 ∧ (‖1 + z * T‖ = 1 → hl = 0)
def Inj_unit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (α : 𝓞 K) (T : ℕ), T.Prime → T ≠ 2 →
    (∀ φ : K →+* ℂ, ‖φ ((1 + α * (T : 𝓞 K) : 𝓞 K) : K)‖ ≤ 1) → α = 0
def FibreMultiplicityNormBound : Prop :=
  ∀ (X X' V V' : Type) [Fintype X] [DecidableEq X] [Fintype X'] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (e : X' → X) (P : V →L[ℂ] V') (φ : X → V) (Φ : ℕ),
    (∀ x, (univ.filter (fun x' => e x' = x)).card ≤ Φ) →
    ∑ x', ‖P (φ (e x'))‖ ^ 2 ≤ Φ * ‖P‖ ^ 2 * ∑ x, ‖φ x‖ ^ 2
def PropU_explicit : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (n : ℕ) (deg smin logW logdim A bt : ι → ℝ)
    (cP C₁ b' La logT eta S mt logP : ℝ), 0 ≤ cP → 0 ≤ C₁ → 0 ≤ La → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S →
    0 ≤ mt → (∀ ρ, 0 ≤ smin ρ) → (∀ ρ, logW ρ ≤ 2 * La) → (∀ ρ, logdim ρ ≤ (n : ℝ) ^ 2 * La) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b' ∧ A ρ - bt ρ - S - eta - mt ≤ deg ρ ∧ smin ρ ≤ 3 * bt ρ + 4 * S + 4 * eta) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - mt ≤ deg ρ ∧ smin ρ ≤ (C₁ + 3) * S + 2 * eta) →
    logP ≤ ∑ ρ, (-deg ρ * logT + cP * n * logW ρ * smin ρ + logdim ρ) →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + TT.card * (2 * b' * logT + 12 * cP * n * b' * La)
        + Fintype.card ι * (S + eta + mt) * logT
        + 2 * cP * Fintype.card ι * n * La * ((C₁ + 4) * S + 4 * eta) + Fintype.card ι * (n : ℝ) ^ 2 * La
def ExteriorPowerNormBound : Prop :=
  ∀ (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (Φ : V →ₗ[ℂ] V') (β : ℝ) (r : ℕ) (x : Fin r → V), 0 ≤ β →
    (∀ y, ‖Φ y‖ ≤ β * ‖y‖) →
    (Matrix.gram ℂ (fun i => Φ (x i))).det.re ≤ β ^ (2 * r) * (Matrix.gram ℂ x).det.re
def EmbeddingFibresEqual : Prop :=
  ∀ (E LL : Type) [Field E] [NumberField E] [Field LL] [NumberField LL] (ρ : E →+* LL) (τ : E →+* ℂ),
    Nat.card {s : LL →+* ℂ // s.comp ρ = τ} * Module.finrank ℚ E = Module.finrank ℚ LL
def LemC_bounds : Prop :=
  ∀ (N : ℕ) (nu : Fin (N + 1) → ℕ), Antitone nu →
    ∏ i, ((nu i).factorial : ℝ) ≤ hookF nu ∧
    hookF nu ≤ (∏ i, ((nu i).factorial : ℝ)) * ((nu 0 : ℝ) + N + 1) ^ ((N + 1) * N / 2)
def IntegralGramDetGeOne : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ), (G.map (fun z : ℤ => (z : ℝ))).PosDef → 1 ≤ G.det
def LogIndexCancellationIdentity : Prop :=
  ∀ (f : ℕ) (I T : ℝ), 1 ≤ f → 0 < I → 0 < T →
    -(1 / (2 * (f : ℝ))) * Real.log (I ^ 2 * T ^ (2 * f)) + (1 / (f : ℝ)) * Real.log (I * T ^ (2 * f))
      = Real.log T
def MeanLogExplicit : Prop :=
  ∀ (d k : ℕ) (h : Fin d → Fin k → ℝ) (v : ℝ), 1 ≤ d → 1 ≤ k → 0 < v → (∀ τ c, 0 < h τ c) →
    (∀ c, (∑ τ, h τ c) / d ≤ (k : ℝ) ^ 2 * (2 * v) ^ 2) →
    (∑ τ, Real.log (∑ c, h τ c)) / d ≤ Real.log ((k : ℝ) ^ 3 * (2 * v) ^ 2)
def AntitoneWeightLogBoundExplicit : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (v logT logB logc muB mu : ℝ), 2 ≤ v → Antitone lam →
    logB ≤ Real.log (4 * ((κ : ℝ) + 1) ^ 3 * v ^ 2) →
    logc ≤ (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus lam 0 : ℝ) + κ + 1) →
    muB ≤ (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1) →
    mu ≤ muB + (wt (plus lam) : ℝ) * logB + logc - (lam (Fin.last κ) : ℝ) * logT →
    mu ≤ (wt (plus lam) : ℝ) * (4 * Real.log (((κ : ℝ) + 1) * v))
        + (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus lam 0 : ℝ) + κ + 1) - (lam (Fin.last κ) : ℝ) * logT
def ColumnParameterMaximalCondition : Prop :=
  ∀ (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta A bt : ℤ), Layout K m s U v b e S eta → IsTop K U A bt →
    κ + 1 = 2 * K →
    Antitone (colW K U (k := κ + 1)) ∧ colW K U (k := κ + 1) 0 = A ∧
    colW K U (k := κ + 1) (Fin.last κ) = -bt ∧
    ∀ i : Fin (κ + 1), i ≠ 0 → i ≠ Fin.last κ → 0 ≤ colW K U i ∧ colW K U i ≤ S
def Col_param_off : Prop :=
  ∀ (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ), Layout K m s U v b e S eta → IsOff K U v S 2 →
    κ + 1 = 2 * K →
    Antitone (colW K U (k := κ + 1)) ∧
    (∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S) ∧
    (∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S) ∧
    wt (plus (colW K U (k := κ + 1))) ≤ (κ + 1 + 2) * S ∧
    0 ≤ wt (colW K U (k := κ + 1)) ∧ wt (colW K U (k := κ + 1)) ≤ 2 * (κ + 1) * S
def PropZ_ii_explicit : Prop :=
  ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X] (TT : Finset ι) (κ : ℕ)
    (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ) (a b' logT S muM : ℝ) (muV : X → ℝ) (muDelta : ι → ℝ),
    2 ≤ κ → 0 < a → 0 ≤ b' → 0 ≤ S → 0 ≤ logT → (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, A τ ≤ 2 * a ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (lam τ) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * S) →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → (wt (lam ρ) : ℝ) ≤ 2 * ((κ : ℝ) + 1) * S) →
    (∀ ρ, (plus (lam ρ) 0 : ℝ) + κ + 1 ≤ 4 * a) →
    muM = mean muV →
    (∀ c, muV c = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ : ℝ) + 1) * logT) + ∑ ρ, muDelta ρ) →
    (∀ ρ, -((wt (plus (lam ρ)) : ℝ) * Real.log ((κ : ℝ) + 1))
        - (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus (lam ρ) 0 : ℝ) + κ + 1) ≤ muDelta ρ) →
    -(∑ τ ∈ TT, A τ / ((κ : ℝ) + 1) * logT) - 2 * TT.card * a * Real.log ((κ : ℝ) + 1)
        - 2 * Fintype.card ι * ((κ : ℝ) + 1) * (b' + S) * Real.log ((κ : ℝ) + 1)
        - 2 * Fintype.card ι * S * logT
        - (1 / 2) * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * Real.log (4 * a) ≤ muM
def PropZ_iii_explicit : Prop :=
  ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X] (TT : Finset ι) (κ : ℕ)
    (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ) (a b' v logT S muMaxM : ℝ) (muMaxV : X → ℝ),
    2 ≤ κ → 0 < a → 0 ≤ b' → 0 ≤ S → 0 ≤ logT → 1 ≤ v → (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, A τ ≤ 2 * a ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ τ ∈ TT, -(lam τ (Fin.last κ) : ℝ) ≤ bt τ) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → 0 ≤ lam ρ (Fin.last κ)) →
    (∀ ρ, (plus (lam ρ) 0 : ℝ) + κ + 1 ≤ 4 * a) →
    (∃ c, muMaxM ≤ muMaxV c) →
    (∀ c, muMaxV c ≤ ∑ ρ, ((wt (plus (lam ρ)) : ℝ) * (4 * Real.log (((κ : ℝ) + 1) * v))
        + (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus (lam ρ) 0 : ℝ) + κ + 1)
        - (lam ρ (Fin.last κ) : ℝ) * logT)) →
    muMaxM ≤ 8 * TT.card * a * Real.log (((κ : ℝ) + 1) * v)
        + 8 * Fintype.card ι * ((κ : ℝ) + 1) * (b' + S) * Real.log (((κ : ℝ) + 1) * v)
        + 2 * TT.card * b' * logT + (1 / 2) * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * Real.log (4 * a)
end Formalism.HermitianLattices.ExplicitEstimates


