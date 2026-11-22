-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
-- name    : Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:52.560652+00:00
-- url     : https://prove2.me/theorems/c1812741-f85b-48d2-a9c2-8111cd67e3aa
-- title:
--   Rank Mul Pow Three Halves Le Fourth Power
-- statement:
--   Definitions and structural lemmas for Rank Mul Pow Three Halves Le Fourth Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/RankMulPowThreeHalvesLeFourthPower.lean

import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioUpperBound
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
open Formalism.LogVandermondeBounds.StandardLattice
def SW_hecke_gap : Prop :=
  ∀ (q : ℝ) (M : ℕ), 2 ≤ q → 3 ≤ M →
    q ^ 2 + q < q ^ M + q - 1 + q ^ (2 - (M : ℤ)) ∧
    ∀ S : ℝ, 0 ≤ S → (q ^ M + q - 1 + q ^ (2 - (M : ℤ))) * S ≤ (q ^ 2 + q) * S → S = 0
def SW_hecke_gap_sharp : Prop :=
  ∀ q : ℝ, 0 < q → q ^ 2 + q - 1 + q ^ (2 - ((2 : ℕ) : ℤ)) = q ^ 2 + q
def SW_hecke_terms : Prop :=
  ∀ p : ℕ, p.Prime →
    Nat.card (ZMod (p ^ 2)) + Nat.card (ZMod p)ˣ + 1 = p ^ 2 + p ∧
    Nat.card {v : ZMod (p ^ 2) × ZMod (p ^ 2) // IsUnit v.1 ∨ IsUnit v.2} =
      (p ^ 2 + p) * Nat.card (ZMod (p ^ 2))ˣ
def SW_height_integral : Prop :=
  ∀ (M f : ℕ) (c R : ℝ), 3 ≤ M → 0 < c → 0 < R →
    ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), (R ^ (2 * f) / t) * t ^ (M - 1) / t =
      c ^ (M - 2) / ((M : ℝ) - 2) * R ^ (2 * f * (M - 1))
def SW_real_gaussian : Prop :=
  ∀ (M : ℕ) (τ : ℂ) (b : ℝ), 0 < τ.im →
    (2 : ℂ) ^ M * ∫ x : EuclideanSpace ℝ (Fin (2 * M)),
        Complex.exp (Real.pi * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)
          + 2 * Real.pi * Complex.I * b * ((‖x‖ ^ 2 : ℝ) : ℂ)) =
      (2 * Complex.I / (τ + 2 * b)) ^ M
def SW_real_decay : Prop :=
  ∀ (M : ℕ) (b : ℝ),
    ‖(2 * Complex.I / (2 * Complex.I + 2 * (b : ℂ))) ^ M‖ ≤ ((max 1 |b|)⁻¹) ^ M
def ball_volume : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
    (volume {x : EuclideanSpace ℝ (Fin (2 * n)) | ‖x‖ ^ 2 ≤ t}).toReal =
      Real.pi ^ n * t ^ n / (n.factorial : ℝ)
def SelfDualMeasure : Prop :=
  ∀ (M : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin (2 * M))) ℂ),
    let FT : (EuclideanSpace ℝ (Fin (2 * M)) → ℂ) → EuclideanSpace ℝ (Fin (2 * M)) → ℂ :=
      fun g ξ => (2 : ℂ) ^ M *
        ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((2 * inner ℝ x ξ : ℝ) : ℂ))) * g x
    ∀ x, FT (FT φ) x = φ (-x)
def SphereVolumeDerivative : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    HasDerivAt
      (fun t : ℝ => (2 : ℝ) ^ M * (volume {x : EuclideanSpace ℝ (Fin (2 * M)) | ‖x‖ ^ 2 ≤ t}).toReal)
      ((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) 1
def SplitDensity : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (M : ℕ) (β : F), 1 ≤ M → β ≠ 0 →
    (Fintype.card {p : (Fin M → F) × (Fin M → F) // ∑ i, p.1 i * p.2 i = β} : ℝ) /
      (Fintype.card F : ℝ) ^ (2 * M - 1) = 1 - ((Fintype.card F : ℝ)⁻¹) ^ M
def InertDensity : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [DecidableEq L] (q M : ℕ) (β : L),
    Fintype.card L = q ^ 2 → 1 ≤ M → β ≠ 0 → β ^ q = β →
    (Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = β} : ℝ) / (q : ℝ) ^ (2 * M - 1) =
      1 - (-1) ^ M * ((q : ℝ)⁻¹) ^ M
def GlobalArithmeticIdentity : Prop :=
  ∀ (f M : ℕ) (v Lv : ℝ), 1 ≤ M → 0 < v → 0 < Lv →
    let dF : ℝ := (2 * v) ^ f
    let cM : ℝ := (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)
    (cM ^ f * dF ^ ((1 : ℝ) / 2 - M) / Lv)⁻¹ =
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f / Real.sqrt dF * Lv
def LogLValueFinitePlaces : Prop :=
  ∀ (f M : ℕ) (ι : Type) [Fintype ι] (pr : ι → ℕ) (Nv : ι → ℝ) (s : ι → ℝ),
    2 ≤ M → (∀ v, (pr v).Prime) → (∀ v, (pr v : ℝ) ≤ Nv v) → (∀ v, s v = 1 ∨ s v = -1) →
    (∀ p : ℕ, (univ.filter (fun v => pr v = p)).card ≤ f) →
    |Real.log (∏ v, (1 - s v * ((Nv v)⁻¹) ^ M)⁻¹)| ≤ f * Real.log (zetaR M)
def LogLFunctionEulerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 3 ≤ M →
    Multipliable (fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsMaximal} =>
      Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
    0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)
def WeightedSumEqQuadraticForm : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ),
    (∀ a b, sg a = sg b → X a b = 0) →
    let P : ℕ → Matrix (Fin N) (Fin N) ℂ :=
      fun i => Matrix.diagonal (fun a => if a.val < i then 1 else 0)
    let V : ℕ → ℝ := fun i => ∑ a, ∑ b, ‖((1 - P i) * X * P i) a b‖ ^ 2
    ∑ i : Fin N, (if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * V (i.val + 1) else 0) =
      ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b),
        (lam b - lam a + ((a.val : ℝ) - b.val)) * ‖X a b‖ ^ 2
def RankLeTwiceMin : Prop :=
  ∀ (N : ℕ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ),
    (∀ a b, sg a = sg b → X a b = 0) →
    X.rank ≤ 2 * min (univ.filter (fun a => sg a = true)).card (univ.filter (fun a => sg a = false)).card
def OppositeSignRhoDifferenceEqCard : Prop :=
  ∀ (N : ℕ) (sg : Fin N → Bool),
    let rhoN : Fin N → ℝ := fun a =>
      (((univ.filter (fun c => a < c ∧ sg c ≠ sg a)).card : ℝ) -
        ((univ.filter (fun c => c < a ∧ sg c ≠ sg a)).card : ℝ)) / 2
    ∀ a b, a < b → sg a = sg b →
      rhoN a - rhoN b = ((univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card : ℝ)
def CumulantLowerBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (P y : ι → ℝ) (ε : ℝ), (∀ j, 0 ≤ P j) → ∑ j, P j = 1 →
    ∑ j, P j * y j = 0 → 0 ≤ ε → ε ≤ 1 → (∀ j, |y j| ≤ ε) →
    (∑ j, P j * y j ^ 2) / 2 * (1 - ε) ≤ Real.log (∑ j, P j * Real.exp (y j))
def LogMomentConvexity : Prop :=
  ∀ (ι : Type) [Fintype ι] (P y : ι → ℝ), (∀ j, 0 ≤ P j) → ∑ j, P j = 1 →
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ j, P j * Real.exp (t * y j))) ∧
    ∀ t₀ t : ℝ, 0 < t₀ → t₀ ≤ t →
      t / t₀ * Real.log (∑ j, P j * Real.exp (t₀ * y j)) ≤ Real.log (∑ j, P j * Real.exp (t * y j))
def ComplexGaussianIntegral : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ), (∀ j, 0 < w j) →
    ∫ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2) = ∏ j, Real.pi / w j
def GaussianRayIntegral : Prop :=
  ∀ (n : ℕ) (t₀ Q : ℝ), 1 ≤ n → 0 < t₀ → 0 < Q →
    ∫ t in Set.Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-((t / t₀) ^ 2 * Q)) =
      t₀ ^ n * Real.Gamma ((n : ℝ) / 2) / (2 * Q ^ ((n : ℝ) / 2))
def ExponentialTailIntegral : Prop :=
  ∀ (n : ℕ) (α : ℝ), 1 ≤ n → (n : ℝ) ≤ α →
    ∫ s in Set.Ioi (1 : ℝ), s ^ (n - 1) * Real.exp (-(α * s)) ≤ Real.exp (-α)
def TailNegligible : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (Q : ℝ), 2 ≤ n → C * n * Real.log n ≤ Q →
    Real.exp (-(Q / 2)) ≤ Real.exp (-(n : ℝ)) * (Real.Gamma ((n : ℝ) / 2) / (2 * Q ^ ((n : ℝ) / 2)))
def ThresholdConstantRescaledEpsilonBounds : Prop :=
  ∀ (C₁ C₂ : ℝ), 0 < C₁ → 1 ≤ C₂ → ∃ C : ℝ, ∀ (p q : ℕ) (ε₀ h₀ : ℝ),
    1 ≤ p → 1 ≤ q → 0 < ε₀ → ε₀ < 1 / 2 →
    C * ((min p q : ℕ) : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * ((p + q : ℕ) : ℝ) * Real.log ((p + q : ℕ) : ℝ) / ε₀ ^ 2
      ≤ h₀ →
    let ε : ℝ := ε₀ / (C₂ * ((p * q : ℕ) : ℝ))
    C₁ * ((2 * p * q : ℕ) : ℝ) * Real.log ((2 * p * q : ℕ) : ℝ) ≤ h₀ * ε ^ 2 / (4 * ((min p q : ℕ) : ℝ)) ∧
    C₁ * ((p + q : ℕ) : ℝ) ≤ ε * h₀ / 2
def GrassmannianVolume : Prop :=
  ∀ p q : ℕ,
    (∏ i ∈ range (p + q), 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) /
        ((∏ i ∈ range p, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) *
          ∏ i ∈ range q, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) =
      Real.pi ^ (p * q) * ((∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ)) /
        ∏ i ∈ range (p + q), (i.factorial : ℝ) ∧
    Real.pi ^ (p * q) * ((∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ)) /
        (∏ i ∈ range (p + q), (i.factorial : ℝ)) ≤ Real.pi ^ (p * q)
def JointLowerBound : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (d dτ c ε₀ Z : ℝ),
    (∀ a b, a < b → lam b < lam a) →
    let p := (univ.filter (fun a => sg a = true)).card
    let q := (univ.filter (fun a => sg a = false)).card
    let nab : Fin N → Fin N → ℕ :=
      fun a b => (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card
    0 < d → 0 < c → 0 < ε₀ → ε₀ < 1 → 0 < Z → Z ≤ (1 - ε₀)⁻¹ →
    (hc : 1 / c = Real.pi ^ (p * q) *
      ((∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ)) /
        ∏ i ∈ range N, (i.factorial : ℝ)) →
    (hτ : dτ = (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b + (nab a b : ℝ))) /
      ((∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ))) →
    (h12 : 1 / d ≤ c / dτ *
      (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b),
        Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))) * Z) →
    (1 - ε₀) * ((∏ a, ∏ b ∈ univ.filter (fun b => a < b), (lam a - lam b)) /
      ∏ i ∈ range N, (i.factorial : ℝ)) ≤ d
def DegreeLeMulPowSignatureBound : Prop :=
  ∀ (p q N : ℕ) (d dτ c c₀ lamAbs : ℝ), 0 < d → 0 < dτ → 0 < c → 0 < c₀ → 0 < lamAbs → 1 ≤ N →
    1 / c ≤ Real.pi ^ (p * q) →
    c * (Real.pi ^ (p * q) * (c₀ / (2 * N * lamAbs)) ^ (p * q) / ((p * q).factorial : ℝ)) * (dτ / 4)
      ≤ dτ ^ 2 / d →
    d ≤ 4 * dτ * (2 / c₀ * ((p * q : ℕ) : ℝ) * N * lamAbs) ^ (p * q)
def LocalColumnIndex : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ), 2 ≤ m → Even m → 3 ≤ Fintype.card F →
    let g : ℝ := Fintype.card F
    let r := k + m - 1
    let rS := m / 2 - 1
    let dimN := (r ^ 2 - (k + 1) ^ 2 - 2 * rS) / 2
    (∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Fintype.card (GL (Fin k) F) : ℝ) / g ^ (k * (k - 1) / 2) = g ^ (k * (k + 1) / 2) * θ) ∧
    (∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Fintype.card (GL (Fin r) F) : ℝ) / (g ^ dimN * g ^ (k * (k - 1) / 2)) =
        g ^ ((r ^ 2 + 3 * k + 1 + 2 * rS) / 2) * θ)
def IndexRatioComparison : Prop :=
  ∀ (f k m : ℕ) (g₁ g₂ Ipi Isig : ℝ) (θ θ' : Fin 2 → ℕ → ℝ), 2 ≤ m → Even m → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ i ρ, 1 / 2 ≤ θ i ρ ∧ θ i ρ ≤ 1 ∧ 1 / 2 ≤ θ' i ρ ∧ θ' i ρ ≤ 1) →
    let r := k + m - 1
    let rS := m / 2 - 1
    let g : Fin 2 → ℝ := ![g₁, g₂]
    Ipi = ∏ i, ∏ ρ ∈ range f, g i ^ (k * (k + 1) / 2) * θ i ρ →
    Isig = ∏ i, ∏ ρ ∈ range f, g i ^ ((r ^ 2 + 3 * k + 1 + 2 * rS) / 2) * θ' i ρ →
    ((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi ∧
    Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)
def RankCountExact : Prop :=
  ∀ (ι : Type) [Fintype ι] (Γ : ι → Type) [∀ i, Group (Γ i)] [∀ i, Fintype (Γ i)] (Y : Type) [Fintype Y]
    [∀ i, MulAction (Γ i) Y], (∀ (i : ι) (y : Y), MulAction.stabilizer (Γ i) y = ⊥) →
    (∑ i, (Nat.card (MulAction.orbitRel.Quotient (Γ i) Y) : ℝ)) =
      (∑ i, ((Fintype.card (Γ i) : ℝ))⁻¹) * Fintype.card Y
def LeastNoncompactGap : Prop :=
  ∀ (k m : ℕ) (v b : ℕ → ℝ) (h₀ : ℝ), 1 ≤ k → 0 ≤ h₀ →
    (∀ i, i < k - 1 → 0 ≤ v i) → 0 < b 0 → (∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j) →
    ∀ i j, i < j → j < k - 1 + m → plusSign k i ≠ plusSign k j →
      h₀ ≤ rowPar k v b i - rowPar k v b j
def RankThresholdInequalityEventually : Prop :=
  ∀ (ε C C₀ : ℝ), 0 < ε → 0 ≤ C → 0 ≤ C₀ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (f m k : ℕ),
    2 ≤ m → Even m → m ≤ f → m ≤ k → (k : ℝ) ≤ x ^ C₀ →
    let L := x ^ ε
    let r := k + m - 1
    let p := k + m / 2 - 1
    let q := m / 2
    Real.exp (-(r : ℝ)) ≤ 1 / 3 ∧ p + q = r ∧ min p q = q ∧
    C * (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r / (1 / 3 : ℝ) ^ 2 ≤ ((r : ℝ) * f * L) ^ 4
def RankMulPowThreeHalvesLeFourthPower : Prop :=
  ∀ (f m k : ℕ) (L : ℝ), 2 ≤ m → m ≤ f → 2 ≤ k → 1 ≤ L →
    120 * ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (((k + m - 1 : ℕ) : ℝ) * f * L) ^ 4
def DimensionMassJointBound : Prop :=
  ∀ (f : ℕ) (Dstar volY massr Isig : ℝ) (dsig dimV : ℕ → ℝ),
    0 < massr → 0 < Isig → (∀ ρ, ρ < f → 0 ≤ dimV ρ) →
    (h2 : volY = massr) → (h3 : ∀ ρ, ρ < f → (1 - 1 / 3) * dimV ρ ≤ dsig ρ) →
    (hD : Dstar = volY * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ ≤ Dstar
def VolumeParameterBounds : Prop :=
  ∀ (e q d : ℕ), 2 ≤ e → 3 ≤ q → 7 ≤ d →
    let n : ℝ := 2 ^ e
    let rd : ℝ := (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)
    let v : ℝ := rd / 2
    Real.pi ≤ v ∧ Real.log v ≤ Real.log (2 * n) + Real.log ((q : ℝ) * d) / 2
def LogVolumeLeParameter : Prop :=
  ∀ (ε C₀ A : ℝ), 0 < ε → 0 ≤ C₀ → 0 ≤ A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (n q d : ℝ),
    1 ≤ n → 1 ≤ q → 1 ≤ d → n ≤ x ^ C₀ → Real.log q ≤ A * x ^ (ε / 5) →
    Real.log d ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
    Real.log (2 * n) + Real.log (q * d) / 2 ≤ x ^ ε
def BracketCoefficients : Prop :=
  ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
    (∑ M ∈ Ico (k + 1) (k - 1 + m + 1), (M : ℝ)) / k = ((m : ℝ) - 1) + (m : ℝ) * (m - 1) / (2 * k) ∧
    ((m : ℝ) * (2 * k + m - 1) / 2) / k = m + (m : ℝ) * (m - 1) / (2 * k)
def LogMassFormula : Prop :=
  ∀ (f m k : ℕ) (vE massk massr : ℝ) (Lval : ℕ → ℝ), 1 ≤ f → 1 ≤ m → 1 ≤ k → 0 < vE → 0 < massk →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (1 / ((f : ℝ) * k)) * Real.log (massr / massk) =
      (((m : ℝ) - 1) + (m : ℝ) * (m - 1) / (2 * k)) * Real.log (vE / Real.pi)
      + (1 / (k : ℝ)) * (∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (((M - 1).factorial : ℕ) : ℝ))
      - (((m : ℝ) - 1) / (2 * k)) * Real.log (2 * vE)
      + (1 / ((f : ℝ) * k)) * ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (Lval M)
def BracketSumBound : Prop :=
  ∀ (k m : ℕ) (L vE G : ℝ) (b w : ℕ → ℝ), 1 ≤ k → 1 ≤ m → Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ G →
    1 ≤ b 0 → (∀ j, j < m → b j < w j) → (∀ j, j + 1 < m → w j < b (j + 1)) →
    w (m - 1) ≤ 2 * Real.exp L →
    (m : ℝ) * Real.log (vE / Real.pi) - L ≤
      (((m : ℝ) - 1) + (m : ℝ) * (m - 1) / (2 * k)) * Real.log (vE / Real.pi) ∧
    (m : ℝ) * Real.log G ≤ ((m : ℝ) + (m : ℝ) * (m - 1) / (2 * k)) * Real.log G ∧
    (∑ j ∈ range m, Real.log (w j)) - (L + Real.log 2) - (m : ℝ) * (L + Real.log 2) / k ≤
      (((k : ℝ) - 1) / k) * ∑ j ∈ range m, Real.log (b j)
def InitialSumIdentity : Prop :=
  ∀ (f m k : ℕ) (vE g₁ g₂ : ℝ) (u : ℕ → ℕ → ℝ) (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ),
    1 ≤ m → 1 ≤ k → 0 < vE → 0 < g₁ → 0 < g₂ → 0 < massk → 0 < Ipi →
    (∀ ρ, ρ < f → 0 < vandN (u ρ) k) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hD : Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    Dstar / dstar =
      (∏ M ∈ Ico (k + 1) (k - 1 + m + 1), Lval M) *
      ((Isig / Ipi) / (g₁ * g₂) ^ (f * (k * m + m * (m - 1) / 2))) *
      ∏ ρ ∈ range f,
        (((Real.pi / vE)⁻¹) ^ ((m - 1) * k + m * (m - 1) / 2) * (2 * vE) ^ (-(((m : ℝ) - 1) / 2)) *
          (g₁ * g₂) ^ (k * m + m * (m - 1) / 2) *
          (dsig ρ * ∏ i ∈ range (k - 1 + m), ((i.factorial : ℕ) : ℝ)) / vandN (u ρ) k)
def InterlacedProductComparison : Prop :=
  ∀ (L vE aeff A : ℝ) (m : ℕ) (b w : ℕ → ℝ), 1 ≤ m → Real.pi ≤ vE → Real.log vE ≤ L →
    1 ≤ b 0 → (∀ j, j < m → b j < w j) → (∀ j, j + 1 < m → w j < b (j + 1)) →
    w (m - 1) ≤ 2 * Real.exp L → 0 < aeff → |Real.log aeff| ≤ A →
    let κ : ℝ := Real.pi / vE
    (∏ j ∈ range m, w j * vE / Real.pi) =
      ((κ⁻¹) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff) * (κ⁻¹ * aeff * ∏ j ∈ range m, w j / b j) ∧
    |Real.log (∏ j ∈ range m, w j * vE / Real.pi)
        - Real.log ((κ⁻¹) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff)| ≤ 2 * L + Real.log 2 + A
def PowerProductTwoSidedBounds : Prop :=
  ∀ (f k : ℕ) (T X Γ Dstar dstar dM lo hi : ℝ), 1 ≤ f → 1 ≤ k → 2 * f ≤ 2 ^ k → 2 ≤ T → 0 < X → 1 ≤ Γ →
    0 < Dstar → 0 < dstar → X ^ (f * k) = Dstar / dstar →
    X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) ≤ T →
    T ≤ X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) * (1 + 1 / ((f : ℝ) * k)) →
    dM = dstar * (T ^ k - 1) ^ f →
    lo ≤ Real.log X → Real.log X ≤ hi →
    Dstar * (Γ⁻¹) ^ 2 / 2 ≤ dM ∧ dM ≤ Real.exp 1 * (Dstar * (Γ⁻¹) ^ 2) ∧
    Real.log T ≤ hi + Real.log 2 ∧ lo - 2 * Real.log Γ / ((f : ℝ) * k) ≤ Real.log T
def MeanSquareRequiresDegreeBound : Prop :=
  ∀ c : ℝ, 0 < c → ∃ (f k : ℕ) (T X Γ Dstar dstar : ℝ), 1 ≤ f ∧ 1 ≤ k ∧ 2 ≤ T ∧ 0 < X ∧ 1 ≤ Γ ∧
    0 < Dstar ∧ 0 < dstar ∧ X ^ (f * k) = Dstar / dstar ∧
    X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) ≤ T ∧
    T ≤ X * Γ ^ (-(2 : ℝ) / ((f : ℝ) * k)) * (1 + 1 / ((f : ℝ) * k)) ∧
    dstar * (T ^ k - 1) ^ f < c * (Dstar * (Γ⁻¹) ^ 2)
def NormalizedLogRatioVandermondeVariation : Prop :=
  ∀ (f k : ℕ) (Dstar massk Ipi V : ℝ) (u u' : ℕ → ℕ → ℝ), 1 ≤ f → 1 ≤ k →
    0 < Dstar → 0 < massk → 0 < Ipi →
    (∀ ρ, ρ < f → 0 < vandN (u ρ) k ∧ 0 < vandN (u' ρ) k ∧
      |Real.log (vandN (u ρ) k) - Real.log (vandN (u' ρ) k)| ≤ V) →
    |(1 / ((f : ℝ) * k)) * Real.log (Dstar / (massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k)) -
      (1 / ((f : ℝ) * k)) * Real.log (Dstar / (massk * Ipi * ∏ ρ ∈ range f, dimVN (u' ρ) k))| ≤ V / k
end Formalism.HermitianLattices.GenusMassVolumes


