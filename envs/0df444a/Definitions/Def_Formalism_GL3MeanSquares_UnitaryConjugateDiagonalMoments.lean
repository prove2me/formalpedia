-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_UnitaryConjugateDiagonalMoments
-- name    : Formalism_GL3MeanSquares_UnitaryConjugateDiagonalMoments
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:49.195274+00:00
-- url     : https://prove2.me/theorems/6e3184a5-a102-4233-a8b7-e18c78a8b29f
-- title:
--   Unitary Conjugate Diagonal Moments
-- statement:
--   Definitions and structural lemmas for Unitary Conjugate Diagonal Moments, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/UnitaryConjugateDiagonalMoments.lean

import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.FormalDegreeBoundsAlt
open Finset MeasureTheory Filter Topology
open Formalism.LogVandermondeBounds.StandardLattice
open scoped ComplexOrder
def SW_density_tail : Prop :=
  ∀ (q : ℝ) (M : ℕ), 2 ≤ q → 3 ≤ M →
    HasSum (fun j : ℕ => q ^ (j + 1) * (1 - 1 / q) * (q⁻¹) ^ ((j + 1) * M))
      ((1 - 1 / q) * (q⁻¹) ^ (M - 1) / (1 - (q⁻¹) ^ (M - 1))) ∧
    (1 - 1 / q) * (q⁻¹) ^ (M - 1) / (1 - (q⁻¹) ^ (M - 1)) ≤ 4 / 3 * (q⁻¹) ^ (M - 1)
def SW_primitive_bound : Prop :=
  ∀ (y F z : ℝ), 0 ≤ y → y ≤ 1 / 4 → |F - 1| ≤ 2 * y → (z = (1 - y) ^ 2 ∨ z = 1 - y ^ 2) →
    |F * z - 1| ≤ 8 * y
def SW_dilation_joint : Prop :=
  ∀ (M : ℕ) (q c κ C F0 : ℝ) (F : ℕ → ℝ), 3 ≤ M → 1 < q → 0 < κ → 0 < F0 →
    Tendsto F atTop (𝓝 F0) →
    (∀ j : ℕ, |c - 1| * |κ * (q ^ j) ^ (M - 2) * F j| ≤ C) → c = 1
def SL2WordIdentities : Prop :=
  ∀ (F : Type) [Field F],
    let n : F → Matrix (Fin 2) (Fin 2) F := fun b => !![1, b; 0, 1]
    let t : F → Matrix (Fin 2) (Fin 2) F := fun a => !![a, 0; 0, a⁻¹]
    let w : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
    let w' : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]
    (∀ a b c d : F, a * d - b * c = 1 → c ≠ 0 → !![a, b; c, d] = n (a / c) * t (-1 / c) * w * n (d / c)) ∧
    (∀ a b : F, a ≠ 0 → !![a, b; 0, a⁻¹] = n (a * b) * t a) ∧
    w' * w = 1 ∧
    (∀ b : F, b ≠ 0 → w' * n b * w = !![1, 0; -b, 1] ∧
      !![1, 0; -b, 1] = n (-1 / b) * t (1 / b) * w * n (-1 / b)) ∧
    (∀ a b c d : F, a * d - b * c = 1 → a ≠ 0 → !![a, b; c, d] = !![1, 0; c / a, 1] * t a * n (b / a))
def SW_heisenberg_phase : Prop :=
  ∀ (K : Type) [Field K] [NeZero (2 : K)] (V : Type) [AddCommGroup V] [Module K V] (B : V →ₗ[K] V →ₗ[K] K),
    (∀ x y, B x y = B y x) →
    ∀ (b : K) (u x y : V),
      -(b * (B u u / 2)) + B u y + B x y / 2 + b * (B (u + x) (u + x) / 2) =
        B u (y + b • x) + B x (y + b • x) / 2
def SW_gauss_fourier : Prop :=
  ∀ (σ : ℂ) (c u' : ℝ), 0 < σ.im → (c = 1 ∨ c = -1) →
    ∫ u : ℝ, Complex.exp (2 * Real.pi * Complex.I * σ * (u : ℂ) ^ 2 + 4 * Real.pi * Complex.I * c * u * u') =
      (-2 * Complex.I * σ) ^ (-(1 / 2 : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (-1 / σ) * (u' : ℂ) ^ 2)
def SW_packing : Prop :=
  ∀ (n : ℕ) (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] (R r : ℝ), 0 < r → r ≤ R →
    ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 R).Finite ∧
    (((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 R).ncard : ℝ) ≤
      (1 + 4 * R / r) ^ n * (((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 r).ncard : ℝ)
def SplitPlaceLiftCountDensity : Prop :=
  ∀ (p n M : ℕ) (β : ZMod (p ^ n)), p.Prime → 1 ≤ n → 1 ≤ M → IsUnit β →
    Nat.card {xy : (Fin M → ZMod (p ^ n)) × (Fin M → ZMod (p ^ n)) // ∑ i, xy.1 i * xy.2 i = β} =
      p ^ ((2 * M - 1) * (n - 1)) * (p ^ (M - 1) * (p ^ M - 1))
def LogZetaIntegerDecayBound : Prop :=
  ∀ M : ℕ, 2 ≤ M →
    Real.log (zetaR M) ≤ zetaR M - 1 ∧ zetaR M - 1 ≤ 3 * ((2 : ℝ)⁻¹) ^ M
noncomputable def cbW {N i : ℕ} (hi : i ≤ N) (U : Matrix (Fin N) (Fin N) ℂ)
    (S : {S : Finset (Fin N) // S.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det‖ ^ 2
noncomputable def sh (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u
noncomputable def jacE {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∏ a, ∏ b ∈ univ.filter (fun b => a < b), sh (x a - x b)
def CauchyBinetLeadingMinor : Prop :=
  ∀ (N i : ℕ) (hi : i ≤ N) (U : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℝ),
    ((U * Matrix.diagonal (fun s => ((Real.exp (x s) : ℝ) : ℂ)) * U.conjTranspose).submatrix
        (Fin.castLE hi) (Fin.castLE hi)).det =
      ((∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S * Real.exp (∑ s ∈ S.1, x s) : ℝ) : ℂ)
def UnitaryConjugateDiagonalMoments : Prop :=
  ∀ (N i : ℕ) (hi : i ≤ N) (U : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℝ),
    U ∈ Matrix.unitaryGroup (Fin N) ℂ →
    let X : Matrix (Fin N) (Fin N) ℂ := U * Matrix.diagonal (fun s => ((x s : ℝ) : ℂ)) * U.conjTranspose
    let trA : ℝ := ∑ a : Fin i, (X (Fin.castLE hi a) (Fin.castLE hi a)).re
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S) = 1 ∧
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S * ∑ s ∈ S.1, x s) = trA ∧
    (∑ S : {S : Finset (Fin N) // S.card = i}, cbW hi U S * (∑ s ∈ S.1, x s) ^ 2) =
      trA ^ 2 + ∑ a, ∑ b ∈ univ.filter (fun b : Fin N => b.val < i ∧ i ≤ a.val), ‖X a b‖ ^ 2
def OffDiagonalEigenvalueSumBound : Prop :=
  ∀ (N : ℕ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian),
    (∀ a b, sg a = sg b → X a b = 0) → ∀ S : Finset (Fin N),
    |∑ s ∈ S, hX.eigenvalues s| ≤
      Real.sqrt (((min (univ.filter (fun a => sg a = true)).card (univ.filter (fun a => sg a = false)).card : ℕ) : ℝ) / 2) *
        Real.sqrt (∑ a, ∑ b, ‖X a b‖ ^ 2)
def SharpIntegralGapBound : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (h₀ lamAbs : ℝ),
    X.IsHermitian → (∀ a b, sg a = sg b → X a b = 0) →
    (∀ a b : Fin N, b < a → ((a.val : ℝ) - b.val) ≤ lam b - lam a) →
    (∀ a b, b < a → sg a ≠ sg b → h₀ ≤ lam b - lam a) → (∀ a b, lam a - lam b ≤ lamAbs) →
    let Q : ℝ := ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b),
        (lam b - lam a + ((a.val : ℝ) - b.val)) * ‖X a b‖ ^ 2
    (h₀ + 1) * (∑ a, ∑ b, ‖X a b‖ ^ 2) / 2 ≤ Q ∧ Q ≤ lamAbs * ∑ a, ∑ b, ‖X a b‖ ^ 2
def JacobianEigenvalueBounds : Prop :=
  ∀ (N : ℕ) (x : Fin N → ℝ),
    1 ≤ jacE x ∧ Real.log (jacE x) ≤ N * (∑ a, x a ^ 2) / 6 ∧
    Real.log (jacE x) ≤ ((N : ℝ) - 1) * ∑ a, |x a|
def JacobianLogBoundOffDiagonal : Prop :=
  ∀ (N : ℕ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian),
    (∀ a b, sg a = sg b → X a b = 0) →
    Real.log (jacE hX.eigenvalues) ≤ ((N : ℝ) - 1) *
      (Real.sqrt (2 * ((min (univ.filter (fun a => sg a = true)).card (univ.filter (fun a => sg a = false)).card : ℕ) : ℝ)) *
        Real.sqrt (∑ a, ∑ b, ‖X a b‖ ^ 2)) ∧
    Real.log (jacE hX.eigenvalues) ≤ N * (∑ a, ∑ b, ‖X a b‖ ^ 2) / 6
def LeastNoncompactGapAdjacent : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (h : ℝ), (∀ a b, a < b → lam b < lam a) →
    (∀ a b : Fin N, b.val = a.val + 1 → sg a ≠ sg b → h ≤ lam a - lam b) →
    ∀ a b, b < a → sg a ≠ sg b → h ≤ lam b - lam a
def CompactPairGapConsistency : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (h₀ : ℝ),
    (∀ a b, b < a → sg a ≠ sg b → h₀ ≤ lam b - lam a) →
    ∀ a e b, a < e → e < b → sg a = sg b → sg e ≠ sg a → 2 * h₀ ≤ lam a - lam b
def SchurOrthogonalityAmGmBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ℕ) (μ f : ι → ℝ) (v : ι → Fin d → ℂ) (dτ : ℝ), (∀ k, 0 ≤ μ k) →
    (∀ k, dτ * ∑ k', μ k' * ‖∑ i, star (v k i) * v k' i‖ ^ 2 = 1) →
    ∑ i, ∑ j, ‖∑ k, ((dτ * μ k * f k : ℝ) : ℂ) * (v k i * star (v k j))‖ ^ 2 ≤ dτ * ∑ k, μ k * f k ^ 2
def SchurOperatorLowerBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ℕ) (μ f : ι → ℝ) (v : ι → Fin d → ℂ) (dτ c₀ : ℝ), (∀ k, 0 ≤ μ k) → 0 ≤ dτ →
    (∀ k, c₀ ≤ f k) →
    (Matrix.of fun i j => ∑ k, ((dτ * μ k : ℝ) : ℂ) * (v k i * star (v k j))) = (1 : Matrix (Fin d) (Fin d) ℂ) →
    ((Matrix.of fun i j => ∑ k, ((dτ * μ k * f k : ℝ) : ℂ) * (v k i * star (v k j))) -
      ((c₀ : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef
def RadiusThresholdLeGapThreshold : Prop :=
  ∀ (p q : ℕ) (ε₀ : ℝ), 1 ≤ p → 1 ≤ q → 0 < ε₀ → ε₀ < 1 / 2 →
    120 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      8192 * ((min p q : ℕ) : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * Real.log ((p + q : ℕ) : ℝ) / ε₀ ^ 2
def GapConditionExplicitConstants : Prop :=
  ∀ (p q : ℕ) (ε₀ h₀ : ℝ), 1 ≤ p → 1 ≤ q → 0 < ε₀ → ε₀ < 1 / 2 →
    8192 * ((min p q : ℕ) : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * Real.log ((p + q : ℕ) : ℝ) / ε₀ ^ 2 ≤ h₀ →
    let ε : ℝ := ε₀ / (8 * ((p * q : ℕ) : ℝ))
    ((p + q : ℕ) : ℝ) / (3 * ε) ≤ h₀ ∧
    8 * ((2 * p * q : ℕ) : ℝ) * Real.log (2 * ((2 * p * q : ℕ) : ℝ)) ≤ (h₀ + 1) * ε ^ 2 / (4 * ((min p q : ℕ) : ℝ))
def ExplicitPowerInverseBound : Prop :=
  ∀ (p q : ℕ) (ε₀ : ℝ), 1 ≤ p → 1 ≤ q → 0 < ε₀ → ε₀ < 1 / 2 →
    ((1 - 2 * (ε₀ / (8 * ((p * q : ℕ) : ℝ))))⁻¹) ^ (p * q) ≤ 1 + 0.33 * ε₀ ∧
    1 + 0.33 * ε₀ + 0.25 * ε₀ ≤ (1 - ε₀)⁻¹
def GaussianTailExplicitBound : Prop :=
  ∀ (p q : ℕ) (ε₀ A : ℝ), 1 ≤ p → 1 ≤ q → Real.exp (-((p + q : ℕ) : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    8 * ((2 * p * q : ℕ) : ℝ) * Real.log (2 * ((2 * p * q : ℕ) : ℝ)) ≤ A →
    let ε : ℝ := ε₀ / (8 * ((p * q : ℕ) : ℝ))
    A / 2 ≤ (1 - ε) * A - ((p + q : ℕ) : ℝ) * ε ∧ ((2 * p * q : ℕ) : ℝ) ≤ (1 - ε) * A - ((p + q : ℕ) : ℝ) * ε ∧
    Real.exp (-(A / 2)) ≤ ε₀ / 4 / (2 * A ^ (p * q))
def UpperBoundExplicitConstants : Prop :=
  ∀ (p q : ℕ) (d dτ c lamAbs : ℝ), 0 < d → 0 < dτ → 0 < c → 0 < lamAbs →
    1 / c ≤ Real.pi ^ (p * q) →
    c * (Real.pi ^ (p * q) * (Real.log 2 / (2 * lamAbs)) ^ (p * q) / ((p * q).factorial : ℝ)) * (dτ / 4)
      ≤ dτ ^ 2 / d →
    d ≤ 4 * dτ * (3 * ((p * q : ℕ) : ℝ) * lamAbs) ^ (p * q)
def UpperBoundBallRadius : Prop :=
  ∀ (p q : ℕ) (lamAbs nX2 : ℝ), 1 ≤ p → 1 ≤ q →
    120 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ lamAbs → nX2 ≤ Real.log 2 / lamAbs →
    2 * ((min p q : ℕ) : ℝ) * nX2 ≤ 1
def WeylDenominatorFactorialProduct : Prop :=
  ∀ p : ℕ, ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, ((j : ℝ) - i) = ∏ i ∈ range p, (i.factorial : ℝ)
def FormalDegreeExactUnitaryOneOne : Prop :=
  ∀ l : ℕ, 1 ≤ l →
    IntegrableOn (fun r : ℝ => ((Real.cosh r)⁻¹) ^ (2 * l + 2) * Real.sinh r * Real.cosh r) (Set.Ioi 0) ∧
    1 / Real.pi * (2 * Real.pi *
      ∫ r in Set.Ioi (0 : ℝ), ((Real.cosh r)⁻¹) ^ (2 * l + 2) * Real.sinh r * Real.cosh r) = 1 / (l : ℝ)
def FormalDegreeExactUnitaryTwoOne : Prop :=
  ∀ κ : ℕ, 3 ≤ κ →
    IntegrableOn (fun r : ℝ => ((Real.cosh r)⁻¹) ^ (2 * κ - 1) * Real.sinh r ^ 3) (Set.Ioi 0) ∧
    2 / Real.pi ^ 2 * (2 * Real.pi ^ 2 *
      ∫ r in Set.Ioi (0 : ℝ), ((Real.cosh r)⁻¹) ^ (2 * κ - 1) * Real.sinh r ^ 3) =
      2 / (((κ : ℝ) - 1) * ((κ : ℝ) - 2))
def FD_dimV_ge_one : Prop :=
  ∀ (N : ℕ) (lam : ℕ → ℝ), (∀ i j, i < j → j < N → ((j : ℝ) - i) ≤ lam i - lam j) → 1 ≤ dimVN lam N
def FD_dtau_le : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (lamAbs : ℝ),
    (∀ a b : Fin N, a < b → ((b.val : ℝ) - a.val) ≤ lam a - lam b) → (∀ a b, lam a - lam b ≤ lamAbs) →
    let p := (univ.filter (fun a => sg a = true)).card
    let q := (univ.filter (fun a => sg a = false)).card
    let nab : Fin N → Fin N → ℕ :=
      fun a b => (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card
    (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b + (nab a b : ℝ))) /
      ((∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ)) ≤ (1 + lamAbs) ^ (N ^ 2)
def FD_log_bounds : Prop :=
  ∀ (p q : ℕ) (C ε₀ d dτ dimV lamAbs : ℝ), 1 ≤ p → 1 ≤ q → 1 ≤ C → 0 < ε₀ → ε₀ < 1 / 2 →
    ((p + q : ℕ) : ℝ) - 1 ≤ lamAbs → 1 ≤ dimV → 0 < dτ → dτ ≤ (1 + lamAbs) ^ ((p + q) ^ 2) →
    (h3l : (1 - ε₀) * dimV ≤ d) →
    (h3u : d ≤ 4 * dτ * (C * ((p * q : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * lamAbs) ^ (p * q)) →
    -1 ≤ Real.log d ∧
    Real.log d ≤ 2 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (C * ((p + q : ℕ) : ℝ) * (1 + lamAbs))
def ParabolicIndexQuotientExact : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ), 2 ≤ m → Even m →
    let g : ℝ := Fintype.card F
    let r := k + m - 1
    let rS := m / 2 - 1
    let dimN := (r ^ 2 - (k + 1) ^ 2 - 2 * rS) / 2
    ((Fintype.card (GL (Fin r) F) : ℝ) / (g ^ dimN * g ^ (k * (k - 1) / 2))) /
        ((Fintype.card (GL (Fin k) F) : ℝ) / g ^ (k * (k - 1) / 2)) =
      g ^ (m * (2 * k + m - 1) / 2) * ∏ i ∈ Ico (k + 1) (r + 1), (1 - (g⁻¹) ^ i) ∧
    1 - 2 * (g⁻¹) ^ (k + 1) ≤ ∏ i ∈ Ico (k + 1) (r + 1), (1 - (g⁻¹) ^ i) ∧
    ∏ i ∈ Ico (k + 1) (r + 1), (1 - (g⁻¹) ^ i) ≤ 1
def WeightGapThresholdPolynomialBounds : Prop :=
  ∀ (f m k : ℕ) (L : ℝ), 2 ≤ m → Even m → m ≤ k → 1 ≤ f → 1 ≤ L →
    let r := k + m - 1
    let p := k + m / 2 - 1
    let q := m / 2
    let need : ℝ := 8192 * (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r / (1 / 3 : ℝ) ^ 2
    need ≤ 4608 * (m : ℝ) ^ 4 * (r : ℝ) ^ 4 * Real.log r ∧
    need ≤ (r : ℝ) ^ 19 * (f : ℝ) ^ 5 * L ∧
    120 * (r : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (r : ℝ) ^ 19 * (f : ℝ) ^ 5 * L ∧
    (L ≤ r → ((r : ℝ) * f * L) ^ 4 ≤ (r : ℝ) ^ 19 * (f : ℝ) ^ 5 * L) ∧
    (m ≤ f → 4608 * Real.log r ≤ L ^ 4 → need ≤ ((r : ℝ) * f * L) ^ 4)
noncomputable def cloudV (c Δ : ℝ) : ℕ → ℝ := fun l => c - 4 * Δ * l
noncomputable def wordU (c Δ : ℝ) (δ : ℕ → ℕ) : ℕ → ℝ := fun l => cloudV c Δ l - 1 / 2 - (δ l : ℝ) * Δ
noncomputable def colU (k : ℕ) (c Δ : ℝ) (δ : ℕ → ℕ) (u0 uk : ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then u0 else if i = k - 1 then uk else wordU c Δ δ (i - 1)
def LogLValueAndEulerFactorSumBounds : Prop :=
  ∀ (f k r : ℕ) (g : ℝ) (Lval : ℕ → ℝ), 1 ≤ k → 3 ≤ g →
    (∀ M ∈ Ico (k + 1) (r + 1), |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    |∑ M ∈ Ico (k + 1) (r + 1), Real.log (Lval M)| ≤ 3 * f * ((2 : ℝ)⁻¹) ^ k ∧
    ∑ j ∈ Ico (k + 1) (r + 1), Real.log (1 - (g⁻¹) ^ j) ≤ 0 ∧
    -(4 * (g⁻¹) ^ (k + 1)) ≤ ∑ j ∈ Ico (k + 1) (r + 1), Real.log (1 - (g⁻¹) ^ j)
def MassFormalDegreeExactIdentity : Prop :=
  ∀ (f m k : ℕ) (vE g₁ g₂ X : ℝ) (u : ℕ → ℕ → ℝ) (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ),
    1 ≤ m → 1 ≤ k → 0 < vE → 1 < g₁ → 1 < g₂ → 0 < massk → 0 < Ipi → 0 < X →
    (∀ ρ, ρ < f → 0 < vandN (u ρ) k ∧ 0 < dsig ρ) →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : Isig / Ipi = (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) *
      ((∏ j ∈ Ico (k + 1) (k - 1 + m + 1), (1 - (g₁⁻¹) ^ j)) *
        ∏ j ∈ Ico (k + 1) (k - 1 + m + 1), (1 - (g₂⁻¹) ^ j)) ^ f) →
    (hD : Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (hX : X ^ (f * k) = Dstar / dstar) →
    (f : ℝ) * k * Real.log X =
      (f : ℝ) * (((m : ℝ) - 1) * k + (m : ℝ) * (m - 1) / 2) * Real.log (vE / Real.pi)
      - (f : ℝ) * (((m : ℝ) - 1) / 2) * Real.log (2 * vE)
      + (∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (Lval M))
      + (f : ℝ) * ((m : ℝ) * (2 * k + m - 1) / 2) * Real.log (g₁ * g₂)
      + (f : ℝ) * ((∑ j ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (1 - (g₁⁻¹) ^ j)) +
          ∑ j ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (1 - (g₂⁻¹) ^ j))
      + ∑ ρ ∈ range f,
          Real.log (dsig ρ * (∏ i ∈ range (k - 1 + m), ((i.factorial : ℕ) : ℝ)) / vandN (u ρ) k)
def CrossTermLogSumBounds : Prop :=
  ∀ (k m : ℕ) (x : ℝ) (v b : ℕ → ℝ), 0 < x → (∀ j, j < m → 0 < b j) →
    (∀ i j, i < k - 1 → j < m → 0 ≤ v i ∧ v i ≤ b j / x) →
    (((k - 1 : ℕ) : ℝ)) * (∑ j ∈ range m, Real.log (b j)) ≤
      ∑ i ∈ range (k - 1), ∑ j ∈ range m, Real.log (v i + b j) ∧
    ∑ i ∈ range (k - 1), ∑ j ∈ range m, Real.log (v i + b j) ≤
      (((k - 1 : ℕ) : ℝ)) * (∑ j ∈ range m, Real.log (b j)) + (((k - 1 : ℕ) : ℝ)) * m / x
def VandermondeCloudVariation : Prop :=
  ∀ (n : ℕ) (c Δ : ℝ) (δ δ' : ℕ → ℕ), 1 ≤ n → 0 < Δ → (∀ l, δ l ≤ 1) → (∀ l, δ' l ≤ 1) →
    |Real.log (vandN (wordU c Δ δ) n) - Real.log (vandN (wordU c Δ δ') n)| ≤
      2 / 3 * (n : ℝ) * (1 + Real.log n) ∧
    -((n : ℝ) / 3 * (1 + Real.log n)) ≤
      Real.log (vandN (wordU c Δ δ) n) - Real.log (vandN (cloudV c Δ) n) ∧
    Real.log (vandN (wordU c Δ δ) n) - Real.log (vandN (cloudV c Δ) n) ≤ (n : ℝ) / 4 * (1 + Real.log n)
def VandermondeBoundaryEntriesBound : Prop :=
  ∀ (k : ℕ) (c Δ a S u0 uk : ℝ) (δ : ℕ → ℕ), 2 ≤ k → 0 < Δ → (∀ l, δ l ≤ 1) →
    (∀ j, 1 ≤ j → j < k → 1 ≤ colU k c Δ δ u0 uk 0 - colU k c Δ δ u0 uk j ∧
      colU k c Δ δ u0 uk 0 - colU k c Δ δ u0 uk j ≤ 2 * a) →
    (∀ i, 1 ≤ i → i < k - 1 → 1 ≤ colU k c Δ δ u0 uk i - colU k c Δ δ u0 uk (k - 1) ∧
      colU k c Δ δ u0 uk i - colU k c Δ δ u0 uk (k - 1) ≤ 2 * a) →
    1 ≤ S → (∀ i, i < k - 2 → 1 ≤ cloudV c Δ i - cloudV c Δ (k - 2) ∧ cloudV c Δ i - cloudV c Δ (k - 2) ≤ S) →
    -(2 * (k : ℝ) * Real.log (2 * a)) - (k : ℝ) / 4 * (1 + Real.log k) ≤
      Real.log (vandN (cloudV c Δ) (k - 1)) - Real.log (vandN (colU k c Δ δ u0 uk) k) ∧
    Real.log (vandN (cloudV c Δ) (k - 1)) - Real.log (vandN (colU k c Δ δ u0 uk) k) ≤
      (k : ℝ) * Real.log S + (k : ℝ) / 3 * (1 + Real.log k)
def VandermondeVariationExplicit : Prop :=
  ∀ (k : ℕ) (c Δ u0 uk : ℝ) (δ δ' : ℕ → ℕ), 2 ≤ k → 0 < Δ → (∀ l, δ l ≤ 1) → (∀ l, δ' l ≤ 1) →
    4 * (k : ℝ) * Δ ≤ u0 - cloudV c Δ 0 →
    (uk = cloudV c Δ (k - 2) - 1 / 2 ∨ ∀ l, l < k - 2 → 4 * (k : ℝ) * Δ ≤ cloudV c Δ l - 1 / 2 - Δ - uk) →
    |Real.log (vandN (colU k c Δ δ u0 uk) k) - Real.log (vandN (colU k c Δ δ' u0 uk) k)| ≤
      (k : ℝ) * (1 + Real.log k) + 2
def LowerBoundTermwiseComparison : Prop :=
  ∀ (f k m : ℕ) (L x vE G logX : ℝ) (b w : ℕ → ℕ → ℝ), 1 ≤ f → 1 ≤ m → m ≤ k → (m : ℝ) ≤ x → 1 ≤ L →
    Real.pi ≤ vE → Real.log (2 * vE) ≤ L → 1 ≤ G →
    (∀ ρ j, ρ < f → j < m → 1 ≤ b ρ j ∧ Real.log (b ρ j) ≤ 2 * L ∧ 0 < w ρ j ∧ w ρ j ≤ b ρ j * (1 + 1 / x)) →
    (hlow : (((m : ℝ) - 1) + (m : ℝ) * (m - 1) / (2 * k)) * Real.log (vE / Real.pi)
      - (((m : ℝ) - 1) / (2 * k)) * Real.log (2 * vE)
      + ((m : ℝ) + (m : ℝ) * (m - 1) / (2 * k)) * Real.log G
      + (((k : ℝ) - 1) / k) * ((1 / (f : ℝ)) * ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (b ρ j))
      - 5 * L - 1 ≤ logX) →
    (1 / (f : ℝ)) * (∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j * vE / Real.pi))
      + (m : ℝ) * Real.log G - 11 * L ≤ logX
def LogLowerBoundOfUniformWeightBound : Prop :=
  ∀ (f m : ℕ) (L vE G logX w2 : ℝ) (w : ℕ → ℕ → ℝ), 1 ≤ f → 44 ≤ m → 0 ≤ L → Real.pi ≤ vE → 1 ≤ G →
    0 < w2 → 3 * L / 4 ≤ Real.log w2 → (∀ ρ j, ρ < f → j < m → w2 ≤ w ρ j) →
    (1 / (f : ℝ)) * (∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j * vE / Real.pi))
      + (m : ℝ) * Real.log G - 11 * L ≤ logX →
    (m : ℝ) * Real.log w2 + (m : ℝ) * Real.log G - 11 * L ≤ logX ∧ (m : ℝ) * L / 2 ≤ logX
def UpperBoundMassRatio : Prop :=
  ∀ (f m k : ℕ) (L vE massk massr : ℝ) (Lval : ℕ → ℝ), 1 ≤ f → 1 ≤ m → m ≤ k → 2 ≤ k →
    Real.pi ≤ vE → Real.log (2 * vE) ≤ L → Real.log (2 * (k : ℝ)) ≤ L → 0 < massk →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    Real.log (massr / massk) ≤ 7 / 2 * (f : ℝ) * m * k * L + f
def UpperBoundLogFormalDegree : Prop :=
  ∀ (p q k m : ℕ) (L dτ lamAbs : ℝ), 1 ≤ p → 1 ≤ q → p * q ≤ k * m → 3 ≤ Real.exp L → 0 < dτ → 0 < lamAbs →
    ((p * q : ℕ) : ℝ) ≤ Real.exp L ^ 2 / 2 → lamAbs ≤ 2 * Real.exp L ^ 2 →
    Real.log (4 * dτ * (3 * ((p * q : ℕ) : ℝ) * lamAbs) ^ (p * q)) ≤ 2 + Real.log dτ + 5 * (k : ℝ) * m * L
def UpperBoundSumOfContributions : Prop :=
  ∀ (f k m : ℕ) (L CY : ℝ), 1 ≤ k → 44 ≤ m → 1 ≤ L → 0 ≤ CY →
    (7 / 2 * (f : ℝ) * m * k * L + f) + 3 * CY * f * m * k * L + (f : ℝ) * (2 + 6 * k * m * L)
      + (f : ℝ) * (5 * k * L + 9 / 4 * k * m * L) ≤ (15 + 3 * CY) * f * k * m * L
def EffectiveConstantLogRange : Prop :=
  ∀ (m : ℕ) (L x vE aeff : ℝ) (b w : ℕ → ℝ), 2 ≤ x → (m : ℝ) ≤ x → 2 ≤ L → Real.pi ≤ vE →
    Real.log (vE / Real.pi) ≤ L → 1 ≤ aeff → Real.log aeff ≤ 4 * L →
    (∀ j, j < m → 0 < b j ∧ |w j - b j| ≤ b j / x) →
    -2 ≤ Real.log ((Real.pi / vE)⁻¹ * aeff * ∏ j ∈ range m, w j / b j) ∧
    Real.log ((Real.pi / vE)⁻¹ * aeff * ∏ j ∈ range m, w j / b j) ≤ 6 * L
def GammaTermNegligible : Prop :=
  ∀ (C₁ C₂ ε : ℝ), 0 < C₁ → 0 < C₂ → 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (f m k j : ℕ) (L logΓ : ℝ),
    1 ≤ f → 1 ≤ m → 0 < L → logΓ = C₁ * (m : ℝ) ^ j * f * L → C₂ * (m : ℝ) ^ j * f * L * x ^ ε ≤ k →
    2 * logΓ / ((f : ℝ) * k) ≤ 1
def UpperBoundLogDegreeTau : Prop :=
  ∀ (k m : ℕ) (L : ℝ) (u v b : ℕ → ℝ), 2 ≤ m → Even m → 2 ≤ k → 0 ≤ L →
    (∀ i j, i < j → j < k - 1 → v j < v i) → (∀ i, i < k - 1 → 0 ≤ v i) →
    (∀ j j', j < j' → j' < m → b j < b j') → 0 < b 0 →
    (∀ i j, i < k - 1 → j < m → v i + b j + m ≤ Real.exp (3 * L)) → 0 < vandN u k →
    Real.log (dTau k m (rowPar k v b)) - Real.log (dimVN u k) ≤
      Real.log (vandN v (k - 1)) - Real.log (vandN u k) + 3 / 2 * (k : ℝ) * m * L + 3 / 4 * (m : ℝ) ^ 2 * L
def LowerBoundTermSizeT : Prop :=
  ∀ (m : ℕ) (L lw lG logX : ℝ), 1 ≤ m → 1 ≤ L → 0 ≤ lw → 16 * L ≤ lG →
    (m : ℝ) * lw + (m : ℝ) * lG - 11 * L ≤ logX → (m : ℝ) * L / 2 ≤ logX - 1
def OneSubInvPowBernoulliBound : Prop :=
  ∀ (f : ℕ) (T : ℝ), 2 ≤ T → 1 - 2 * (f : ℝ) / T ≤ (1 - 1 / (T - 1)) ^ f
end Formalism.HermitianLattices.FormalDegreeBoundsAlt


