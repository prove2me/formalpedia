-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_GFiniteOrderUnipotent
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_GFiniteOrderUnipotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:43.442407+00:00
-- url     : https://prove2.me/theorems/f6e22f38-b667-4a3d-80d9-c7ab3a1bf44f
-- title:
--   GFinite Order Unipotent
-- statement:
--   Definitions and structural lemmas for GFinite Order Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/GFiniteOrderUnipotent.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Polynomial Finset
namespace Formalism.LatticeBaseChangeAlt
def GSeriesBound : Prop :=
  ∀ f N n : ℕ, 8 * f * N + 4 ≤ n →
    Summable (fun m : ℕ => ((m + 2 : ℕ) : ℝ) ^ (((4 * f * N : ℕ) : ℝ) - (n : ℝ) / 2)) ∧
    ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (((4 * f * N : ℕ) : ℝ) - (n : ℝ) / 2) < 1
def GSublatticeCount : Prop :=
  ∀ ρ m : ℕ, 1 ≤ m →
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ
def GStdLat (ρ : ℕ) : AddSubgroup (Fin ρ → ℚ) :=
  (AddMonoidHom.compLeft (Int.castAddHom ℚ) (Fin ρ)).range
def GLatticeCount : Prop :=
  ∀ ρ m : ℕ, 1 ≤ m →
    {L' : AddSubgroup (Fin ρ → ℚ) |
      ((GStdLat ρ ⊓ L').addSubgroupOf (GStdLat ρ)).index = m ∧
      ((GStdLat ρ ⊓ L').addSubgroupOf L').index = m}.Finite ∧
    {L' : AddSubgroup (Fin ρ → ℚ) |
      ((GStdLat ρ ⊓ L').addSubgroupOf (GStdLat ρ)).index = m ∧
      ((GStdLat ρ ⊓ L').addSubgroupOf L').index = m}.ncard ≤ m ^ (2 * ρ)
def GNormBound : Prop :=
  ∀ (f N n : ℕ), 8 * f * N + 4 ≤ n →
  ∀ (ι : Type) (idx : ι → ℕ) (a : ι → ℝ),
    (∀ i, 2 ≤ idx i) →
    (∀ i, 0 ≤ a i ∧ a i ≤ ((idx i : ℕ) : ℝ) ^ (-((n : ℝ) / 2))) →
    (∀ m : ℕ, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (4 * f * N)) →
    Summable a ∧ ∑' i, a i < 1
def GNeumannPositive : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : E →L[ℂ] E), ‖T‖ < 1 →
    (∀ F : E, F ≠ 0 → 0 < RCLike.re (inner ℂ (F + T F) F)) ∧
    (∀ (c : ℝ), 0 < c → ∀ F : E, (c : ℂ) * inner ℂ (F + T F) F = 0 → F = 0)
def GGridNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (p : MvPolynomial σ K) (d : ℕ),
    p ≠ 0 → p.totalDegree ≤ d →
    ∃ x : σ → ℕ, (∀ i, x i ≤ d) ∧ MvPolynomial.eval (fun i => (x i : K)) p ≠ 0
noncomputable def GAdjVec {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (h : V →ₗ[R] V → R) (e e' g : Fin N → V) (b : Fin N) : V :=
  (Matrix.of fun a' a => h (e' a') (e a)).det • g b -
    ∑ a, ∑ a', ((Matrix.of fun a' a => h (e' a') (e a)).adjugate a a' * h (g b) (e a)) • e' a'
def GAdjugateOrth : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (h : V →ₗ[R] V → R) (e e' g : Fin N → V),
    (∀ b c, h (GAdjVec h e e' g b) (e c) = 0) ∧
    (∀ (O : Subring R) (S : AddSubgroup V),
      (∀ (c : R) (v : V), c ∈ O → v ∈ S → c • v ∈ S) →
      (∀ v w, v ∈ S → w ∈ S → h v w ∈ O) →
      (∀ a, e a ∈ S) → (∀ a, e' a ∈ S) → (∀ a, g a ∈ S) → ∀ b, GAdjVec h e e' g b ∈ S)
def GAdjugateNormBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (N : ℕ)
    (h : V →ₗ[ℂ] V → ℂ) (e e' g : Fin N → V) (ρ' : ℝ),
    (∀ x y, ‖h x y‖ ≤ ‖x‖ * ‖y‖) →
    (∀ a, ‖e a‖ ≤ ρ') → (∀ a, ‖e' a‖ ≤ ρ') → (∀ a, ‖g a‖ ≤ ρ') →
    ∀ b, ‖GAdjVec h e e' g b‖ ≤ (N + 1).factorial * ρ' ^ (2 * N + 1)
def GIsotropicNorm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : NumberField.RingOfIntegers K)
    (H : (K →+* ℂ) → ℝ),
    (∀ τ, 0 ≤ H τ) → (∀ τ, ‖τ (a : K)‖ ≤ H τ) → ∑ τ, H τ < 1 → a = 0
def GSchwarzArith : Prop :=
  ∀ (c s ε q F : ℝ), 0 < c → 0 < s → 0 < ε → 0 < q → 0 < F →
    (∀ t : ℝ, 0 < t → t ≤ c / (s * ε) → 1 ≤ Real.exp (-2 * Real.pi * t / q) * (2 : ℝ) ^ F) →
    2 * Real.pi * c / (s * q * F * Real.log 2) ≤ ε
def GFrequencySign : Prop :=
  ∀ (A ν M : ℝ) (k : ℕ), 0 < A →
    (∀ t : ℝ, 1 ≤ t → A * Real.exp (-2 * Real.pi * ν * t) ≤ M * t ^ k) → 0 ≤ ν
def GCauchyArith : Prop :=
  ∀ (ι : Type) [Fintype ι] (α : ι → ℕ),
    ((∏ i, ((α i).factorial : ℝ)) * Real.exp ((∑ i, (α i : ℝ)) / 2) *
      ∏ i, (Real.pi / (α i : ℝ)) ^ ((α i : ℝ) / 2)) ≤
    (Real.pi * Real.exp 1 * (∑ i, (α i : ℝ))) ^ ((∑ i, (α i : ℝ)) / 2)
def GTorsionFree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ l : ℕ, ¬ p ∣ l → ‖(l : K)‖ = 1) →
    ∀ (ζ : K) (n : ℕ), 0 < n → ζ ^ n = 1 →
      ‖ζ - 1‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ζ = 1
def GEigenValuation : Prop :=
  ∀ (r g e : ℕ) (k : ℤ), 1 ≤ r → r + 1 < g → 1 ≤ e → e ≤ r → 0 < k →
    (1 : ℝ) / ((g : ℝ) - 1) < (k : ℝ) / e
def GFiniteOrderUnipotent : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (k : ℕ), 0 < k → A ^ k = 1 →
    A.charpoly = (X - 1) ^ Fintype.card n → A = 1
def GMonomialDet : Prop :=
  ∀ (H : Type) [Group H] [Fintype H] [DecidableEq H] (Y : Type) [MulAction H Y]
    (K : Type) [Field K] (y₀ : Y) (u : Y → K),
    MulAction.IsPretransitive H Y →
    (∀ (h : H) (y : Y), h • y = y → h = 1) →
    u y₀ = 1 → (∀ y, y ≠ y₀ → u y = 0) →
    ∀ y : Y, (Matrix.of fun h h' : H => u ((h * h') • y)).det ≠ 0
def GMarkovIneq : Prop :=
  ∀ (p : ℝ[X]) (a b : ℝ), a < b → ∀ Mx : ℝ, (∀ x ∈ Set.Icc a b, |p.eval x| ≤ Mx) →
    ∀ x ∈ Set.Icc a b, |p.derivative.eval x| ≤ 2 * (p.natDegree : ℝ) ^ 2 / (b - a) * Mx
def GDimDescent : Prop :=
  GMarkovIneq →
  ∀ (p : ℝ[X]) (D n₀ s γ : ℕ), p.natDegree ≤ D → 1 ≤ n₀ → 8 * D ^ 2 * (n₀ + s) ≤ γ →
    (∀ i : ℕ, i ≤ (γ - 1) / n₀ →
      0 ≤ p.eval ((i * n₀ : ℕ) : ℝ) ∧ p.eval ((i * n₀ : ℕ) : ℝ) ≤ p.eval 0) →
    (∀ x ∈ Set.Icc (0 : ℝ) (((γ - 1) / n₀ * n₀ : ℕ) : ℝ),
        |p.derivative.eval x| ≤ 4 * (D : ℝ) ^ 2 * p.eval 0 / γ) ∧
    (1 - 8 * (D : ℝ) ^ 2 * s / γ) * p.eval 0 ≤ p.eval (s : ℝ)
def GPropRJoint : Prop :=
  ∀ (dm d0 dp dpp h B I μρ dimρ ε : ℝ), 0 ≤ ε → ε < 1 → 0 < h → 0 ≤ dimρ →
    (1 - ε) * d0 ≤ dm → (1 - ε) * dp ≤ d0 → (1 - ε) * dpp ≤ dp →
    dm ≤ h * B → h * B ≤ dp → h * I ≤ dpp → μρ ≤ dimρ * I →
    ((1 - ε) * d0 ≤ h * B ∧ h * B ≤ d0 / (1 - ε)) ∧
    μρ ≤ dimρ * d0 / ((1 - ε) ^ 2 * h)
def GSlopeDG : Prop :=
  ∀ (dA dB lam μmin ε' : ℝ) (rA rB : ℕ), 0 < rA → rA ≤ rB → 0 ≤ ε' → 0 ≤ lam →
    (1 - ε') * rB ≤ rA →
    dA - rA * lam + ((rB : ℝ) - rA) * μmin ≤ dB →
    dA / rA - lam - ε' * (|dA / rA| + |μmin|) ≤ dB / rB
def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)
def GOrthogonalEigen : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type) (U : G → E →L[ℂ] E)
    (χ χ' : G → ℂ) (v w : E),
    (∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y) →
    (∀ g, U g v = χ g • v) → (∀ g, U g w = χ' g • w) → (∃ g, χ g ≠ χ' g) →
    inner ℂ v w = 0
end Formalism.LatticeBaseChangeAlt


