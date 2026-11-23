-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:40.733326+00:00
-- url     : https://prove2.me/theorems/d8f071a5-bd2f-4fcc-91aa-5842fa922f42
-- title:
--   Transvection Isometry
-- statement:
--   Definitions and structural lemmas for Transvection Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/TransvectionIsometry.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Finset
def KRelFlag : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) (e : ℕ → G),
    (∑ i ∈ Icc 1 p, ∑ j ∈ Icc 1 p, if i < j then e i - e j else 0) =
        ∑ i ∈ Icc 1 p, ((p : ℤ) + 1 - 2 * (i : ℤ)) • e i ∧
      ∑ i ∈ Icc 1 p, ((p : ℤ) + 1 - 2 * (i : ℤ)) • e i =
        -((-2 : ℤ) • ∑ i ∈ Icc 1 (p - 1), ∑ l ∈ Icc 1 i, e l +
          ((p : ℤ) - 1) • ∑ l ∈ Icc 1 p, e l)
def KLogSum : Prop :=
  ∀ (G ι : Type) [AddCommGroup G] [Module ℚ G] (Ψ : Finset ι) (p q : ℕ) (om omc : ι → G)
    (Qd Qc : ι → ℕ → G),
    (∑ τ ∈ Ψ, ((q : ℚ) • om τ + (p : ℚ) • omc τ)) +
        ∑ τ ∈ Ψ, (((-2 : ℚ) • ∑ i ∈ Icc 1 (p - 1), Qd τ i + ((p : ℚ) - 1) • om τ) +
          ((-2 : ℚ) • ∑ i ∈ Icc 1 (q - 1), Qc τ i + ((q : ℚ) - 1) • omc τ)) =
      (-2 : ℚ) • ∑ τ ∈ Ψ, (∑ i ∈ Icc 1 (p - 1), Qd τ i + ∑ i ∈ Icc 1 (q - 1), Qc τ i) +
        (2 * ((p : ℚ) + q) - 2) • ((1 / 2 : ℚ) • ∑ τ ∈ Ψ, (om τ + omc τ))
def GammaL : Prop :=
  ∀ (T D r nW n' ap am : ℝ), 0 ≤ D → 0 ≤ r → r ≤ nW → 0 ≤ n' → n' ≤ nW →
    (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T → 1.9 * T ≤ ap → 1.9 * T ≤ am →
      max T (2 * r + n' + 2 * (T + D + 2)) ≤ ap + am + nW - r + 1
def TraceAmGm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α : F),
    (∀ σ : F →+* ℂ, (σ α).im = 0 ∧ 0 < (σ α).re) →
      (Module.finrank ℚ F : ℝ) * |((Algebra.norm ℚ α : ℚ) : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ F) ≤
        ((Algebra.trace ℚ F α : ℚ) : ℝ)
def OrderSharp : Prop :=
  ∀ (lamQ lamQs lam1 lB d' rd f : ℝ), 0 < f → 0 < rd → 0 ≤ d' → 0 ≤ lB → 0 ≤ lamQs → 0 < lam1 →
    lamQ ^ 2 ≤ (1 / 2) * lB * lamQs ^ 2 → lamQs * lam1 ≤ d' → 2 * f / rd ^ 2 ≤ lam1 ^ 2 →
      lamQ ^ 2 ≤ lB * d' ^ 2 * rd ^ 2 / (4 * f)
def MinimaTies : Prop :=
  ∀ (𝕜 V : Type) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (Λ : Set V) (N : V → ℝ) (n : ℕ)
    (m : ℕ → ℝ) (v : ℕ → V), Monotone m → (∀ i < n, v i ∈ Λ ∧ N (v i) ≤ m i) →
    LinearIndependent 𝕜 (fun i : Fin n => v i) →
    (∀ (k : ℕ) (w : Fin (k + 1) → V), k < n → LinearIndependent 𝕜 w → (∀ j, w j ∈ Λ) →
      ∃ j, m k ≤ N (w j)) →
    ∀ s < n, ∀ z ∈ Λ, N z < m s → z ∈ Submodule.span 𝕜 (v '' {i | i < s})
def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2
def ReducedFlagBasis : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (u v : Fin n → V),
    LinearIndependent ℝ u → (∀ i, v i ∈ Submodule.span ℤ (Set.range u)) → LinearIndependent ℝ v →
      ∃ b : Fin n → V, (∀ i, b i ∈ Submodule.span ℤ (Set.range u)) ∧
        (∀ s : ℕ, s ≤ n →
          (Submodule.span ℤ (b '' {i | (i : ℕ) < s}) : Set V) =
            (Submodule.span ℤ (Set.range u) : Set V) ∩ Submodule.span ℝ (v '' {i | (i : ℕ) < s})) ∧
        ∀ s : Fin n, ‖b s‖ ^ 2 ≤ ‖v s‖ ^ 2 + (1 / 4) * ∑ i ∈ univ.filter (fun i : Fin n => i < s), ‖v i‖ ^ 2
def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)
def ThickArith : Prop :=
  ∀ (g c : ℕ) (R0 : ℝ), 1 ≤ g + c → 90 * ((g : ℝ) + c) ≤ R0 ^ 2 →
    (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g) * Real.exp (-R0 ^ 2 / 16) ≤
        4 * Real.exp (3.3 * ((g : ℝ) + c) - R0 ^ 2 / 16) ∧
      4 * Real.exp (3.3 * ((g : ℝ) + c) - R0 ^ 2 / 16) ≤ 1 / 2
def TransvectionIsometry : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, h w v = starRingEnd ℂ (h v w)) → ∀ x : V, h x x = 0 →
      (∀ (β : ℂ) (v w : V), β + starRingEnd ℂ β = 0 →
        h (v + (β * h v x) • x) (w + (β * h w x) • x) = h v w) ∧
      ∀ (β β' : ℂ) (v : V),
        let u := v + (β' * h v x) • x
        u + (β * h u x) • x = v + ((β + β') * h v x) • x
def MultCount : Prop :=
  ∀ (N : ℕ) (la : Fin N → ℝ) (la1 laN : ℝ), 0 < la1 → (∀ i, la1 ≤ la i ∧ la i ≤ laN) →
    ∏ i, (1 + 4 * la i / la1) ^ N ≤ (5 * laN / la1) ^ (N ^ 2)
def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))
def GammaHalf : Prop :=
  ∀ g : ℕ, 1 ≤ g →
    (1 / 2 : ℝ) ≤ Real.pi ^ (-(g : ℝ)) *
      ∫ z in {z : EuclideanSpace ℝ (Fin (2 * g)) | ‖z‖ ^ 2 ≤ 2 * (g : ℝ)}, Real.exp (-‖z‖ ^ 2)
def CharConst : Prop :=
  ∀ (ρ d' rd RR φ ms chi : ℝ), 0 ≤ ρ → 0 ≤ d' → 0 ≤ rd → 0 ≤ ms → 0 ≤ chi →
    chi ≤ 1.5 * (30 * ρ ^ 2 * (d' * rd * ms)) → ms ^ 2 ≤ 4 * RR * d' ^ 2 * φ →
      chi ^ 2 ≤ 8100 * ρ ^ 4 * d' ^ 4 * rd ^ 2 * RR * φ
end Formalism.LatticeBaseChangeAlt


