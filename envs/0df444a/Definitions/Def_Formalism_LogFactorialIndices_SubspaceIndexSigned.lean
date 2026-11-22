-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
-- name    : Formalism_LogFactorialIndices_SubspaceIndexSigned
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:39:20.221257+00:00
-- url     : https://prove2.me/theorems/ec1eefe6-8e59-46f5-84cd-f1a4da259643
-- title:
--   Subspace Index Signed
-- statement:
--   Definitions and structural lemmas for Subspace Index Signed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SubspaceIndexSigned.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeIndexTer
open Finset Module
open scoped ComplexConjugate Pointwise
def HeightSumBound : Prop :=
  ∀ (W Rho Tt : Type) [Fintype W] [Fintype Rho] [Fintype Tt] (m D : ℕ), 0 < D →
    ∀ (l vG : W → ℝ) (F Aj : ℕ → W → ℝ) (cov : ℕ → ℝ) (wt : ℕ → Rho → ℝ) (a : Tt → ℝ)
      (lcvR muCC logkap hu k logOm B A logTu : ℝ),
    lcvR ≤ D * logkap + (∑ j ∈ Icc 1 m, cov j) + ∑ w, l w * (vG w + ∑ j ∈ Icc 1 m, Aj j w) →
    muCC = lcvR / D →
    (∀ j ∈ Icc 1 m, cov j ≤ D * ((∑ ρ, ((k : ℝ) + 2 * (j : ℝ) - 1 - m) * wt j ρ * logOm) + B)) →
    (∑ w, l w * (vG w + ∑ j ∈ Icc 1 m, Aj j w)) ≤
        D * (2 * (∑ j ∈ Icc 1 m, ∑ w, l w * F j w) + m * B) →
    hu + logkap ≤ (∑ t, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * logTu)) -
        (∑ j ∈ Icc 1 m, ∑ ρ, k * wt j ρ * logOm) + m * B + (Fintype.card Tt : ℝ) * A →
    (∀ j ∈ Icc 1 m, (m : ℝ) * |logOm| * (∑ ρ, wt j ρ) ≤ B) →
    (∀ j ρ, 0 ≤ wt j ρ) →
    muCC + hu - 2 * (∑ j ∈ Icc 1 m, ∑ w, l w * F j w) ≤
      (∑ t, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * logTu)) +
        (Fintype.card Tt : ℝ) * A + 4 * m * B
def MeanBoundAlt : Prop :=
  ∀ (W J : Type) [Fintype W] [Fintype J] (D : ℕ), 0 < D →
    ∀ (l vG g : W → ℝ) (Aj F : J → W → ℝ) (lcvM C : J → ℝ) (lcvR muCC meanLogKap Err : ℝ),
    lcvR ≤ D * meanLogKap + (∑ j, lcvM j) + ∑ w, l w * (vG w + ∑ j, Aj j w) →
    muCC = lcvR / D →
    (∀ w, 0 ≤ l w) → (∀ w, vG w ≤ g w) → (∀ j, lcvM j ≤ D * C j) →
    (∑ w, l w * ((∑ j, Aj j w) - 2 * D * ∑ j, F j w)) ≤ D * Err →
    muCC ≤ meanLogKap + (∑ j, C j) + 2 * (∑ w, l w * ∑ j, F j w) + Err + (∑ w, l w * g w) / D
def CancellationBound : Prop :=
  ∀ (Emb W J : Type) [Fintype Emb] [Nonempty Emb] [Fintype W] [Fintype J] (D : ℕ), 0 < D →
    ∀ (kap lam p : Emb → ℝ) (l g sg : W → ℝ) (F gain E : J → W → ℝ) (C : J → ℝ)
      (muCC h muN muN' Err Rnd : ℝ),
    (∀ σ, 0 < kap σ) → (∀ σ, 0 < lam σ) → (∀ σ, 0 < p σ) →
    muCC ≤ (∑ σ, Real.log (kap σ)) / Fintype.card Emb + (∑ j, C j) +
        2 * (∑ w, l w * ∑ j, F j w) + Err + (∑ w, l w * g w) / D →
    h ≤ (∑ σ, Real.log (p σ ^ 2 / (kap σ * lam σ))) / Fintype.card Emb →
    muN' = muN + 2 * ∑ w, l w * sg w →
    2 * (∑ w, l w * ((∑ j, (gain j w + F j w - E j w)) - sg w)) ≤ Rnd →
    muCC + h - muN' ≤ (∑ j, C j) + (∑ σ, Real.log (p σ ^ 2 / lam σ)) / Fintype.card Emb - muN -
      2 * (∑ w, l w * ∑ j, (gain j w - E j w)) + Err + (∑ w, l w * g w) / D + Rnd
def ProdNormRelDiv : Prop :=
  ∀ (L : Type) [Field L] (σ : L →+* ℂ) (c : L →+* L), (∀ x, σ (c x) = conj (σ x)) →
    ∀ (J : Type) [Fintype J] (D : ℕ) (κ : ℝ) (ρ y G₀ Gμ : L) (z G₀j Gμj : J → L) (s₀ sμ : J → ℂ)
      (E₀ Eμ : ℂ),
    κ ≠ 0 → Gμ ≠ 0 → (∀ j, Gμj j ≠ 0) → (∀ j, s₀ j ≠ 0) →
    E₀ = (κ : ℂ) ^ D * (∏ j, s₀ j) * σ G₀ →
    Eμ = (κ : ℂ) ^ D * σ ρ ^ D * (∏ j, sμ j) * σ Gμ →
    Eμ = σ (y * c y) * E₀ →
    (∀ j, sμ j * σ (Gμj j) = σ (z j * c (z j)) * s₀ j * σ (G₀j j)) →
    y * c y * G₀ / Gμ = ρ ^ D * ∏ j, z j * c (z j) * G₀j j / Gμj j
def ProdNormRelVal : Prop :=
  ∀ (L : Type) [Field L] (c : L →+* L), (∀ x, c (c x) = x) →
    ∀ (v v' : AddValuation L (WithTop ℤ)), (∀ x, v' (c x) = v x) →
    ∀ (J : Type) [Fintype J] (D : ℕ) (ρ y G₀ Gμ : L) (z G₀j Gμj : J → L),
    Gμ ≠ 0 → (∀ j, Gμj j ≠ 0) →
    y * c y * G₀ / Gμ = ρ ^ D * ∏ j, z j * c (z j) * G₀j j / Gμj j →
    v y + v' y + v G₀ + ∑ j, v (Gμj j) = D • v ρ + v Gμ + ∑ j, (v (z j) + v' (z j) + v (G₀j j))
def SubspaceIndexSigned : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (F : ℤ) (M Θ : Submodule O X), IsLat O K X M → IsLat O K X Θ →
      Θ ≤ M.map ((((algebraMap O K ϖ) ^ F) • LinearMap.id : X →ₗ[K] X).restrictScalars O) →
      ∀ W : Submodule K X,
        idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          idx O X M Θ - F * ((finrank K X : ℤ) - finrank K W)
def GoodDualSesq : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (c : K ≃+* K),
    (∀ x : K, x ∈ Set.range (algebraMap O K) ↔ c x ∈ Set.range (algebraMap O K)) →
    ∀ (B : X →ₗ[K] X →ₛₗ[(c : K →+* K)] K), (∀ x, (∀ y, B x y = 0) → x = 0) →
    ∀ (e : X →ₗ[K] X), e ∘ₗ e = e → (∀ x y, B (e x) y = B x (e y)) →
    ∀ A : Submodule O X, IsLat O K X A →
      {x : X | x ∈ LinearMap.range e ∧
          ∀ y ∈ A ⊓ (LinearMap.range e).restrictScalars O, B x y ∈ Set.range (algebraMap O K)} =
        e '' {z : X | ∀ y ∈ A, B z y ∈ Set.range (algebraMap O K)}
def DetBound : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (D g : ℕ) (a : K) (M : Matrix (Fin D) (Fin D) K),
    (∀ i j, ∃ o : O, a ^ g * M i j = algebraMap O K o) →
      ∃ o : O, a ^ (g * D) * M.det = algebraMap O K o
def AvgPair : Prop :=
  ∀ (Emb : Type) [Fintype Emb] (π : Emb ≃ Emb) (a b : Emb → ℝ), (∀ σ, a σ ≤ b σ + b (π σ)) →
    ∑ σ, a σ ≤ 2 * ∑ σ, b σ
def ExpIndex : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (J : ℕ) (A B : Submodule O X), IsLat O K X A → (ϖ ^ J) • A ≤ B → B ≤ A → ∀ W : Submodule K X,
      let AW : Submodule O X := A ⊓ W.restrictScalars O
      let BW : Submodule O X := B ⊓ W.restrictScalars O
      Module.length O (AW ⧸ BW.comap AW.subtype) ≤ ((J * finrank K W : ℕ) : ℕ∞)
def LenGenKilled : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] (d : ℕ) (s : Fin d → M) (n : O), n ≠ 0 → Submodule.span O (Set.range s) = ⊤ →
    (∀ x : M, n • x = 0) →
      Module.length O M ≤ (d : ℕ∞) * IsDiscreteValuationRing.addVal O n
def WeightedMean : Prop :=
  ∀ (S : Type) [Fintype S] (y r n : S → ℝ) (nbar δ : ℝ), 0 < nbar → 0 ≤ δ → δ < 1 →
    (∀ s, 0 ≤ y s) → (∀ s, 0 ≤ r s) → 0 < ∑ s, r s →
    (∀ s, nbar * (1 - δ) ≤ n s ∧ n s ≤ nbar * (1 + δ)) →
      (∑ s, n s * r s * y s) / (∑ s, n s * r s) ≤ ((1 + δ) / (1 - δ)) * ((∑ s, r s * y s) / ∑ s, r s)
def PhFactorial : Prop :=
  ∀ n : ℕ, ph n ≤ Real.log (n.factorial : ℝ) ∧
    (1 ≤ n → Real.log (n.factorial : ℝ) ≤ ph n + Real.log n + 1)
def SupGauss : Prop :=
  ∀ ν : ℝ, 0 < ν →
    (∀ s : ℝ, 0 ≤ s → s ^ ν * Real.exp (-(s ^ 2) / 2) ≤ Real.exp (ph ν / 2)) ∧
      (Real.sqrt ν) ^ ν * Real.exp (-((Real.sqrt ν) ^ 2) / 2) = Real.exp (ph ν / 2)
def LengthUnramified : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Flat O O'],
    Ideal.map (algebraMap O O') (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal O' →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
      Module.length O' (TensorProduct O O' M) = Module.length O M
end Formalism.LatticeIndexTer


