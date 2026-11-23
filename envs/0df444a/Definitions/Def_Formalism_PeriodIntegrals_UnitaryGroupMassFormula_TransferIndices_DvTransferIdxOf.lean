-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:50.4198+00:00
-- url     : https://prove2.me/theorems/cb9c1fc0-c76a-4d14-b69a-1dd1e396e7cc
-- title:
--   Dv Transfer Idx Of
-- statement:
--   Definitions and structural lemmas for Dv Transfer Idx Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/DvTransferIdxOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
def IntEl {K : Type} [Field K] [NumberField K] {G : Type} (z : MonoidAlgebra K G) : Prop :=
  ∀ g, z.coeff g ∈ Set.range (algebraMap (𝓞 K) K)
def BlockIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (n : ℕ) (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V)
    (Γ : Matrix (Fin n) (Fin n) (𝓞 K)), Γ.det ≠ 0 →
    (∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = algebraMap (𝓞 K) K (Γ j i) • x) →
    (∀ i, ∀ x ∈ X, Φ i x ∈ Y) → (∀ j, ∀ y ∈ Y, Ψ j y ∈ X) →
    (∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N.FG → Submodule.span K (M : Set V) = ⊤ →
      Submodule.span K (N : Set V) = ⊤ →
      (∀ i, ∀ x ∈ M, x ∈ X → Φ i x ∈ M) → (∀ j, ∀ y ∈ M, y ∈ Y → Ψ j y ∈ M) →
      (∀ i, ∀ x ∈ N, x ∈ X → Φ i x ∈ N) → (∀ j, ∀ y ∈ N, y ∈ Y → Ψ j y ∈ N) →
      Formalism.HN.rkK (M ⊓ Y.restrictScalars (𝓞 K)) = n * Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        |(idxAt w (M ⊓ Y.restrictScalars (𝓞 K)) (N ⊓ Y.restrictScalars (𝓞 K)) : ℝ) -
            (n : ℝ) * (idxAt w (M ⊓ X.restrictScalars (𝓞 K)) (N ⊓ X.restrictScalars (𝓞 K)) : ℝ)| ≤
          (Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) : ℝ) * (vAdd w (algebraMap (𝓞 K) K Γ.det) : ℝ)
def SumIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (S : Type) [Fintype S] [DecidableEq S] (π : S → V →ₗ[K] V) (m : ℕ), 0 < m →
    (∀ s t, π s ∘ₗ π t = if s = t then π s else 0) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N.FG → Submodule.span K (M : Set V) = ⊤ →
      Submodule.span K (N : Set V) = ⊤ →
      (∀ s, ∀ x ∈ M, x ∈ LinearMap.range (∑ t, π t) → ((m : ℕ) : 𝓞 K) • π s x ∈ M) →
      (∀ s, ∀ x ∈ N, x ∈ LinearMap.range (∑ t, π t) → ((m : ℕ) : 𝓞 K) • π s x ∈ N) →
      Formalism.HN.rkK (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) =
                ∑ s, Formalism.HN.rkK (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        |(idxAt w (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K))
              (N ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) : ℝ) -
            ∑ s, (idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
              (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) : ℝ)| ≤
          (Formalism.HN.rkK (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) : ℝ) *
            (vAdd w ((m : ℕ) : K) : ℝ)
def GrpData : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G),
    M1 T P0 →
    (∀ s t, eS T s * eS T t = if s = t then eS T s else 0) ∧
    (∀ s (z : MonoidAlgebra K G), eS T s * z = z * eS T s) ∧
    eps P * eps P = eps P ∧
    (∀ s, IntEl (((Fintype.card G : ℕ) : K) • eS T s)) ∧
    ∀ s, ∃ (a b : Fin (nS T P s) → MonoidAlgebra K G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      Γ.det ≠ 0 ∧
      (∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K Γ.det)‖ ≤ ((Fintype.card G : ℕ) : ℝ) ^ (4 * nS T P s)) ∧
      (∀ i, IntEl (a i)) ∧ (∀ j, IntEl (b j)) ∧
      (∀ i j, b j * a i * (eps P0 * eS T s) = algebraMap (𝓞 K) K (Γ j i) • (eps P0 * eS T s)) ∧
      (∀ i, a i * (eps P0 * eS T s) = eps P * eS T s * a i * (eps P0 * eS T s)) ∧
      (∀ j, b j * (eps P * eS T s) = eps P0 * eS T s * b j * (eps P * eS T s)) ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, a i * b' i * (eps P * eS T s) = eps P * eS T s
def VNonneg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K),
    0 ≤ vAdd w (algebraMap (𝓞 K) K x)
def VFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), x ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => vAdd w (algebraMap (𝓞 K) K x)).Finite
def VSumLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ), x ≠ 0 → 0 < B →
    (∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) →
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) ≤ Real.log B
section Lat
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Lat
end PI.Dv.TIW


