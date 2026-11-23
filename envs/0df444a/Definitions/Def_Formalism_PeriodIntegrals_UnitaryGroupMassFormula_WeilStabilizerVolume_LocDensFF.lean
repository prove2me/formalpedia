-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:49.836515+00:00
-- url     : https://prove2.me/theorems/895365c2-4516-4892-b759-aa7fe5b53d00
-- title:
--   Loc Dens FF
-- statement:
--   Definitions and structural lemmas for Loc Dens FF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFF.lean

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
namespace PI.VolStabW
def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j
def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)
def IsQuadInv (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K) : Prop :=
  (∀ x, σ (σ x) = x) ∧
    ((IsField K ∧ Module.finrank k K = 2 ∧ σ ≠ AlgEquiv.refl) ∨
      ∃ e : K ≃ₐ[k] k × k, ∀ x, e (σ x) = (e x).swap)
def FFCount : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ (k K : Type) [Field k] [Finite k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K), IsQuadInv k K σ → (2 : k) ≠ 0 →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ a : ℕ, a + 2 ≤ M → ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) →
    IsUnit T.det →
    |(Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) /
        (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1| ≤ C * ((Nat.card k : ℝ)⁻¹) ^ 2
def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))
def FFInert : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl → (2 : k) ≠ 0 →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))
end PI.VolStabW


