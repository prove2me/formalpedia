-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:21.855882+00:00
-- url     : https://prove2.me/theorems/c74b5478-2a8c-4222-a095-61e60d7ad635
-- title:
--   Statements Coinv
-- statement:
--   Definitions and structural lemmas for Statements Coinv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsCoinv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace Coinv
def IsUnderStaircase {f n : ℕ} (e : Fin f × Fin n →₀ ℕ) : Prop := ∀ v, e v ≤ (v.2 : ℕ)
def staircase (f n : ℕ) : Fin f × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (v.2 : ℕ)
def underStaircaseSpan (K : Type*) [Field K] (f n : ℕ) :
    Submodule K (MvPolynomial (Fin f × Fin n) K) :=
  Submodule.span K {P | ∃ e : Fin f × Fin n →₀ ℕ, IsUnderStaircase e ∧ P = monomial e 1}
def coinvTop (f n : ℕ) : ℕ := f * (n * (n - 1) / 2)
end Coinv
open Coinv
def CoinvStepReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (b : Fin f) (k : Fin n)
    (e : Fin f × Fin n →₀ ℕ), (k : ℕ) + 1 ≤ e (b, k) →
    ∃ (T : Finset (Fin f × Fin n →₀ ℕ)) (c : (Fin f × Fin n →₀ ℕ) → K),
      (∀ e' ∈ T, (∀ u : Fin f × Fin n, (u.1 < b ∨ (u.1 = b ∧ u.2 < k)) → e' u = e u) ∧
        e' (b, k) < e (b, k)) ∧
      monomial e (1 : K) - ∑ e' ∈ T, c e' • monomial e' (1 : K) ∈ psumIdeal K f n
def CoinvMonomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (e : Fin f × Fin n →₀ ℕ),
    ∃ v ∈ underStaircaseSpan K f n, monomial e (1 : K) - v ∈ psumIdeal K f n
def CoinvPolynomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    ∃ v ∈ underStaircaseSpan K f n, H - v ∈ psumIdeal K f n
def HomogeneousComponentMul.Statement : Prop :=
  ∀ (σ R : Type) [CommSemiring R] (p a : MvPolynomial σ R) (m d : ℕ), p.IsHomogeneous m →
    homogeneousComponent d (p * a) = if m ≤ d then p * homogeneousComponent (d - m) a else 0
def CoinvIdealRepresentation.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n →
    ∃ a : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * a m b
def CoinvIdealComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n → ∀ d : ℕ,
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      homogeneousComponent d J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b
def CoinvStaircaseDegree.Statement : Prop :=
  ∀ (f n : ℕ) (e : Fin f × Fin n →₀ ℕ), IsUnderStaircase e →
    e.degree ≤ coinvTop f n ∧ (e.degree = coinvTop f n → e = staircase f n)
def CoinvStaircaseComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (v : MvPolynomial (Fin f × Fin n) K),
    v ∈ underStaircaseSpan K f n →
    (∀ d, coinvTop f n < d → homogeneousComponent d v = 0) ∧
    ∃ c : K, homogeneousComponent (coinvTop f n) v = C c * monomial (staircase f n) 1
def CoinvAboveTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n d : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous d → coinvTop f n < d →
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b
def CoinvAtTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous (coinvTop f n) →
    ∃ c : K, H - C c * monomial (staircase f n) 1 ∈ psumIdeal K f n
def CoinvAboveTopGeneral.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (β ι : Type) [Fintype β] [DecidableEq β] [Fintype ι]
    [DecidableEq ι] (d : ℕ) (H : MvPolynomial (β × ι) K), H.IsHomogeneous d →
    Fintype.card β * (Fintype.card ι * (Fintype.card ι - 1) / 2) < d →
    ∃ Q : ℕ → β → MvPolynomial (β × ι) K, (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 (Fintype.card ι), ∑ b : β, (∑ i : ι, X (b, i) ^ m) * Q m b
def CoinvAtTopGeneral.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (β ι : Type) [Fintype β] [DecidableEq β] [Fintype ι]
    [DecidableEq ι] (o : ι ≃ Fin (Fintype.card ι)) (H : MvPolynomial (β × ι) K),
    H.IsHomogeneous (Fintype.card β * (Fintype.card ι * (Fintype.card ι - 1) / 2)) →
    ∃ c : K, H - C c * ∏ b : β, ∏ i : ι, X (b, i) ^ (o i : ℕ) ∈
      Ideal.span {P | ∃ (m : ℕ) (b : β), 1 ≤ m ∧ m ≤ Fintype.card ι ∧ P = ∑ i : ι, X (b, i) ^ m}
def VandermondeOfHomogeneous.Statement : Prop :=
  ∀ (σ R : Type) [CommRing R] (m : ℕ) (v : Fin m → MvPolynomial σ R),
    (∀ i, (v i).IsHomogeneous 1) → (vandermondeOf v).IsHomogeneous (m * (m - 1) / 2)
def RestPolynomialHomogeneous.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock),
    (restPolynomial f r a c).IsHomogeneous (topDegree f (r + a) + 1)
def RestPolynomialHomogeneousDecomposition.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), ∃ Q : ℕ → Fin f → RootRing f (r + a),
    IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q ∧
    ∀ k τ, (Q k τ).IsHomogeneous (topDegree f (r + a) + 1 - k)
end
end GroundTheory.Heights₂.Heights.RestTerms


