-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
-- name    : Formalism_PeriodIntegrals_RowWtSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:12.250433+00:00
-- url     : https://prove2.me/theorems/25f237df-4059-4043-b949-0053af7daee2
-- title:
--   Row Wt Span
-- statement:
--   Definitions and structural lemmas for Row Wt Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/RowWtSpan.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.RW
def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1
def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)
def initMinor (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) R)).det
def bideterminant (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : MvPolynomial (Fin r × Fin n) R :=
  ∏ k : Fin K, initMinor R (I k) (hsz k)
def shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin K => t.val < sz k).card
def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f
def BideterminantMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r),
    bideterminant R sz hsz I ∈ dualWeyl R r n (shapeDeg sz)
def BideterminantSpan : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ),
    dualWeyl R k n ν ≤ Submodule.span R {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ f = bideterminant R sz hsz I}
end PI.RW
namespace PI
open PI.RW
def RowWtSpan : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0
end PI


