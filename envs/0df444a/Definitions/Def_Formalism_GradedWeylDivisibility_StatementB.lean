-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
-- name    : Formalism_GradedWeylDivisibility_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:24.340772+00:00
-- url     : https://prove2.me/theorems/af81bee0-1ad9-4957-85f2-20c131044018
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementB.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
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
namespace Formalism.GradedWeylDivisibility
def RowDivClosed {R : Type*} [CommRing R] {r n : ℕ} (M : Submodule R (MvPolynomial (Fin r × Fin n) R)) : Prop :=
  ∀ (a b : Fin r) (k : ℕ), ∀ f ∈ M, rowDiv R a b k f ∈ M
def fockQ {σ : Type*} (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)
def bidetSpan (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
      shapeDeg sz = ν ∧ f = bideterminant R sz hsz I}
def HWLine : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ f ∈ dualWeyl K r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv K a b k f = 0) →
      ∃ c : K, f = c • hw K hn ν
def HWLineTall : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r n : ℕ) (ν : Fin n → ℕ),
    (∃ s : Fin n, r ≤ s.val ∧ 0 < ν s) →
    ∀ f ∈ dualWeyl K r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv K a b k f = 0) → f = 0
def FockQPos : Prop :=
  ∀ (σ : Type) (f g : MvPolynomial σ ℚ), fockQ f g = fockQ g f ∧ (f ≠ 0 → 0 < fockQ f f)
def FockQBilin : Prop :=
  ∀ (σ : Type) (f f' g : MvPolynomial σ ℚ) (c : ℚ),
    fockQ (f + f') g = fockQ f g + fockQ f' g ∧ fockQ (c • f) g = c * fockQ f g
def FockQRowDivAdj : Prop :=
  ∀ (r n : ℕ) (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℚ),
    fockQ (rowDiv ℚ a b k f) g = fockQ f (rowDiv ℚ b a k g)
def RowDivClosedGraded : Prop :=
  ∀ (r n : ℕ) (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)), RowDivClosed M →
    ∀ f ∈ M, ∀ μ : Fin r → ℕ, weightedHomogeneousComponent (rowW r n) μ f ∈ M
def HWInClosed : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ), M ≤ dualWeyl ℚ r n ν → RowDivClosed M → M ≠ ⊥ →
      hw ℚ hn ν ∈ M
def NablaTallZero : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), (∃ s : Fin n, r ≤ s.val ∧ 0 < ν s) → dualWeyl ℚ r n ν = ⊥
def ClosedEqNabla : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ), M ≤ dualWeyl ℚ r n ν → RowDivClosed M →
      hw ℚ hn ν ∈ M → M = dualWeyl ℚ r n ν
def WeylEqNablaQ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → weyl ℚ r n hn ν = dualWeyl ℚ r n ν
def BideterminantSpanClosed : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ), RowDivClosed (bidetSpan R r n ν)
def HighestWeightVectorMemBideterminantSpan : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    hw R hn ν ∈ bidetSpan R r n ν
def DualWeylModuleEqBideterminantSpanRat : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), Antitone ν → dualWeyl ℚ r n ν = bidetSpan ℚ r n ν
def WeylRationalOf : Prop := WeylEqNablaQ → WeylRational
end Formalism.GradedWeylDivisibility


