-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- name    : Formalism_GradedWeylDivisibility_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:15.38598+00:00
-- url     : https://prove2.me/theorems/6e60159d-0876-4233-94f3-35e82fde29fc
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
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
def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1
def rowW (r n : ℕ) : Fin r × Fin n → (Fin r → ℕ) := fun v => Pi.single v.1 1
def rowDeg {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) : ℕ := ∑ s : Fin n, m (a, s)
def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
def colAdd (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => if v.2 = j then X v + C c * X (v.1, l) else X v
def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)
def rowAct (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => ∑ b : Fin r, C (g v.1 b) * X (b, v.2)
def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)
def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k
def initMinor (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) R)).det
def bideterminant (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : MvPolynomial (Fin r × Fin n) R :=
  ∏ k : Fin K, initMinor R (I k) (hsz k)
def shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin K => t.val < sz k).card
def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det
def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0
def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)
def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f
def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))
def rowNu {r n : ℕ} (ν : Fin n → ℕ) (a : Fin r) : ℕ := if h : a.val < n then ν ⟨a.val, h⟩ else 0
def sub {σ : Type*} [Fintype σ] (U : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ j, C (U i j) * X j
def BideterminantMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r),
    bideterminant R sz hsz I ∈ dualWeyl R r n (shapeDeg sz)
def HWMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    hw R hn ν ∈ dualWeyl R r n ν
def HWNe : Prop :=
  ∀ (R : Type) [CommRing R] [Nontrivial R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
    hw R hn ν ≠ 0
def HWRowWeight : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    IsWeightedHomogeneous (rowW r n) (hw R hn ν) (rowNu (r := r) ν)
def DualWeylSat : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R),
    c ≠ 0 → c • f ∈ dualWeyl R r n ν → f ∈ dualWeyl R r n ν
def DualWeylPoint : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Infinite R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν ↔
      (IsWeightedHomogeneous (colW r n) f ν ∧
        ∀ l j : Fin n, l < j → ∀ c : R, colAdd R l j c f = f)
def DualWeylRowStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν → rowAct R g f ∈ dualWeyl R r n ν
def RowDivStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν → rowDiv R a b k f ∈ dualWeyl R r n ν
def DualWeylRowGraded : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν → weightedHomogeneousComponent (rowW r n) μ f ∈ dualWeyl R r n ν
def DualWeylMap : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν → map φ f ∈ dualWeyl S r n ν
def DualWeylIntRat : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ),
    f ∈ dualWeyl ℤ r n ν ↔ map (Int.castRingHom ℚ) f ∈ dualWeyl ℚ r n ν
def WeylLeDual : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    weyl R r n hn ν ≤ dualWeyl R r n ν
def DualWeylNonDom : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (r n : ℕ) (ν : Fin n → ℕ),
    (∃ l j : Fin n, l < j ∧ ν l < ν j) → dualWeyl R r n ν = ⊥
def BideterminantDominance : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (m : Fin r × Fin n →₀ ℕ), m ∈ (bideterminant R sz hsz I).support →
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, shapeDeg sz t) ∧
    ∑ a : Fin r, rowDeg m a = ∑ t : Fin n, shapeDeg sz t
def DualWeylMul : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν μ : Fin n → ℕ) (f g : MvPolynomial (Fin r × Fin n) R),
    (f ∈ dualWeyl R r n ν → g ∈ dualWeyl R r n μ → f * g ∈ dualWeyl R r n (ν + μ)) ∧
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0
def HWRaise : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ),
    a < b → 1 ≤ k → rowDiv R a b k (hw R hn ν) = 0
def WeylRowDivStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ weyl R r n hn ν → rowDiv R a b k f ∈ weyl R r n hn ν
def RowNuSum : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → ∀ k : ℕ,
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t
def InterlaceRange : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℕ) (ν : Fin n → ℕ),
    (∀ i : Fin n, lam i.succ ≤ ν i ∧ ν i ≤ lam i.castSucc) →
    ∀ i : Fin n, ν i - lam i.succ ≤ min (lam i.castSucc - lam i.succ) (∑ j, (ν j - lam j.succ))
open Formalism.REAL (fockF)
def FockHerm : Prop :=
  ∀ (σ : Type) (f g : MvPolynomial σ ℂ), fockF g f = star (fockF f g)
def FockPos : Prop :=
  ∀ (σ : Type) (f : MvPolynomial σ ℂ), f ≠ 0 → 0 < (fockF f f).re ∧ (fockF f f).im = 0
def FockMono : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (m m' : σ →₀ ℕ),
    fockF (monomial m (1 : ℂ)) (monomial m' 1) =
      if m = m' then ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) else 0
def FockWeightOrth : Prop :=
  ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (μ μ' : M) (f g : MvPolynomial σ ℂ), μ ≠ μ' →
    IsWeightedHomogeneous w f μ → IsWeightedHomogeneous w g μ' → fockF f g = 0
def FockSubAdj : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ) (f g : MvPolynomial σ ℂ),
    fockF (sub U f) g = fockF f (sub U.conjTranspose g)
def FockUnitary : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ), U ∈ Matrix.unitaryGroup σ ℂ →
    ∀ f g : MvPolynomial σ ℂ, fockF (sub U f) (sub U g) = fockF f g
def FockDet : Prop :=
  ∀ r : ℕ,
    fockF (Matrix.of fun a b : Fin r => (X (a, b) : MvPolynomial (Fin r × Fin r) ℂ)).det
      (Matrix.of fun a b : Fin r => (X (a, b) : MvPolynomial (Fin r × Fin r) ℂ)).det =
      ((Nat.factorial r : ℕ) : ℂ)
def FockRowAdj : Prop :=
  ∀ (r n : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f h : MvPolynomial (Fin r × Fin n) ℂ),
    fockF (rowAct ℂ g f) h = fockF f (rowAct ℂ g.conjTranspose h)
def DomPow : Prop :=
  ∀ (r : ℕ) (t : Fin r → ℝ) (μ lam : Fin r → ℕ), (∀ a, 0 ≤ t a) → Antitone t →
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, μ a) ≤ ∑ a : Fin r with a.val < k, lam a) →
    ∑ a : Fin r, μ a = ∑ a : Fin r, lam a →
    ∏ a : Fin r, t a ^ μ a ≤ ∏ a : Fin r, t a ^ lam a
def FockDiagBound : Prop :=
  ∀ (r n : ℕ) (t : Fin r → ℝ) (lam : Fin r → ℕ), (∀ a, 0 ≤ t a) → Antitone t →
    ∀ f : MvPolynomial (Fin r × Fin n) ℂ,
      (∀ m ∈ f.support, ∀ k : ℕ,
          (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, lam a) →
      (∀ m ∈ f.support, ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, lam a) →
      (fockF (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f)
          (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f)).re ≤
        (∏ a : Fin r, t a ^ (2 * lam a)) * (fockF f f).re
def StandardMonomialSpan : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    dualWeyl ℤ r n ν = Submodule.span ℤ
      {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ f = bideterminant ℤ sz hsz I}
def WeylRational : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, c ≠ 0 ∧ c • f ∈ weyl ℤ r n hn ν
def DualWeylDominanceOf : Prop :=
  StandardMonomialSpan →
    ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → Antitone ν → ∀ f ∈ dualWeyl ℤ r n ν, ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a) ∧
      ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, rowNu (r := r) ν a
end Formalism.GradedWeylDivisibility


