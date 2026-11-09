-- Prove2me | Definitions.Def_FourBlockIP350_Main_LatticeConvexity
-- name    : FourBlockIP350_Main_LatticeConvexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:35.617697+00:00
-- url     : https://prove2.me/theorems/0c045379-c925-4b55-ad5c-caf861ef7ad2
-- title:
--   Integral-midpoint convexity, discrete convicity and the full convex envelope
-- statement:
--   A real-valued function $h$ on the whole integer lattice is midpoint-convex when
--   $$a+b=2w\ \Longrightarrow\ 2h(w)\le h(a)+h(b).$$
--   It is convex extensible if it agrees on all lattice points with a finite real-valued convex function on the entire real vector space. Discrete convicity uses the source's cone of directions $y-x$ from lower-level points and requires $h(y)\le h(z)$ whenever $z-y$ belongs to that cone, with both points in the specified domain. Cones use all finite nonnegative combinations.
--
--   The coarser lattice is $k\mathbb Z^k$. A dilated simplex is the convex hull of its scaled integer vertices. Affine independence uses the usual zero-sum dependence test. Its convex envelope is the infimum of costs of **all finite** convex representations on $k\mathbb Z^k$:
--   $$C(z)=\inf\left\{\sum_i\lambda_i h(p_i):\lambda_i\ge0,\ \sum_i\lambda_i=1,\ \sum_i\lambda_i p_i=z\right\}.$$
--   The infimum is taken in the extended reals until finiteness is proved; an empty representing set has value $+\infty$ and costs unbounded below have value $-\infty$.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 4–5, 10–12, Definitions 2.3–2.4; Claims 4.2.1–4.2.4

import Mathlib

namespace FourBlockIP350.Main

open scoped BigOperators

abbrev ZVec (k : ℕ) := Fin k → ℤ
abbrev RVec (k : ℕ) := Fin k → ℝ

def realVec {k : ℕ} (x : ZVec k) : RVec k := fun j => (x j : ℝ)

/-- Only integral midpoints are tested: `a+b=2w`. -/
def MidpointConvex {k : ℕ} (h : ZVec k → ℝ) : Prop :=
  ∀ a b w, a + b = (2 : ℤ) • w → 2 * h w ≤ h a + h b

def ConvexExtensible {k : ℕ} (h : ZVec k → ℝ) : Prop :=
  ∃ H : RVec k → ℝ, ConvexOn ℝ Set.univ H ∧ ∀ x, H (realVec x) = h x

/-- Finite nonnegative combinations, including the empty combination. -/
def InCone {k : ℕ} (S : Set (RVec k)) (z : RVec k) : Prop :=
  ∃ a : ℕ, ∃ p : Fin a → RVec k, ∃ lam : Fin a → ℝ,
    (∀ i, p i ∈ S ∧ 0 ≤ lam i) ∧ z = ∑ i, lam i • p i

def DiscreteConvic {k : ℕ} (D : Set (ZVec k)) (h : ZVec k → ℝ) : Prop :=
  ∀ y ∈ D, ∀ z ∈ D,
    InCone {u | ∃ x ∈ D, h x ≤ h y ∧ u = realVec y - realVec x}
      (realVec z - realVec y) → h y ≤ h z

def CoarseLattice (k : ℕ) : Set (ZVec k) := Set.range (fun x : ZVec k => (k : ℤ) • x)

def IndependentPoints {k r : ℕ} (p : Fin (r+1) → ZVec k) : Prop :=
  ∀ lam : Fin (r+1) → ℝ,
    (∑ i, lam i = 0) → (∑ i, lam i • realVec (p i)) = 0 → ∀ i, lam i = 0

def DilatedSimplex {k r : ℕ} (p : Fin (r+1) → ZVec k) : Set (RVec k) :=
  convexHull ℝ (Set.range fun i => realVec ((k : ℤ) • p i))

/-- Affine coordinates on the scaled vertices; independent vertices make these unique
on their affine span. Outside the span the fallback coefficients are zero. -/
def AffineCoordinates {k r : ℕ} (p : Fin (r+1) → ZVec k) (z : RVec k)
    (lam : Fin (r+1) → ℝ) : Prop :=
  (∑ i, lam i = 1) ∧ (∑ i, lam i • realVec ((k : ℤ) • p i)) = z

noncomputable def simplexCoordinates {k r : ℕ} (p : Fin (r+1) → ZVec k)
    (z : RVec k) : Fin (r+1) → ℝ := by
  classical
  exact if hex : ∃ lam, AffineCoordinates p z lam then Classical.choose hex else 0

/-- The affine interpolant is constructed from h and the vertices; it is not an
independent function supplied by a hypothesis. Values outside the affine span are unused. -/
noncomputable def simplexInterpolant {k r : ℕ} (h : ZVec k → ℝ)
    (p : Fin (r+1) → ZVec k) (z : RVec k) : ℝ :=
  ∑ i, simplexCoordinates p z i * h ((k : ℤ) • p i)

/-- Costs of ALL finite convex representations on the coarser lattice. -/
def EnvelopeCosts {k : ℕ} (h : ZVec k → ℝ) (z : RVec k) : Set EReal :=
  {v | ∃ a : ℕ, ∃ p : Fin (a+1) → ZVec k, ∃ lam : Fin (a+1) → ℝ,
    (∀ i, p i ∈ CoarseLattice k ∧ 0 ≤ lam i) ∧
    (∑ i, lam i = 1) ∧ (∑ i, lam i • realVec (p i)) = z ∧
    v = ((∑ i, lam i * h (p i) : ℝ) : EReal)}

noncomputable def ConvexEnvelope {k : ℕ} (h : ZVec k → ℝ) (z : RVec k) : EReal :=
  sInf (EnvelopeCosts h z)

end FourBlockIP350.Main


