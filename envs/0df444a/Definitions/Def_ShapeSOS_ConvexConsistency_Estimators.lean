-- Prove2me | Definitions.Def_ShapeSOS_ConvexConsistency_Estimators
-- name    : ShapeSOS_ConvexConsistency_Estimators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:44.949014+00:00
-- url     : https://prove2.me/theorems/ef5c9735-0181-42bf-83f4-ff458a0c987c
-- title:
--   Degree-bounded shape estimators and their distinct optimization problems
-- statement:
--   For a box $B$, write $b_j(x)=(u_j-x_j)(x_j-l_j)$. A convex SOSE candidate is a degree-at-most-$d$ polynomial $g$ admitting the polynomial identity
--   $$H_g=S_0+\sum_j b_jS_j,$$
--   where $S_0$ is an SOS matrix with entry degrees at most $2r$, and each $S_j$ has entry degrees at most $2r-2$. The Hessian consists of actual second polynomial partial derivatives. The derivative SOSE imposes, at finite endpoints, the analogous scalar identities $\partial_i h-K_i^-=s_{i0}^-+\sum_j b_js_{ij}^-$ and $K_i^+-\partial_i h=s_{i0}^++\sum_j b_js_{ij}^+$, with the same caps.
--
--   Both SOSEs minimize the actual empirical loss $\sum_{i<m}(Y_i-g(X_i))^2$ using the fixed attained-minimum selector. The class $C_{n,d}$ requires convexity on $B$; $K_{n,d}$ requires the stated bounded derivatives. Best uniform approximation instead minimizes $\sup_B|g-f|$ over these classes. Equation (10) is represented literally: its constraints involve $\partial_i f$, not $\partial_i h$.
--
--   Identifiability means that evaluating the degree-$d$ polynomial space at the observed points is injective. No existence, identifiability, bound, or convergence property is built into an estimator.
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, pp. 3–4, Definitions 1–4, (3)–(4); pp. 13–14, (9)–(10) and Proposition 3.11

import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open scoped BigOperators

namespace ShapeSOS.ConvexConsistency
noncomputable section
open MvPolynomial

def boxPolynomial {n : ℕ} (B : Box n) (i : Fin n) : Poly n :=
  (C (B.upper i) - X i) * (X i - C (B.lower i))

/-- Equation (3): bounds are on entries, with the subtraction in ℤ. -/
def convexSOSFeasible {n : ℕ} (B : Box n) (d r : ℕ) : Set (Poly n) :=
  {g | g.totalDegree ≤ d ∧ ∃ (S₀ : PMat n) (S : Fin n → PMat n),
    sosMatrixCap (2 * (r : ℤ)) S₀ ∧
    (∀ j, sosMatrixCap (2 * (r : ℤ) - 2) (S j)) ∧
    ∀ a b, RobustPMI.Hierarchy.hessian g a b =
      S₀ a b + ∑ j, boxPolynomial B j * S j a b}

/-- The scalar certificate in (4), with exactly the same hierarchy truncation. -/
def scalarCertificate {n : ℕ} (B : Box n) (r : ℕ) (p : Poly n) : Prop :=
  ∃ (s₀ : Poly n) (s : Fin n → Poly n),
    sosCap (2 * (r : ℤ)) s₀ ∧ (∀ j, sosCap (2 * (r : ℤ) - 2) (s j)) ∧
    p = s₀ + ∑ j, boxPolynomial B j * s j

def derivativeSOSFeasible {n : ℕ} (B : Box n) (K : DerivativeBounds n)
    (d r : ℕ) : Set (Poly n) :=
  {h | h.totalDegree ≤ d ∧ ∀ i,
    (∀ a : ℝ, K.lower i = a → scalarCertificate B r (pderiv i h - C a)) ∧
    (∀ b : ℝ, K.upper i = b → scalarCertificate B r (C b - pderiv i h))}

/-- C_{n,d}, equivalently the polynomial Hessian PSD constraints in (9). -/
def convexClass {n : ℕ} (B : Box n) (d : ℕ) : Set (Poly n) :=
  {p | p.totalDegree ≤ d ∧ ConvexOn ℝ B.carrier (value p)}

def derivativeClass {n : ℕ} (B : Box n) (K : DerivativeBounds n)
    (d : ℕ) : Set (Poly n) :=
  {p | p.totalDegree ≤ d ∧ HasBoundedDerivatives B K (value p)}

/-- Equation (10) literally constrains f, not the optimized polynomial h. -/
def printedDerivativeClass {n : ℕ} (B : Box n) (K : DerivativeBounds n)
    (f : Vec n → ℝ) (d : ℕ) : Set (Poly n) :=
  {h | h.totalDegree ≤ d ∧ HasBoundedDerivatives B K f}

/-- The unnormalized finite empirical squared loss in (3), (4), (9), (10). -/
def empiricalLoss {n : ℕ} (m : ℕ) (xs : ℕ → Vec n) (ys : ℕ → ℝ)
    (p : Poly n) : ℝ := ∑ i ∈ Finset.range m, (ys i - value p (xs i)) ^ 2

def convexSOSE {n : ℕ} (B : Box n) (m d r : ℕ) (xs : ℕ → Vec n)
    (ys : ℕ → ℝ) : Poly n :=
  selectMin (convexSOSFeasible B d r) (empiricalLoss m xs ys)

def derivativeSOSE {n : ℕ} (B : Box n) (K : DerivativeBounds n) (m d r : ℕ)
    (xs : ℕ → Vec n) (ys : ℕ → ℝ) : Poly n :=
  selectMin (derivativeSOSFeasible B K d r) (empiricalLoss m xs ys)

/-- Uniform approximation objective, distinct from empirical squared loss. -/
def approximationLoss {n : ℕ} (B : Box n) (f : Vec n → ℝ) (p : Poly n) : ℝ :=
  uniformError B.carrier (value p) f

def bestConvex {n : ℕ} (B : Box n) (f : Vec n → ℝ) (d : ℕ) : Poly n :=
  selectMin (convexClass B d) (approximationLoss B f)

def bestDerivative {n : ℕ} (B : Box n) (K : DerivativeBounds n)
    (f : Vec n → ℝ) (d : ℕ) : Poly n :=
  selectMin (derivativeClass B K d) (approximationLoss B f)

/-- Identifiability of the degree-d regression design, not independence of raw X vectors. -/
def Identifiable {n : ℕ} (m d : ℕ) (xs : ℕ → Vec n) : Prop :=
  ∀ p q : Poly n, p.totalDegree ≤ d → q.totalDegree ≤ d →
    (∀ i < m, value p (xs i) = value q (xs i)) → p = q

end
end ShapeSOS.ConvexConsistency


