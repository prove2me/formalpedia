-- Prove2me | Definitions.Def_RobustOpt2009_Adjustable_Model
-- name    : RobustOpt2009_Adjustable_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:59.617024+00:00
-- url     : https://prove2.me/theorems/862917f4-c6f7-47e8-a199-578a2bcba26c
-- title:
--   Ellipsoidal quadratic policies, lifted moments, and the explicit SDP
-- statement:
--   Let $L,r,n,m$ be nonnegative integers, let $k_j$ be the observation dimension of variable $j$, and let $Q\in\mathbb R^{r\times L}$ and $P_j\in\mathbb R^{k_j\times L}$. The uncertainty set is $Z=\{z:\sum_a(Qz)_a^2\le1\}$. The raw quadratic lift is $\widehat z=\begin{bmatrix}0&z^T\\z&zz^T\end{bmatrix}$. Its convex hull and the candidate moment region $\{\begin{bmatrix}0&v^T\\v&W\end{bmatrix}:\begin{bmatrix}1&v^T\\v&W\end{bmatrix}\succeq0,\operatorname{Tr}(QWQ^T)\le1\}$ are defined separately.
--
--   The model stores all affine data of $\min\{c(z)^Tx+d(z):A(z)x\ge b(z)\}$. A policy has coefficients $p_j,q_j,R_j$ and evaluates to
--   $$X_j(z)=p_j+q_j^TP_jz+(P_jz)^TR_j(P_jz).$$
--   Fixed recourse means that all perturbation coefficients in $c_j$ and column $A_j$ vanish whenever $P_j\ne0$. No such condition is imposed when $P_j=0$. The robust epigraph requires the original constraints and $c(z)^TX(z)+d(z)\le t$ for every $z\in Z$.
--
--   The signed slack rows are $A_i(z)X(z)-b_i(z)$ and $t-c(z)^TX(z)-d(z)$. The module explicitly constructs their constant, linear and symmetric quadratic coefficients $\alpha_i,\beta_i,\Gamma_i$ from the model and policy parameters, using $(R_j+R_j^T)/2$. For each row it defines the matrix
--   $$M_i=\begin{bmatrix}\alpha_i-\lambda_i&\beta_i^T/2\\\beta_i/2&\Gamma_i+\lambda_iQ^TQ\end{bmatrix}.$$
--   The SDP has linear objective $t$ with $\lambda_i\ge0$ and $M_i\succeq0$. Its coordinates are precisely the threshold, the policy coefficients, and one multiplier per signed row. The definitions also give the total observation size $K=\sum_jk_j$, a variable bound $B=1+n(1+K+K^2)+(m+1)$, and the dense storage count $(N+1)(m+1)(L+1)^2$, where $N$ is the number of SDP variables.
--
--   An optimal robust policy is a feasible pair $(t,y)$ with threshold no larger than that of any other feasible pair. An optimal SDP vector is feasible with threshold no larger than any feasible SDP vector. Both predicates are defined explicitly; neither asserts that an optimizer exists.
--
--   **Formalization Note** All objects are concrete definitions, without any assumed equivalence between robust feasibility and the SDP. Matrices use a distinguished top-left index. Full quadratic coefficient arrays avoid choosing an upper-triangular indexing convention; their skew parts are redundant. Dimensions may be zero. The squared norm is Euclidean, even though vectors are finite functions.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Definition 14.3.1, printed p. 371 (PDF p. 397); (14.3.5)–(14.3.6), printed pp. 373–375 (PDF pp. 399–401); Lemma 14.3.7 and Corollary 14.3.8, printed pp. 384–385 (PDF pp. 410–411).

import Mathlib

open scoped BigOperators
noncomputable section

namespace RobustOpt2009.Adjustable

/-- The book's ellipsoid, using the Euclidean squared norm (not the Pi sup norm). -/
def ellipsoid {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) : Set (Fin L → ℝ) :=
  {z | ∑ i, (Q.mulVec z i) ^ 2 ≤ 1}

/-- Index `none` is the distinguished top-left coordinate. -/
def momentBlock {L : ℕ} (s : ℝ) (v : Fin L → ℝ)
    (W : Matrix (Fin L) (Fin L) ℝ) : Matrix (Option (Fin L)) (Option (Fin L)) ℝ
  | none, none => s
  | none, some j => v j
  | some i, none => v i
  | some i, some j => W i j

def quadraticLift {L : ℕ} (z : Fin L → ℝ) :=
  momentBlock 0 z (fun i j => z i * z j)

def liftedHull {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) :=
  convexHull ℝ (quadraticLift '' ellipsoid Q)

/-- The unshifted lift has 0 in its corner; only the PSD test has 1. -/
def momentRegion {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ) :
    Set (Matrix (Option (Fin L)) (Option (Fin L)) ℝ) :=
  {M | ∃ (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ),
    M = momentBlock 0 v W ∧ (momentBlock 1 v W).PosSemidef ∧
      Matrix.trace (Q * W * Q.transpose) ≤ 1}

/-- Affinely uncertain LO data for (14.3.6), with a prescribed observation map per variable. -/
structure Model (L r n m : ℕ) (k : Fin n → ℕ) where
  Q : Matrix (Fin r) (Fin L) ℝ
  P : (j : Fin n) → Matrix (Fin (k j)) (Fin L) ℝ
  A0 : Matrix (Fin m) (Fin n) ℝ
  A1 : Fin L → Matrix (Fin m) (Fin n) ℝ
  b0 : Fin m → ℝ
  b1 : Fin L → Fin m → ℝ
  c0 : Fin n → ℝ
  c1 : Fin L → Fin n → ℝ
  d0 : ℝ
  d1 : Fin L → ℝ

/-- One constant, k_j linear coefficients and k_j² quadratic coefficients per policy. -/
abbrev CoeffIndex {n : ℕ} (k : Fin n → ℕ) :=
  (j : Fin n) × (Unit ⊕ (Fin (k j) ⊕ (Fin (k j) × Fin (k j))))

abbrev Row (m : ℕ) := Option (Fin m)

/-- Threshold, policy coefficients, and one multiplier for each row including the objective. -/
abbrev VarIndex {n : ℕ} (k : Fin n → ℕ) (m : ℕ) :=
  Unit ⊕ (CoeffIndex k ⊕ Row m)

variable {L r n m : ℕ} {k : Fin n → ℕ}

def constantCoeff (y : CoeffIndex k → ℝ) (j : Fin n) := y ⟨j, Sum.inl ()⟩
def linearCoeff (y : CoeffIndex k → ℝ) (j : Fin n) (a : Fin (k j)) :=
  y ⟨j, Sum.inr (Sum.inl a)⟩
def quadCoeff (y : CoeffIndex k → ℝ) (j : Fin n) (a b : Fin (k j)) :=
  y ⟨j, Sum.inr (Sum.inr (a, b))⟩

/-- Literal quadratic polynomial of P_j z, with all cross terms. -/
def policy (D : Model L r n m k) (y : CoeffIndex k → ℝ) (z : Fin L → ℝ)
    (j : Fin n) : ℝ :=
  constantCoeff y j + ∑ a, linearCoeff y j a * (D.P j).mulVec z a +
    ∑ a, ∑ b, quadCoeff y j a b * (D.P j).mulVec z a * (D.P j).mulVec z b

/-- Definition 14.3.1: certainty is required only on columns with nonzero observation maps. -/
def FixedRecourse (D : Model L r n m k) : Prop :=
  ∀ j, D.P j ≠ 0 → ∀ l, D.c1 l j = 0 ∧ ∀ i, D.A1 l i j = 0

/-- The exact robust epigraph in the prescribed quadratic policy class. -/
def robustEpigraph (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ) : Prop :=
  ∀ z ∈ ellipsoid D.Q,
    (∑ j, (D.c0 j + ∑ l, z l * D.c1 l j) * policy D y z j) +
      D.d0 + (∑ l, z l * D.d1 l) ≤ t ∧
    ∀ i, D.b0 i + (∑ l, z l * D.b1 l i) ≤
      ∑ j, (D.A0 i j + ∑ l, z l * D.A1 l i j) * policy D y z j

/-- Signed rows: `none` is t - c(z)'x - d(z); `some i` is A_i(z)x - b_i(z). -/
def rowCoeff0 (D : Model L r n m k) : Row m → Fin n → ℝ
  | none => fun j => -D.c0 j
  | some i => D.A0 i

def rowCoeff1 (D : Model L r n m k) : Row m → Fin L → Fin n → ℝ
  | none => fun l j => -D.c1 l j
  | some i => fun l j => D.A1 l i j

def rowOffset0 (D : Model L r n m k) (t : ℝ) : Row m → ℝ
  | none => t - D.d0
  | some i => -D.b0 i

def rowOffset1 (D : Model L r n m k) : Row m → Fin L → ℝ
  | none => fun l => -D.d1 l
  | some i => fun l => -D.b1 l i

def pulledLinear (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n)
    (l : Fin L) : ℝ := ∑ a, linearCoeff y j a * D.P j a l

/-- Symmetrization changes no quadratic polynomial; no restriction is placed on y. -/
def pulledQuadratic (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n)
    (l h : Fin L) : ℝ :=
  ∑ a, ∑ b, ((quadCoeff y j a b + quadCoeff y j b a) / 2) * D.P j a l * D.P j b h

def residualConstant (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ)
    (i : Row m) : ℝ := rowOffset0 D t i + ∑ j, rowCoeff0 D i j * constantCoeff y j

def residualLinear (D : Model L r n m k) (y : CoeffIndex k → ℝ)
    (i : Row m) (l : Fin L) : ℝ :=
  rowOffset1 D i l + ∑ j,
    (rowCoeff0 D i j * pulledLinear D y j l + rowCoeff1 D i l j * constantCoeff y j)

def residualQuadratic (D : Model L r n m k) (y : CoeffIndex k → ℝ)
    (i : Row m) (l h : Fin L) : ℝ :=
  ∑ j, rowCoeff0 D i j * pulledQuadratic D y j l h

def assemble (t : ℝ) (y : CoeffIndex k → ℝ) (lam : Row m → ℝ) : VarIndex k m → ℝ
  | Sum.inl _ => t
  | Sum.inr (Sum.inl a) => y a
  | Sum.inr (Sum.inr i) => lam i

def threshold (u : VarIndex k m → ℝ) : ℝ := u (Sum.inl ())
def coefficients (u : VarIndex k m → ℝ) (a : CoeffIndex k) : ℝ := u (Sum.inr (Sum.inl a))
def multiplier (u : VarIndex k m → ℝ) (i : Row m) : ℝ := u (Sum.inr (Sum.inr i))

/-- Explicit LMI of order L+1; its affine dependence on all decision variables is a theorem. -/
def certificateMatrix (D : Model L r n m k) (u : VarIndex k m → ℝ) (i : Row m) :=
  momentBlock (residualConstant D (threshold u) (coefficients u) i - multiplier u i)
    (fun l => residualLinear D (coefficients u) i l / 2)
    (fun l h => residualQuadratic D (coefficients u) i l h +
      multiplier u i * (D.Q.transpose * D.Q) l h)

/-- The SDP minimizes `threshold u` over this explicitly defined feasible set. -/
def sdpFeasible (D : Model L r n m k) (u : VarIndex k m → ℝ) : Prop :=
  (∀ i, 0 ≤ multiplier u i) ∧ ∀ i, (certificateMatrix D u i).PosSemidef

/-- An attained minimum of the original restricted robust program; existence is not assumed. -/
def robustOptimal (D : Model L r n m k) (t : ℝ) (y : CoeffIndex k → ℝ) : Prop :=
  robustEpigraph D t y ∧ ∀ (s : ℝ) (y' : CoeffIndex k → ℝ),
    robustEpigraph D s y' → t ≤ s

/-- An attained minimum of the explicit SDP with its linear threshold objective. -/
def sdpOptimal (D : Model L r n m k) (u : VarIndex k m → ℝ) : Prop :=
  sdpFeasible D u ∧ ∀ v : VarIndex k m → ℝ, sdpFeasible D v → threshold u ≤ threshold v

def observationSize (k : Fin n → ℕ) : ℕ := ∑ j, k j

def variableBound (k : Fin n → ℕ) (m : ℕ) : ℕ :=
  1 + n * (1 + observationSize k + observationSize k ^ 2) + (m + 1)

/-- Dense affine LMI storage: constant matrix plus one coefficient matrix per variable. -/
def denseLMICoefficientCount (L : ℕ) (k : Fin n → ℕ) (m : ℕ) : ℕ :=
  (Fintype.card (VarIndex k m) + 1) * Fintype.card (Row m) *
    Fintype.card (Option (Fin L)) ^ 2

end RobustOpt2009.Adjustable


