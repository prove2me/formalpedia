-- Prove2me | Definitions.Def_RobustOpt2009_Quadratic_Setup
-- name    : RobustOpt2009_Quadratic_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:20.702798+00:00
-- url     : https://prove2.me/theorems/452fb8c2-41e8-448b-ac55-d01a7fdba1d7
-- title:
--   Side-wise CQI uncertainty and the two explicit LMI certificates
-- statement:
--   For real finite dimensional vectors put $\|x\|_2=\sqrt{\sum_i x_i^2}$. The matrix uncertainty set consists of all $p\times q$ matrices $\eta$ such that $\|\eta u\|_2\le\|u\|_2$ for every $u$. Let $Z=\{\chi:\exists u,\ P\chi+Qu+c\in K\}$. Its regularity condition requires $Z$ closed and either a closed convex pointed cone with a strictly feasible representation, or a cone given by a finite list of homogeneous linear inequalities.
--
--   For nominal residual $b$, factors $L,R$ and right-side coefficients $\sigma,\delta$, robust feasibility means $\|b+L^T\eta R\|_2\le\sigma^T\chi+\delta$ for every independently chosen admissible $\eta,\chi$. The right certificate is $\tau+c^Tv\le\delta$, $P^Tv=\sigma$, $Q^Tv=0$, $v\in K^*$. The two matrix certificates are
--   $$M_1=\begin{pmatrix}\tau I_k&L^T&b\\L&\lambda I_p&0\\b^T&0&\tau-\lambda R^TR\end{pmatrix},\qquad M_2=\begin{pmatrix}\tau I_k-\lambda L^TL&0&b\\0&\lambda I_q&R\\b^T&R^T&\tau\end{pmatrix}.$$
--   The arrow matrix is $\begin{pmatrix}t&b^T\\b&tI_k\end{pmatrix}$. These concrete constructions separate robust feasibility from certificate existence.
--
--   **Formalization Note** Coordinates use finite real function spaces and an explicit Euclidean norm, including dimension zero. The operator ball is expressed by its contraction property, equivalent to induced Euclidean norm at most one. The cone predicates and dual cone are imported from the published ModernConvex definition. The source's vector $p$ is named $c$ to distinguish it from the matrix row count. The closedness requirement is inherited from Section 5.1.2, printed p. 151 (PDF p. 177). As in the literal Section 6.2(ii), the polyhedral branch does not require nonempty uncertainty; finding F6 records the resulting limitation of the printed equivalence.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, equation (1.3.10) and Sections 6.2–6.3, equations (6.3.1), (6.3.4), (6.3.5), Lemma 6.3.3; printed pp. 20, 160–163 (PDF pp. 46, 186–189). Standing closedness convention: Section 5.1.2, printed p. 151 (PDF p. 177).

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix
open scoped BigOperators

noncomputable section

namespace RobustOpt2009.Quadratic

/-- Euclidean norm, not the supremum norm on a function space. -/
def euclidNorm {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The induced Euclidean operator-norm unit ball (6.3.1), expressed without a supremum. -/
def OperatorBall {p q : ℕ} (η : Matrix (Fin p) (Fin q) ℝ) : Prop :=
  ∀ u : Fin q → ℝ, euclidNorm (η *ᵥ u) ≤ euclidNorm u

/-- An explicit finite homogeneous inequality representation of a polyhedral cone. -/
def PolyhedralCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  ∃ (h : ℕ) (H : Matrix (Fin h) (Fin m) ℝ), K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}

/-- The lifted right-side perturbation set of section 6.2 and (1.3.10). -/
def rightSet {m r s : ℕ} (K : Set (Fin m → ℝ))
    (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin m) (Fin s) ℝ)
    (c : Fin m → ℝ) : Set (Fin r → ℝ) :=
  {χ | ∃ u : Fin s → ℝ, P *ᵥ χ + Q *ᵥ u + c ∈ K}

/-- Section 6.2(ii), with the closed-uncertainty convention of section 5.1.2.
The printed polyhedral branch does not require nonemptiness; see finding F6. -/
def RightRegular {m r s : ℕ} (K : Set (Fin m → ℝ))
    (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin m) (Fin s) ℝ)
    (c : Fin m → ℝ) : Prop :=
  IsClosed (rightSet K P Q c) ∧
    ((ModernConvex.ConicDuality.IsConvexCone K ∧
      ModernConvex.ConicDuality.IsPointedSet K ∧ IsClosed K ∧
      ∃ χ u, P *ᵥ χ + Q *ᵥ u + c ∈ interior K) ∨ PolyhedralCone K)

/-- The actual side-wise robust CQI, with independent adversaries (6.2.2). -/
def RobustCQI {k p q r : ℕ} (Z : Set (Fin r → ℝ))
    (b : Fin k → ℝ) (L : Matrix (Fin p) (Fin k) ℝ) (R : Fin q → ℝ)
    (σ : Fin r → ℝ) (δ : ℝ) : Prop :=
  ∀ η : Matrix (Fin p) (Fin q) ℝ, OperatorBall η →
    ∀ χ ∈ Z, euclidNorm (b + Lᵀ *ᵥ (η *ᵥ R)) ≤ σ ⬝ᵥ χ + δ

/-- Right-hand conic certificate (6.3.4.a) = (6.3.5.a). -/
def RightCertificate {m r s : ℕ} (K : Set (Fin m → ℝ))
    (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin m) (Fin s) ℝ)
    (c : Fin m → ℝ) (σ : Fin r → ℝ) (δ τ : ℝ) (v : Fin m → ℝ) : Prop :=
  τ + c ⬝ᵥ v ≤ δ ∧ Pᵀ *ᵥ v = σ ∧ Qᵀ *ᵥ v = 0 ∧
    v ∈ ModernConvex.ConicDuality.dualCone K

/-- Arrow matrix of Lemma 6.3.3, scalar coordinate first. -/
def arrow {k : ℕ} (b : Fin k → ℝ) (t : ℝ) :
    Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ :=
  Matrix.fromBlocks (fun _ _ => t) (fun _ j => b j) (fun i _ => b i)
    (t • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- The complete block matrix (6.3.4.b), with block order k,p,1. -/
def leftAffineLMI {k p q : ℕ} (b : Fin k → ℝ)
    (L : Matrix (Fin p) (Fin k) ℝ) (R : Fin q → ℝ) (τ lam : ℝ) :
    Matrix ((Fin k ⊕ Fin p) ⊕ Unit) ((Fin k ⊕ Fin p) ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ)) Lᵀ L
      (lam • (1 : Matrix (Fin p) (Fin p) ℝ)))
    (fun i _ => Sum.elim b (fun _ => 0) i)
    (fun _ j => Sum.elim b (fun _ => 0) j)
    (fun _ _ => τ - lam * (R ⬝ᵥ R))

/-- The complete block matrix (6.3.5.b), with block order k,q,1. -/
def rightAffineLMI {k p q : ℕ} (b : Fin k → ℝ)
    (L : Matrix (Fin p) (Fin k) ℝ) (R : Fin q → ℝ) (τ lam : ℝ) :
    Matrix ((Fin k ⊕ Fin q) ⊕ Unit) ((Fin k ⊕ Fin q) ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ) - lam • (Lᵀ * L))
      (0 : Matrix (Fin k) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin k) ℝ)
      (lam • (1 : Matrix (Fin q) (Fin q) ℝ)))
    (fun i _ => Sum.elim b R i)
    (fun _ j => Sum.elim b R j)
    (fun _ _ => τ)

end RobustOpt2009.Quadratic


