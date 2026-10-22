-- Prove2me | Definitions.Def_RobustOpt2009_CQApproximation_LeastSquares
-- name    : RobustOpt2009_CQApproximation_LeastSquares
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:28.248271+00:00
-- url     : https://prove2.me/theorems/a0cbd8a9-2158-4c4c-837b-2989ddd8bfd0
-- title:
--   Structured least-squares data and the explicit SDP
-- statement:
--   Let $y\in\mathbb R^d$, with residual dimension $k$ and $N$ independent blocks of positive sizes $p_\nu\times q_\nu$. A prescribed subset $I_s$ consists of scalar blocks, all normalized to size $1\times1$. The nominal residual $c(y)$ is affine. Each block has one of the following two forms:
--
--   1. A fixed nonzero $p_\nu\times k$ matrix $L_\nu$ and an affine vector $R_\nu(y)\in\mathbb R^{q_\nu}$ that is not identically zero. Its vector contribution is $L_\nu^T\eta_\nu R_\nu(y)$ and its arrow factors are $\widehat L_\nu=[0,L_\nu]$, $\widehat R_\nu(y)=[R_\nu(y),0]$.
--   2. A fixed nonzero vector $L_\nu\in\mathbb R^{p_\nu}$ and an affine $q_\nu\times k$ matrix $R_\nu(y)$ that is not identically zero. Its vector contribution is $R_\nu(y)^T\eta_\nu^TL_\nu$ and its arrow factors are $\widehat L_\nu=[L_\nu,0]$, $\widehat R_\nu(y)=[0,R_\nu(y)]$.
--
--   An admissible perturbation satisfies $\|\eta_\nu\|_{2,2}\le\rho$ for every block. Robust feasibility means that the Euclidean norm of the nominal residual plus the sum of these contributions is at most $\tau$ for every admissible perturbation.
--
--   The explicit LMI system has symmetric variables $Y_\nu$ and real variables $\lambda_\nu$:
--   $$Y_\nu\succeq\pm(\widehat L_\nu^T\widehat R_\nu(y)+\widehat R_\nu(y)^T\widehat L_\nu),\quad\nu\in I_s,$$
--   $$\begin{bmatrix}Y_\nu-\lambda_\nu\widehat L_\nu^T\widehat L_\nu&\widehat R_\nu(y)^T\\\widehat R_\nu(y)&\lambda_\nu I_{q_\nu}\end{bmatrix}\succeq0,\quad\nu\notin I_s,$$
--   $$\operatorname{Arrow}(c(y),\tau)-\rho\sum_\nu Y_\nu\succeq0.$$
--   The SDP predicate existentially quantifies $Y$ and $\lambda$. Separately, the envelope predicate existentially quantifies symmetric $Y_\nu$ dominating $\widehat L_\nu^T\eta\widehat R_\nu(y)+\widehat R_\nu(y)^T\eta^T\widehat L_\nu$ for all unit-norm blocks, with the same final arrow inequality.
--
--   **Formalization Note** The two constructors implement the factor swapping and perturbation transposition on printed p. 181, so $p_\nu,q_\nu$ refer to the oriented factors. This retains both possibilities for which original factor is constant. No rank bound or equivalence of the finite and semi-infinite systems is assumed. The nonconstant factor may vanish at a particular $y$. Scalar restrictions are automatic for $1\times1$ blocks. The bottom block has positive size, making $\lambda_\nu\ge0$ implicit in its positive semidefiniteness.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, (7.1.1)–(7.1.11), Remark 7.1.1, printed pp. 179–182 (PDF pp. 205–208).

import Definitions.Def_RobustOpt2009_CQApproximation_Basic

open Matrix
open scoped BigOperators

namespace RobustOpt2009.CQApproximation

/-- The two orientations in (7.1.5). In the second constructor η is the transpose
of the original perturbation: the fixed factor always has p rows. -/
inductive LSBlock (d k p q : ℕ) where
  | leftFixed (L : Matrix (Fin p) (Fin k) ℝ)
      (R : (Fin d → ℝ) →ᵃ[ℝ] (Fin q → ℝ))
  | rightFixed (L : Fin p → ℝ)
      (R : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin q) (Fin k) ℝ)

/-- The constant factor in the arrow representation, constructed from original data. -/
def LSBlock.hatL {d k p q : ℕ} (b : LSBlock d k p q) :
    Matrix (Fin p) (Unit ⊕ Fin k) ℝ :=
  match b with
  | .leftFixed L _ => fun i j => Sum.elim (fun _ => 0) (L i) j
  | .rightFixed L _ => fun i j => Sum.elim (fun _ => L i) (fun _ => 0) j

/-- The affine factor in the arrow representation. -/
def LSBlock.hatR {d k p q : ℕ} (b : LSBlock d k p q) (y : Fin d → ℝ) :
    Matrix (Fin q) (Unit ⊕ Fin k) ℝ :=
  match b with
  | .leftFixed _ R => fun i j => Sum.elim (fun _ => R y i) (fun _ => 0) j
  | .rightFixed _ R => fun i j => Sum.elim (fun _ => 0) (R y i) j

/-- Original vector perturbation L(y)ᵀ η R(y), with transposition when the right
factor is constant. -/
def LSBlock.effect {d k p q : ℕ} (b : LSBlock d k p q) (y : Fin d → ℝ)
    (η : Matrix (Fin p) (Fin q) ℝ) : Fin k → ℝ :=
  match b with
  | .leftFixed L R => L.transpose *ᵥ (η *ᵥ R y)
  | .rightFixed L R => (R y).transpose *ᵥ (η.transpose *ᵥ L)

/-- Neither factor is identically zero, as in (7.1.2); the affine factor may vanish
at particular decisions. -/
def LSBlock.Nonzero {d k p q : ℕ} (b : LSBlock d k p q) : Prop :=
  match b with
  | .leftFixed L R => L ≠ 0 ∧ ∃ y, R y ≠ 0
  | .rightFixed L R => L ≠ 0 ∧ ∃ y, R y ≠ 0

/-- Structured real least-squares data after the source's scalar-block normalization. -/
structure LSData (d k N : ℕ) where
  p : Fin N → ℕ
  q : Fin N → ℕ
  p_pos : ∀ i, 0 < p i
  q_pos : ∀ i, 0 < q i
  scalar : Finset (Fin N)
  scalar_size : ∀ i ∈ scalar, p i = 1 ∧ q i = 1
  block : ∀ i, LSBlock d k (p i) (q i)
  nonzero : ∀ i, (block i).Nonzero
  nominal : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ)

/-- Independent operator-norm balls; scalar blocks are 1 by 1, so their scalar
restriction is automatic. -/
def LSData.Admissible {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (η : ∀ i, Matrix (Fin (D.p i)) (Fin (D.q i)) ℝ) : Prop :=
  ∀ i, OperatorBound (η i) ρ

/-- Robust feasibility of the original vector inequality (7.1.3). -/
def LSData.Robust {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∀ η, D.Admissible ρ η →
    ‖(WithLp.toLp 2 (D.nominal y + ∑ i, (D.block i).effect y (η i)) :
      EuclideanSpace ℝ (Fin k))‖ ≤ τ

/-- System (7.1.11), including its lifted variables. The scalar expression uses
an all-ones p by q matrix, which is [1] on the specified 1 by 1 scalar blocks. -/
def LSData.LMI {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ)
    (Y : Fin N → Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ)
    (lam : Fin N → ℝ) : Prop :=
  (∀ i, (Y i).IsHermitian) ∧
  (∀ i ∈ D.scalar,
    let B := (D.block i).hatL.transpose * (Matrix.of (fun (_ : Fin (D.p i)) (_ : Fin (D.q i)) => (1 : ℝ))) * (D.block i).hatR y +
      ((D.block i).hatR y).transpose * (Matrix.of (fun (_ : Fin (D.q i)) (_ : Fin (D.p i)) => (1 : ℝ))) * (D.block i).hatL
    (Y i - B).PosSemidef ∧ (Y i + B).PosSemidef) ∧
  (∀ i, i ∉ D.scalar →
    (Matrix.fromBlocks
      (Y i - lam i • ((D.block i).hatL.transpose * (D.block i).hatL))
      ((D.block i).hatR y).transpose ((D.block i).hatR y)
      (lam i • (1 : Matrix (Fin (D.q i)) (Fin (D.q i)) ℝ))).PosSemidef) ∧
  (arrow (D.nominal y) τ - ρ • ∑ i, Y i).PosSemidef

/-- Projection of the explicit LMI system onto (y,τ). -/
def LSData.SDP {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∃ Y lam, D.LMI ρ y τ Y lam

/-- Intermediate system (7.1.7)-(7.1.8), defined independently of the finite LMIs. -/
def LSData.Envelope {d k N : ℕ} (D : LSData d k N) (ρ : ℝ)
    (y : Fin d → ℝ) (τ : ℝ) : Prop :=
  ∃ Y : Fin N → Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ,
    (∀ i, (Y i).IsHermitian) ∧
    (∀ (i : Fin N) (η : Matrix (Fin (D.p i)) (Fin (D.q i)) ℝ), OperatorBound η 1 →
      (Y i - ((D.block i).hatL.transpose * η * (D.block i).hatR y +
        ((D.block i).hatR y).transpose * η.transpose * (D.block i).hatL)).PosSemidef) ∧
    (arrow (D.nominal y) τ - ρ • ∑ i, Y i).PosSemidef

end RobustOpt2009.CQApproximation


