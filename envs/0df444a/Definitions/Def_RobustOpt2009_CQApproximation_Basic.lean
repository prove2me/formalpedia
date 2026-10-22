-- Prove2me | Definitions.Def_RobustOpt2009_CQApproximation_Basic
-- name    : RobustOpt2009_CQApproximation_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:46.777719+00:00
-- url     : https://prove2.me/theorems/7ff4fcca-d0e9-4b07-815f-58d484fa018d
-- title:
--   Euclidean perturbation bounds and arrow matrices
-- statement:
--   For a real $p\times q$ matrix $M$, define $\operatorname{OperatorBound}(M,r)$ by
--   $$\|Mv\|_2\le r\|v\|_2\quad\text{for every }v\in\mathbb R^q.$$
--   For nonnegative $r$ this is exactly the Euclidean operator-norm bound $\|M\|_{2,2}\le r$. For $u\in\mathbb R^k$ and $t\in\mathbb R$, define
--   $$\operatorname{Arrow}(u,t)=\begin{bmatrix}t&u^T\\u&tI_k\end{bmatrix}.$$
--   For compatible real matrices define the symmetric full-block contribution $L^T\eta R+R^T\eta^TL$. These are the concrete matrix operations used by the least-squares and mixed matrix-cube statements.
--
--   **Formalization Note** Norms of vectors use Mathlib's Euclidean space, not the default function-space norm. The arrow index is a distinguished scalar coordinate followed by $k$ vector coordinates. Zero dimensions are allowed in these basic definitions; theorem hypotheses specify positive problem dimensions where required.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Lemma 6.3.3, printed p. 163 (PDF p. 189); (7.1.1), (7.1.5), Theorem 7.1.3, printed pp. 179–183 (PDF pp. 205–209).

import Mathlib

open Matrix
open scoped BigOperators

namespace RobustOpt2009.CQApproximation

/-- Euclidean operator-norm bound, written without choosing a matrix norm instance. -/
def OperatorBound {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (r : ℝ) : Prop :=
  ∀ v : Fin q → ℝ,
    ‖(WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℝ (Fin p))‖ ≤
      r * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin q))‖

/-- Scalar coordinate first, followed by the residual coordinates. -/
def arrow {k : ℕ} (u : Fin k → ℝ) (t : ℝ) :
    Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ :=
  Matrix.fromBlocks (fun _ _ => t) (fun _ j => u j) (fun i _ => u i)
    (t • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- The symmetric contribution of a full matrix perturbation. -/
def blockTerm {m p q : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (R : Matrix (Fin q) (Fin m) ℝ) (η : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  L.transpose * η * R + R.transpose * η.transpose * L

end RobustOpt2009.CQApproximation


