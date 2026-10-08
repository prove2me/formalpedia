-- Prove2me | Definitions.Def_CompOT_Metric_Defs
-- name    : CompOT_Metric_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:30.402437+00:00
-- url     : https://prove2.me/theorems/ba46f5b5-9a64-4032-801d-ef88da713def
-- title:
--   (2.10), (2.11), (2.17), pp. 370–378 — couplings U(a, b), the Kantorovich cost L_C(a, b), W_p = L_{D^p}^{1/p} and the glued coupling P diag(1/b̃) Q
-- statement:
--   Fix integers $n, m \ge 1$. A **histogram** is a vector $a\in\mathbb R^n$; the **probability simplex** is $\Sigma_n=\{a\in\mathbb R^n_+ : \sum_i a_i=1\}$.
--
--   1. **Couplings (2.10).** For $a\in\mathbb R^n$ and $b\in\mathbb R^m$, the transportation polytope is
--   $$U(a,b)=\{P\in\mathbb R^{n\times m}_+ : P\mathbb 1_m=a,\ P^{\top}\mathbb 1_n=b\},$$
--   the nonnegative matrices whose row sums are $a$ and whose column sums are $b$.
--   2. **Pairing.** For matrices $C,P$ of the same size, $\langle C,P\rangle=\sum_{i,j}C_{i,j}P_{i,j}$. A coupling $P$ is **optimal** for the cost $C$ if $P\in U(a,b)$ and $\langle C,P\rangle\le\langle C,Q\rangle$ for every $Q\in U(a,b)$.
--   3. **Kantorovich cost (2.11).** $L_C(a,b)=\min_{P\in U(a,b)}\langle C,P\rangle$, written as the infimum of $\langle C,P\rangle$ over $U(a,b)$.
--   4. **Entrywise power.** For a square matrix $D\in\mathbb R^{n\times n}$ and a real $p$, $D^p=(D_{i,j}^p)_{i,j}$.
--   5. **Wasserstein distance (2.17).** $\mathrm W_p(a,b)=L_{D^p}(a,b)^{1/p}$; it depends on $D$.
--   6. **The glued coupling** (proof of Proposition 2.2, p. 378). For $b\in\mathbb R^n$ let $\tilde b_j=b_j$ if $b_j>0$ and $\tilde b_j=1$ otherwise, and for $P,Q\in\mathbb R^{n\times n}$ put
--   $$S=P\,\mathrm{diag}(1/\tilde b)\,Q,\qquad S_{i,k}=\sum_j \frac{P_{i,j}Q_{j,k}}{\tilde b_j}.$$
--
--   These are the objects of §2.3–2.4 needed to state that $\mathrm W_p$ is a distance on $\Sigma_n$ and to follow its proof.
--
--   **Formalization Note** The index set $[\![n]\!]=\{1,\dots,n\}$ is `Fin n` (0-based). Matrices are `Matrix (Fin n) (Fin m) ℝ`. $L_C(a,b)$ is a real infimum over the subtype $U(a,b)$. It is only used for $a,b\in\Sigma_n$, where $U(a,b)$ is nonempty (it contains $ab^{\top}$) and compact, so the infimum is a minimum; on an empty $U(a,b)$ the Lean value would be the junk value $0$, which is why every theorem assumes $a,b\in\Sigma_n$. Powers are real powers (`Real.rpow`) with a real exponent $p$, so $1/p$ is a real number, not a truncated natural-number quotient. $\tilde b$ is positive, so $1/\tilde b_j$ is never a division by zero.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.10)–(2.11), pp. 370–371; (2.17), p. 377; proof of Proposition 2.2 (b̃ and S), p. 378

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Metric

open Matrix

/-- The Kantorovich cost `L_C(a, b) = min_{P ∈ U(a, b)} ⟨C, P⟩` of (2.11), written as a
real infimum over `U(a, b)`. It is only used for histograms `a, b` in the probability
simplex, where `U(a, b)` is nonempty and compact (so the infimum is a minimum); on an
empty `U(a, b)` the real infimum is the junk value `0`. -/
noncomputable def otCost {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨅ P : CompOT.Assignment.couplings a b, CompOT.Assignment.frob C (P : Matrix (Fin n) (Fin m) ℝ)

/-- The entrywise power `D^p = (D_{i,j}^p)_{i,j}` (real power `Real.rpow`). -/
noncomputable def powCost {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => D i j ^ p

/-- The `p`-Wasserstein distance (2.17): `W_p(a, b) = L_{D^p}(a, b)^{1/p}`, with real
exponent `p`. -/
noncomputable def W {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (a b : Fin n → ℝ) : ℝ :=
  (otCost (powCost D p) a b) ^ (1 / p)

/-- The vector `b̃` of the proof of Proposition 2.2 (p. 378):
`b̃_j = b_j` if `b_j > 0`, and `b̃_j = 1` otherwise. -/
noncomputable def btilde {n : ℕ} (b : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if 0 < b j then b j else 1

/-- The glued coupling `S = P diag(1/b̃) Q` of the proof of Proposition 2.2 (p. 378). -/
noncomputable def glue {n : ℕ} (b : Fin n → ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  P * Matrix.diagonal (fun j => 1 / btilde b j) * Q

end CompOT.Metric


