-- Prove2me | Definitions.Def_SignSymRat_Hierarchy_Setting
-- name    : SignSymRat_Hierarchy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:20.75902+00:00
-- url     : https://prove2.me/theorems/531aa0cb-eb84-45ae-9bd0-e8941c0209d0
-- title:
--   (SRFO), Assumption 1.1 and quadratic modules
-- statement:
--   Fix $n$ variables, $m$ polynomial constraints and $N$ rational summands, with real polynomials $p_i,q_i,g_j$. The feasible set and objective are
--
--   $$K=\{x\in\mathbb R^n:g_j(x)\ge0\ (j\in[m])\},\qquad F(x)=\sum_{i=1}^{N}\frac{p_i(x)}{q_i(x)},\qquad \rho=\inf_{x\in K}F(x).$$
--
--   Assumption 1.1 is compactness of $K$ and strict positivity of every $q_i$ on $K$. This module also defines the sum-of-squares quadratic module $Q(g)$, its degree-$2k$ truncation $Q_k(g)$, the Archimedean condition $M-\sum_a x_a^2\in Q(g)$ for some $M>0$, the degree threshold $d_{\min}$, and the exact polynomial programs (D) and (Dk). They are the common data and dense comparison program for the later sparse hierarchy.
--
--   **Formalization Note** Paper index $1$ is Lean index `0`; $i\in[N]\setminus\{1\}$ is `i ≠ 0`. All optimal values are extended real numbers, with $\rho=+\infty$ when $K$ is empty and value $-\infty$ for an infeasible dual program.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, pp. 1–6, (SRFO), (1.1), Assumption 1.1, Definition 2.1, (D), (Dk)

import Mathlib

open MvPolynomial

namespace SignSymRat.Hierarchy

/-- Data of the sum-of-ratios problem (SRFO). -/
structure SRFO (n m N : ℕ) where
  p : Fin N → MvPolynomial (Fin n) ℝ
  q : Fin N → MvPolynomial (Fin n) ℝ
  g : Fin m → MvPolynomial (Fin n) ℝ

variable {n m N : ℕ}

/-- The basic closed semialgebraic set in (1.1). -/
def semialgK (g : Fin m → MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, 0 ≤ eval x (g j)}

def SRFO.K (P : SRFO n m N) : Set (Fin n → ℝ) := semialgK P.g

noncomputable def SRFO.obj (P : SRFO n m N) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin N, eval x (P.p i) / eval x (P.q i)

def SRFO.Assumption11 (P : SRFO n m N) : Prop :=
  IsCompact P.K ∧ ∀ i : Fin N, ∀ x ∈ P.K, 0 < eval x (P.q i)

noncomputable def SRFO.rho (P : SRFO n m N) : EReal :=
  ⨅ x ∈ P.K, (P.obj x : EReal)

/-- The k-th truncated quadratic module Q_k(g). -/
def truncQM (g : Fin m → MvPolynomial (Fin n) ℝ) (k : ℕ) :
    Set (MvPolynomial (Fin n) ℝ) :=
  {f | ∃ (σ₀ : MvPolynomial (Fin n) ℝ) (σ : Fin m → MvPolynomial (Fin n) ℝ),
    IsSumSq σ₀ ∧ σ₀.totalDegree ≤ 2 * k ∧
    (∀ j, IsSumSq (σ j) ∧ (σ j * g j).totalDegree ≤ 2 * k) ∧
    f = σ₀ + ∑ j, σ j * g j}

/-- The untruncated quadratic module Q(g). -/
def QM (g : Fin m → MvPolynomial (Fin n) ℝ) : Set (MvPolynomial (Fin n) ℝ) :=
  ⋃ k : ℕ, truncQM g k

/-- Definition 2.1. -/
def IsArchimedean (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ C M - ∑ i : Fin n, X i ^ 2 ∈ QM g

/-- The ceiling of half the total degree. -/
def halfDeg (f : MvPolynomial (Fin n) ℝ) : ℕ := (f.totalDegree + 1) / 2

/-- The maximum half-degree on p. 4. -/
def SRFO.dmin (P : SRFO n m N) : ℕ :=
  max (Finset.univ.sup fun i : Fin N => max (halfDeg (P.p i)) (halfDeg (P.q i)))
      (Finset.univ.sup fun j : Fin m => halfDeg (P.g j))

/-- Feasibility in (D). Paper index 1 is Lean index 0. -/
def SRFO.DFeasible (P : SRFO n m N) [NeZero N]
    (c : ℝ) (h : Fin N → MvPolynomial (Fin n) ℝ) : Prop :=
  (∀ x ∈ P.K,
    0 ≤ eval x (P.p 0 + ((∑ i ∈ Finset.univ.erase (0 : Fin N), h i) - C c) * P.q 0)) ∧
  (∀ i : Fin N, i ≠ 0 → ∀ x ∈ P.K,
    0 ≤ eval x (P.p i - h i * P.q i))

/-- The value of the polynomial dual (D), including infeasibility. -/
noncomputable def SRFO.valD (P : SRFO n m N) [NeZero N] : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | ∃ h, P.DFeasible c h})

/-- Feasibility in the dense order-k dual relaxation (Dk). -/
def SRFO.DKFeasible (P : SRFO n m N) [NeZero N] (k : ℕ)
    (c : ℝ) (h : Fin N → MvPolynomial (Fin n) ℝ) : Prop :=
  P.p 0 + ((∑ i ∈ Finset.univ.erase (0 : Fin N), h i) - C c) * P.q 0 ∈ truncQM P.g k ∧
  (∀ i : Fin N, i ≠ 0 →
    P.p i - h i * P.q i ∈ truncQM P.g k ∧
    (h i).totalDegree ≤ 2 * k - max (P.q 0).totalDegree (P.q i).totalDegree)

/-- The value ρ_k of (Dk). -/
noncomputable def SRFO.rhoK (P : SRFO n m N) [NeZero N] (k : ℕ) : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | ∃ h, P.DKFeasible k c h})

end SignSymRat.Hierarchy


