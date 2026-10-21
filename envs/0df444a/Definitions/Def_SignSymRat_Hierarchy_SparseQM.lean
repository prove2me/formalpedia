-- Prove2me | Definitions.Def_SignSymRat_Hierarchy_SparseQM
-- name    : SignSymRat_Hierarchy_SparseQM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:29.773915+00:00
-- url     : https://prove2.me/theorems/d5b21128-4bf1-4595-ae83-abe80ae815e4
-- title:
--   Sparse quadratic module and (SDk)
-- statement:
--   For a finite monomial support $A$, the degree-$k$ binary pattern has entry $1$ at $(\alpha,\beta)$ exactly when $\alpha+\beta\in\bar A$. A sparse SOS multiplier is $[x]_s^T G[x]_s$ with $G$ positive semidefinite and zero outside that pattern. The associated quadratic module is
--
--   $$Q_k(g,A)=\left\{\sigma_0+\sum_{j=1}^{m}\sigma_jg_j:\sigma_j=[x]_{k-d_j}^T G_j[x]_{k-d_j},\ G_j\succeq0\text{ in the }\bar A\text{ pattern}\right\},$$
--
--   where $d_0=0$ and $d_j=\lceil\deg(g_j)/2\rceil$. Program (SDk) uses $Q_k(g,A_1)$ for its first certificate and $Q_k(g,A_i)$ for the remaining certificates, while requiring $h_i\in\mathbb R[\bar A_i]$ and $\deg h_i\le2k-\max\{\deg q_1,\deg q_i\}$. Its value is $\rho_k^s$.
--
--   **Formalization Note** Paper index $1$ is Lean index `0`. Gram matrices are indexed by all monomials of degree at most their indicated order. Values are in the extended reals; an infeasible (SDk) has value $-\infty$.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 12, binary matrix B^A_k, Q_k(g,A), (SDk)

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SignSym
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

open MvPolynomial
open SemialgebraicSDP.Psatz

namespace SignSymRat.Hierarchy

variable {n m N : ℕ}

/-- G ∈ S⁺(B^A_s): PSD with zero entries whenever α + β ∉ A-bar. -/
def InPattern {n s : ℕ} (A : Finset (Fin n →₀ ℕ))
    (G : Matrix (Mon n s) (Mon n s) ℝ) : Prop :=
  G.PosSemidef ∧
  ∀ α β : Mon n s, α.toFinsupp + β.toFinsupp ∉ symClosure A → G α β = 0

/-- The sign-symmetry-adapted sparse quadratic module Q_k(g,A). -/
def sparseQM (g : Fin m → MvPolynomial (Fin n) ℝ)
    (A : Finset (Fin n →₀ ℕ)) (k : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {f | ∃ (G₀ : Matrix (Mon n k) (Mon n k) ℝ)
          (G : ∀ j : Fin m,
            Matrix (Mon n (k - halfDeg (g j))) (Mon n (k - halfDeg (g j))) ℝ),
    InPattern A G₀ ∧ (∀ j, InPattern A (G j)) ∧
    f = gramPoly G₀ + ∑ j, gramPoly (G j) * g j}

/-- Feasibility in the sign-symmetric order-k dual relaxation (SDk). -/
def SRFO.SKFeasible (P : SRFO n m N) [NeZero N] (k : ℕ)
    (c : ℝ) (h : Fin N → MvPolynomial (Fin n) ℝ) : Prop :=
  P.p 0 + ((∑ i ∈ Finset.univ.erase (0 : Fin N), h i) - C c) * P.q 0 ∈
    sparseQM P.g (P.Aset 0) k ∧
  (∀ i : Fin N, i ≠ 0 →
    P.p i - h i * P.q i ∈ sparseQM P.g (P.Aset i) k ∧
    SupportedIn (symClosure (P.Aset i)) (h i) ∧
    (h i).totalDegree ≤ 2 * k - max (P.q 0).totalDegree (P.q i).totalDegree)

/-- The value ρˢ_k of (SDk), including infeasibility. -/
noncomputable def SRFO.rhoSK (P : SRFO n m N) [NeZero N] (k : ℕ) : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | ∃ h, P.SKFeasible k c h})

end SignSymRat.Hierarchy


