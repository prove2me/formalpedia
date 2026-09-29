-- Prove2me | Definitions.Def_HeldWolfeCrowder_Assignment_Setting
-- name    : HeldWolfeCrowder_Assignment_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:51:51.476559+00:00
-- url     : https://prove2.me/theorems/5b272606-af7a-4ded-89b0-4f6de7f00cbb
-- title:
--   The assignment problem (3.1), its dual function w of Eq. (3.3), the assignment vectors of Eq. (3.4) and the set Π of Eq. (3.6)
-- statement:
--   This file fixes the objects of Section 3 of Held, Wolfe & Crowder's paper, the assignment problem and its Lagrangean dual.
--
--   There are $n$ men and $n$ jobs, and $A=(a_{ir})$ is a real $n\times n$ matrix: $a_{ir}$ is the cost for which man $i$ does job $r$.
--
--   1. **Assignments and their cost.** An *assignment* is a function $A:\{1,\dots,n\}\to\{1,\dots,n\}$, where $A(r)$ is the man assigned to job $r$; two jobs may go to the same man. Its cost is
--   $$c_A=\sum_{r=1}^n a_{A(r)\,r}.$$
--   2. **The vector of an assignment (3.4).** For an assignment $A$ and a man $i$,
--   $$(v_A)_i = 1-\#\{r : A(r)=i\}.$$
--   3. **Optimal assignments (3.1).** A *one-to-one* assignment is a permutation $\sigma$ of $\{1,\dots,n\}$ ($\sigma(r)$ is the man doing job $r$). It is *optimal* if $c_\sigma\le c_\tau$ for every permutation $\tau$.
--   4. **The dual function (3.3).** For $\pi\in\mathbb R^n$ (a price on each man),
--   $$w(\pi)=\sum_{i=1}^n \pi_i+\sum_{r=1}^n \min_{s}\,[a_{sr}-\pi_s],$$
--   where, for each job $r$, the minimum is over the men $s$. It is the objective of the dual linear program (3.2), $\max\{\sum_i\pi_i+\sum_r\rho_r : \pi_i+\rho_r\le a_{ir}\}$, after the best choice of $\rho$.
--   5. **The optimal set.** The optimal set of (3.3) is $\{\pi : w(\pi')\le w(\pi) \text{ for all } \pi'\}$, the set of maximizers of $w$.
--   6. **The set $\Pi$ of (3.6).** For a permutation $\sigma$, $\Pi_\sigma$ is the set of $\pi$ with
--   $$a_{ir}-\pi_i > a_{\sigma(r)\,r}-\pi_{\sigma(r)}\qquad\text{for every job } r \text{ and every man } i\ne\sigma(r).$$
--
--   These objects are shared by every statement of the mission: the representation of $w$ as a minimum of affine functions, the equality between $\max w$ and the optimal assignment cost, and the dimension of the optimal set.
--
--   **Formalization Note** Men and jobs are both indexed by `Fin n`; the cost matrix is `a : Matrix (Fin n) (Fin n) ℝ` with `a i r` the cost of man `i` on job `r`, and prices are `π : Fin n → ℝ` (no inner product or norm is needed). An assignment is any `Fin n → Fin n`, a one-to-one assignment is an `Equiv.Perm (Fin n)`. The inner minimum of (3.3) is `Finset.univ.inf'` over the men, which is well defined for every `n` because the job `r` itself witnesses that the index set is nonempty. The page prints the condition of (3.6) as "for all r, i ≠ r"; the set is defined with $i\ne\sigma(r)$, which is what the page's argument uses (with $i\ne r$ the set would force a strict inequality of a quantity with itself when $\sigma(r)\ne r$).
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 69, Eqs. (3.1)–(3.4); p. 70, Eq. (3.6)

import Mathlib

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), §3, p. 69. The cost `c = Σ_r a_{A(r) r}` of an *assignment*
`A : Fin n → Fin n`, where `A r` is the man assigned to job `r` and `a i r` is the cost for which
man `i` does job `r`. Two jobs may be assigned to the same man. -/
def assignCost {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n) : ℝ :=
  ∑ r, a (A r) r

/-- The vector `v` of Eq. (3.4), p. 69: `(v_A)_i = 1 − #{r : A(r) = i}`. -/
def assignVec {n : ℕ} (A : Fin n → Fin n) (i : Fin n) : ℝ :=
  1 - ((Finset.univ.filter fun r => A r = i).card : ℝ)

/-- A one-to-one assignment `σ` (a permutation; `σ r` is the man doing job `r`) is *optimal* for
the assignment problem (3.1), p. 69, if its total cost is minimal among all one-to-one
assignments. -/
def IsOptimalAssignment {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), assignCost a σ ≤ assignCost a τ

/-- The dual function (3.3), p. 69: `w(π) = Σ_i π_i + Σ_r min_s [a_{sr} − π_s]`, the minimum
for job `r` being over the man index `s`. (The index set of the minimum is nonempty because it
contains `r`, so the definition is valid for every `n`.) -/
def w {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : ℝ :=
  ∑ i, π i + ∑ r, Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun s => a s r - π s)

/-- The optimal set of the problem `max w` for (3.3): all `π` at which `w` attains its
maximum. -/
def optSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {π | ∀ π' : Fin n → ℝ, w a π' ≤ w a π}

/-- The set `Π` of Eq. (3.6), p. 70, for a one-to-one assignment `σ`: all `π` with
`a_{ir} − π_i > a_{σ(r) r} − π_{σ(r)}` for every job `r` and every man `i ≠ σ(r)`. -/
def PiSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {π | ∀ r i : Fin n, i ≠ σ r → a (σ r) r - π (σ r) < a i r - π i}

end HeldWolfeCrowder.Assignment


