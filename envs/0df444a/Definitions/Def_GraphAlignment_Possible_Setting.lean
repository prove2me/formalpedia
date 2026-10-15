-- Prove2me | Definitions.Def_GraphAlignment_Possible_Setting
-- name    : GraphAlignment_Possible_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:09.244981+00:00
-- url     : https://prove2.me/theorems/261ae50b-356f-417b-9d70-effbba47eb00
-- title:
--   §2.2, §2.4, Definition 2 — the correlated Erdős–Rényi model (n, q, s) with planted permutation π*, the overlap β, the edge law P (3), good permutations and conditions (6)
-- statement:
--   The **correlated Erdős–Rényi model** $(n, q, s)$ with a planted permutation, and the objects of the possibility result.
--
--   Let $n \ge 1$ and let $q, s \in [0,1]$ with $q < s$. A parent graph $G \sim G(n, q/s)$ on the vertex set $\{1,\dots,n\}$ is copied twice, and each copy keeps every edge independently with probability $s$. The two resulting graphs $G_A$ and $G_{B'}$ have adjacency matrices $A$ and $B'$ (symmetric, zero diagonal). For each unordered pair $\{i,j\}$ of distinct vertices, the pair $(A_{ij}, B'_{ij}) \in \{0,1\}^2$ has the law $P$ of display (3),
--   $$p_{00} = 1 - 2q + qs,\qquad p_{01} = p_{10} = q(1-s),\qquad p_{11} = qs,$$
--   and the $\binom n2$ pairs are independent. A **configuration** $\omega$ assigns such a pair to every unordered pair of distinct vertices, and has probability $\prod_{\{i,j\}} P(\omega_{\{i,j\}})$; the probability $\mathbb P(E)$ of an event $E$ is the total probability of the configurations in $E$.
--
--   Given a permutation $\pi^*$ of $\{1,\dots,n\}$, the observed graph $G_B$ is $G_{B'}$ relabelled by $\pi^*$:
--   $$B_{\pi^*(i)\pi^*(j)} = B'_{ij}.$$
--   An algorithm observes the pair $(A, B)$ only.
--
--   1. **Overlap** (p. 6). For permutations $\pi, \pi^*$, $\beta(\pi,\pi^*) = \frac1n \sum_{i=1}^n \mathbf 1\{\pi(i) = \pi^*(i)\}$.
--   2. **Good permutation** (Definition 2, p. 15). For $0 < \alpha < 1$, a permutation $\pi$ is good for the observed $(A,B)$ if
--   $$\sum_{i=1}^n \mathbf 1\Big\{\sum_{j \ne i} A_{ij} B_{\pi(i)\pi(j)} \ge \frac{nqs}{2}\Big\} \ \ge\ n\cdot\frac{1+\alpha}{2}.$$
--   3. **Conditions (6)** (Theorem 2.3, p. 8). For exponents $\beta, \gamma > 0$ and a given $n$:
--   $$nqs \ge \max\Big\{20,\ 84\log\frac{2}{1-\alpha},\ \frac{16}{\min(\gamma,\beta)(1-\alpha)}\Big\},\quad s > \frac{8}{1-\alpha}\,q,\quad \frac{2q(1-s^2)}{s} \le n^{-\beta},\quad qs \le n^{-2\gamma}.$$
--
--   These definitions are the common vocabulary of Proposition 4.2, Proposition 4.4 and Theorem 2.3.
--
--   **Formalization Note** Vertices are `Fin n`; a configuration is a function from the non-diagonal elements of `Sym2 (Fin n)` to `Bool × Bool` (first coordinate $A_{ij}$, second $B'_{ij}$), and `prob` is the finite sum of `cfgProb` over configurations, so it is a genuine probability whenever $0 \le q < s \le 1$. $B$ is computed as $B_{kl} = B'_{\pi^{*-1}(k)\,\pi^{*-1}(l)}$. The overlap is called `overlap` (not $\beta$), and the exponents of (6) are `βe`, `γe`. Both thresholds of Definition 2 are real numbers, not floored. The logarithm is natural. The overlap is $0$ when $n = 0$, which is irrelevant for the asymptotic statements.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, pp. 5–8, 15, §2.2, (3), Theorem 2.3 (6), Definition 2

import Mathlib

namespace GraphAlignment.Possible

/-- The joint law `P` of one edge pair `(A_ij, B'_ij)` in the correlated Erdős–Rényi model
(n, q, s), display (3) on p. 7: `p00 = 1 - 2q + qs`, `p01 = p10 = q(1 - s)`, `p11 = qs`.
The first coordinate is `A_ij`, the second `B'_ij` (`true` = edge present). -/
def pLaw (q s : ℝ) : Bool × Bool → ℝ
  | (false, false) => 1 - 2 * q + q * s
  | (false, true) => q * (1 - s)
  | (true, false) => q * (1 - s)
  | (true, true) => q * s

/-- A configuration of the model on `n` vertices: for every unordered pair `{i, j}` of distinct
vertices (a non-diagonal element of `Sym2 (Fin n)`), the pair `(A_ij, B'_ij)` of edge
indicators of `G_A` and `G_B'`. -/
abbrev Config (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool × Bool

/-- The probability of a configuration: the pairs are independent, each with law `pLaw q s`. -/
def cfgProb {n : ℕ} (q s : ℝ) (ω : Config n) : ℝ :=
  ∏ e, pLaw q s (ω e)

/-- The adjacency matrix `A` of `G_A` read off a configuration (no self-loops, symmetric). -/
def A {n : ℕ} (ω : Config n) (i j : Fin n) : Bool :=
  if h : i = j then false else (ω ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff] using h⟩).1

/-- The adjacency matrix `B'` of `G_B'` read off a configuration (no self-loops, symmetric). -/
def B' {n : ℕ} (ω : Config n) (i j : Fin n) : Bool :=
  if h : i = j then false else (ω ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff] using h⟩).2

/-- The observed adjacency matrix `B` of `G_B`, obtained by relabelling `G_B'` with the planted
permutation `π*`: `B (π* i) (π* j) = B' i j` (p. 5), i.e. `B k l = B' (π*⁻¹ k) (π*⁻¹ l)`. -/
def B {n : ℕ} (πstar : Equiv.Perm (Fin n)) (ω : Config n) (k l : Fin n) : Bool :=
  B' ω (πstar.symm k) (πstar.symm l)

open Classical in
/-- The probability, in the correlated Erdős–Rényi model (n, q, s), of an event `E` on
configurations: the total weight `cfgProb q s` of the configurations where `E` holds. -/
noncomputable def prob {n : ℕ} (q s : ℝ) (E : Config n → Prop) : ℝ :=
  ∑ ω : Config n, cfgProb q s ω * (if E ω then 1 else 0)

/-- The overlap `β(π, π*) = (1/n) Σ_i 1{π(i) = π*(i)}` of two permutations (p. 6). -/
noncomputable def overlap {n : ℕ} (π πstar : Equiv.Perm (Fin n)) : ℝ :=
  (1 / (n : ℝ)) * ((Finset.univ.filter fun i => π i = πstar i).card : ℝ)

/-- The observation available to an algorithm: the pair `(A, B)` of adjacency matrices. -/
abbrev Obs (n : ℕ) : Type := (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool)

/-- Definition 2 (p. 15): for `0 < α < 1`, a permutation `π` is *good* for the observed pair
`(A, B)` if at least `n (1 + α) / 2` vertices `i` satisfy `Σ_{j ≠ i} A_ij B_{π(i)π(j)} ≥ nqs/2`.
Both thresholds are real numbers. -/
def good (n : ℕ) (q s α : ℝ) (Aobs Bobs : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    Prop :=
  (n : ℝ) * (1 + α) / 2 ≤
    ((Finset.univ.filter fun i : Fin n =>
        (n : ℝ) * q * s / 2 ≤
          ∑ j ∈ Finset.univ.erase i, (if Aobs i j && Bobs (π i) (π j) then (1 : ℝ) else 0)).card : ℝ)

/-- The four conditions (6) of Theorem 2.3 (p. 8) at a given `n`, with exponents `βe, γe`:
`nqs ≥ max{20, 84 log(2/(1-α)), 16/(min(γ,β)(1-α))}`, `s > 8q/(1-α)`,
`2q(1-s²)/s ≤ n^{-β}` and `qs ≤ n^{-2γ}` (natural logarithm). -/
def Cond6 (α βe γe : ℝ) (n : ℕ) (q s : ℝ) : Prop :=
  max (max 20 (84 * Real.log (2 / (1 - α)))) (16 / (min γe βe * (1 - α))) ≤ (n : ℝ) * q * s ∧
  8 / (1 - α) * q < s ∧
  2 * q * (1 - s ^ 2) / s ≤ (n : ℝ) ^ (-βe) ∧
  q * s ≤ (n : ℝ) ^ (-2 * γe)

end GraphAlignment.Possible


