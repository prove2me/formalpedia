-- Prove2me | Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
-- name    : InteractiveConsistency_OralAlgorithm_Scenario
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:21.997799+00:00
-- url     : https://prove2.me/theorems/b20bea1e-dbc0-4fbf-94f7-935dafd02903
-- title:
--   Sections 1, 3, 4 (pp. 229, 230, 232) — strings over P, consistency of a k-level scenario with N, and assuring interactive consistency for m faults
-- statement:
--   This file fixes the vocabulary of Pease, Shostak and Lamport for the oral-message setting.
--
--   Let $P$ be a finite set of $n = |P|$ processors and $V$ a set of values. A **string over** a set $S$ is a finite sequence $p_1p_2\cdots p_r$ of elements of $S$ (repetitions allowed). A **$k$-level scenario** is a map $\sigma$ from the nonempty strings over $P$ of length at most $k+1$ to $V$; for $r \ge 2$, $\sigma(p_1p_2\cdots p_r)$ is the value $p_2$ tells $p_1$ that $p_3$ told $p_2$ that … $p_r$ told $p_{r-1}$ is $p_r$'s private value, and $\sigma(p)$ is $p$'s private value $V_p$.
--
--   1. **Consistency with $N$ at level $k$.** For a set $N \subseteq P$ of nonfaulty processors, $\sigma$ is consistent with $N$ if nonfaulty processors relay truthfully:
--   $$\sigma(pqw) = \sigma(qw)\qquad\text{for every } q\in N,\ p\in P \text{ and string } w \text{ over } P \text{ with } |pqw| \le k+1 .$$
--   2. **View.** Processor $p$ receives only the restriction $\sigma_p$ of $\sigma$ to strings beginning with $p$.
--   3. **Assuring interactive consistency for $m$ faults.** A family $\{F_p \mid p\in P\}$, where $F_p$ maps a $p$-view and a processor to a value or NIL, assures interactive consistency for $m$ faults on $(m+1)$-level scenarios if for every $N\subseteq P$ with $|N|\ge n-m$ and every $(m+1)$-level scenario $\sigma$ consistent with $N$:
--      (i) $F_p(\sigma_p, q) = \sigma(q)$ for all $p, q\in N$;
--      (ii) $F_p(\sigma_p, r) = F_{p'}(\sigma_{p'}, r)$ for all $p, p'\in N$ and $r\in P$.
--
--   Clause (i) says that every nonfaulty processor computes the private value of every nonfaulty processor; clause (ii) says that all nonfaulty processors compute the same interactive-consistency vector. These are conditions (1)–(2) of Section 1, in the formal form of Section 4, restricted to the $m+1$ rounds of information exchange that Section 3 uses.
--
--   **Formalization Note.** Strings are Lean lists read left to right ($p_1$, the receiver, is the head; the originator $p_r$ is the last entry). A scenario is a total function `List α → V`; only its values on nonempty strings over $P$ of length $\le k+1$ are constrained, and the condition $|pqw|\le k+1$ is written `w.length + 2 ≤ k + 1`. The view of $p$ is `fun w => σ (p :: w)`, so $F_p$ never sees strings that do not begin with $p$. The computed values live in `Option V`, with `none` standing for NIL; clause (i) reads `F p σ_p q = some (σ [q])`. $|N| \ge n - m$ is written `P.card ≤ N.card + m`.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 229, Section 1, conditions (1)–(2); p. 230, Section 3 (k-level scenario, σ(pqw) = σ(qw), σ_p); p. 232, Section 4, clauses (i)–(ii)

import Mathlib

namespace InteractiveConsistency.OralAlgorithm

/-- `w` is a string over `S`: every letter of `w` lies in `S` (repetitions allowed). -/
def IsStringOver {α : Type*} (S : Finset α) (w : List α) : Prop :=
  ∀ x ∈ w, x ∈ S

/-- Consistency of a `k`-level scenario with the set `N` of nonfaulty processors (p. 230):
`σ (p :: q :: w) = σ (q :: w)` for every nonfaulty `q ∈ N`, every processor `p ∈ P` and every
string `w` over `P`, as long as the string `p q w` lies in the domain of a `k`-level scenario,
i.e. has length `≤ k + 1`.  The string `p₁ p₂ … p_r` is the list `[p₁, …, p_r]`. -/
def ConsistentUpTo {α V : Type*} (P N : Finset α) (k : ℕ) (σ : List α → V) : Prop :=
  ∀ q ∈ N, ∀ p ∈ P, ∀ w : List α, IsStringOver P w → w.length + 2 ≤ k + 1 →
    σ (p :: q :: w) = σ (q :: w)

/-- A family `F p` (processor `p`'s decision rule, applied to `p`'s view `fun w => σ (p :: w)`
and a processor `r`, returning a value or `none` = NIL) assures interactive consistency for `m`
faults on `(m + 1)`-level scenarios (p. 229 (1)–(2), p. 232 (i)–(ii)): for every set `N ⊆ P`
with `|N| ≥ |P| - m` and every `σ` consistent with `N` at level `m + 1`,
(i) every nonfaulty `p` computes `σ [q]` for every nonfaulty `q`, and
(ii) any two nonfaulty processors compute the same value for every `r ∈ P`. -/
def AssuresICLevel {α V : Type*} (P : Finset α) (m : ℕ)
    (F : α → (List α → V) → α → Option V) : Prop :=
  ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m → ∀ σ : List α → V,
    ConsistentUpTo P N (m + 1) σ →
      (∀ p ∈ N, ∀ q ∈ N, F p (fun w => σ (p :: w)) q = some (σ [q])) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        F p (fun w => σ (p :: w)) r = F p' (fun w => σ (p' :: w)) r)

end InteractiveConsistency.OralAlgorithm


