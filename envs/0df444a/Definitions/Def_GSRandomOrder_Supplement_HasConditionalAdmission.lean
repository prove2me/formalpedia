-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_HasConditionalAdmission
-- name    : GSRandomOrder_Supplement_HasConditionalAdmission
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:09:23.716894+00:00
-- url     : https://prove2.me/theorems/9f40ba88-5478-4812-9862-9b9796877ccb
-- title:
--   Conditional admission (Definition 4.4)
-- statement:
--   Let $v$ be a valuation, $P$ a proposal map and $s$ a cutoff, and put $a_k=s/(k-1)$. An admission module for $v$ and $P$ has **conditional admission** if
--
--   1. for every $k>s$, every $k$-set $S$ and every $g\in P(S)$,
--   $$
--   \mathbb P\bigl[g_k\text{ is accepted}\bigm| S_k=S,\ g_k=g\bigr]\ \ge\ a_k ;\qquad(15)
--   $$
--   2. there are numbers $c_g(S)\ge0$, fixed in advance for $S\subseteq N$ and $g\in P(S)$, with $\sum_{g\in P(S)}c_g(S)=v(P(S))$, such that $A\in\operatorname{dom}v$ almost surely and
--   $$
--   \mathbb E\,v(A)\ \ge\ \mathbb E\sum_{k=s+1}^n c_{g_k}(S_k)\,\mathbf 1\{g_k\text{ is accepted}\}.\qquad(16)
--   $$
--
--   Probabilities are over the uniformly random arrival order and the module's coins. The credit $c_g(S)$ is the share of $v(P(S))$ promised for accepting $g$ when the arrived set is $S$.
--
--   **Formalization Note** The joint law of order and decisions gives mass $\frac1{n!}\cdot$(decision probability) to each pair. (15) is written multiplied out, $\mathbb P[\text{accepted},S_k=S,g_k=g]\ge a_k\,\mathbb P[S_k=S,g_k=g]$, which is the conditional form since the event has positive probability. "Almost surely" is "on every outcome of positive probability". The credit sum is an equality in `WithBot ℝ`; $v(A)$ is read as a real with `unbotD 0` in the expectation.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Definition 4.4, pp.15–16, eqs. (15) and (16)

import Mathlib
import Definitions.Def_GSRandomOrder_Supplement_AdmissionModule

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Conditional admission** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, Definition 4.4, pp.15–16). An
admission module for `v` and `P` with cutoff `s` has conditional admission if
(i) for every `k > s`, every `k`-set `S` and every `g ∈ P(S)`,
    `P[g_k is accepted | S_k = S, g_k = g] ≥ a_k = s/(k − 1)`   (15);
(ii) there are numbers `c_g(S) ≥ 0`, fixed in advance for `S ⊆ N` and `g ∈ P(S)`, with
    `Σ_{g ∈ P(S)} c_g(S) = v(P(S))`, such that `A ∈ dom v` almost surely and
    `E v(A) ≥ E Σ_{k=s+1}^n c_{g_k}(S_k) 1{g_k is accepted}`   (16).
Probabilities are over the uniformly random arrival order and the module's coins.

**Formalization Note.** The joint law of (order `σ`, decisions `d`) gives mass
`(1/n!) · M.weight σ d` to each pair. Step `k` is arrival position `j = k − 1`, so `k > s` is
`s ≤ j`, `a_k = s/j`, `S_k = prefixSet σ (j+1)` and `g_k = σ j`. (15) is stated multiplied out,
`P[accepted ∧ S_k = S ∧ g_k = g] ≥ a_k · P[S_k = S ∧ g_k = g]`; the conditioning event has
positive probability, so this is the conditional form. "Almost surely" on this finite space is
"on every pair of positive mass". `v(A)` and the credits are compared in `WithBot ℝ`, and `v(A)` is
read as a real with `unbotD 0` only in the expectation, where `A ∈ dom v` holds on every pair of
positive mass. Credits are a function on all pairs `(S, g)`; only the values at `g ∈ P(S)` enter. -/
def HasConditionalAdmission {n : ℕ} (v : Finset (Fin n) → WithBot ℝ)
    {P : Finset (Fin n) → Finset (Fin n)} {s : ℕ} (M : AdmissionModule n P s) : Prop :=
  (∀ j : Fin n, s ≤ j.val → ∀ S : Finset (Fin n), S.card = j.val + 1 → ∀ g ∈ P S,
      (s : ℝ) / j.val * ∑ σ : Fin n ≃ Fin n, ∑ d : Fin n → Bool,
          (1 / (n.factorial : ℝ)) * M.weight σ d *
            (if prefixSet σ (j.val + 1) = S ∧ σ j = g then 1 else 0) ≤
        ∑ σ : Fin n ≃ Fin n, ∑ d : Fin n → Bool,
          (1 / (n.factorial : ℝ)) * M.weight σ d *
            (if d j = true ∧ prefixSet σ (j.val + 1) = S ∧ σ j = g then 1 else 0)) ∧
  ∃ c : Finset (Fin n) → Fin n → ℝ,
    (∀ S, ∀ g ∈ P S, 0 ≤ c S g) ∧
    (∀ S, (((∑ g ∈ P S, c S g : ℝ)) : WithBot ℝ) = v (P S)) ∧
    (∀ σ d, M.weight σ d ≠ 0 → v (acceptedSet σ d) ≠ ⊥) ∧
    ∑ σ : Fin n ≃ Fin n, ∑ d : Fin n → Bool,
        (1 / (n.factorial : ℝ)) * M.weight σ d *
          ∑ j : Fin n, (if s ≤ j.val ∧ d j = true then c (prefixSet σ (j.val + 1)) (σ j) else 0) ≤
      ∑ σ : Fin n ≃ Fin n, ∑ d : Fin n → Bool,
        (1 / (n.factorial : ℝ)) * M.weight σ d * (v (acceptedSet σ d)).unbotD 0

end GSRandomOrder.Supplement


