-- Prove2me | Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt
-- name    : BudgetAgg_NashChar_Supplement_TwoAlt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:01:55.13415+00:00
-- url     : https://prove2.me/theorems/228f0000-f688-4cc8-a3ac-bcbc0a857003
-- title:
--   §7 — two alternatives: single-peaked domains, strategyproofness, anonymity, proportionality, generalized median and uniform phantom rules
-- statement:
--   With two alternatives $M=\{a,b\}$ (§7, p. 17), a distribution is identified with the share $x\in[0,1]$ of $b$, and agent $i$'s peak with $p_i\in[0,1]$. A profile is $P=(p_1,\dots,p_n)\in[0,1]^n$ and a (tops-only) mechanism is $f:[0,1]^n\to[0,1]$.
--
--   1. A utility $u$ is **single-peaked at $p$** if it satisfies the star-shapedness condition (1) on $[0,1]$: for every $q\in[0,1]$, $q\neq p$, and $\lambda\in(0,1)$, $u(p)>u(\lambda p+(1-\lambda)q)>u(q)$.
--   2. A **domain** $U\subseteq U_{SP}$ is a set of utilities each single-peaked at some $p\in[0,1]$, containing **at least one** utility single-peaked at each $p\in[0,1]$.
--   3. $f$ is **strategyproof on $U$** if for every agent $i$, profile $P$, report $p'$ and every $u\in U$ single-peaked at $p_i$: $u(f(P))\ge u(f(p',P_{-i}))$.
--   4. $f$ is **anonymous** if $f(P\circ\sigma)=f(P)$ for every permutation $\sigma$ of the agents.
--   5. $P$ is **single-minded** if every $p_i\in\{0,1\}$; $f$ is **proportional** if $f(P)=\frac1n\sum_i p_i$ on single-minded profiles.
--   6. $\mathrm{med}(x_1,\dots,x_{2k+1})$ is the $(k+1)$-th smallest value. The **generalized median rule** with phantoms $\alpha_0,\dots,\alpha_n$ is $P\mapsto\mathrm{med}(p_1,\dots,p_n,\alpha_0,\dots,\alpha_n)$, and the **uniform phantom rule** is the case $\alpha_k=k/n$.
--
--   These objects carry the characterizations of §7 (Lemmas 12, 13, Theorems 5, 6).
--
--   **Formalization Note** Peaks and outcomes are elements of Mathlib's `unitInterval`; utilities are functions `ℝ → ℝ` whose values are used only on $[0,1]$. `med` sorts the multiset of values ascending and returns index $\lfloor \text{card}/2\rfloor$ (0-based), which is the $(k+1)$-th smallest for $2k+1$ values. The generalized median takes the $n$ peaks and $n+1$ phantoms as a family indexed by `Fin n ⊕ Fin (n+1)`.
--   The helper `med` also accepts other finite cardinalities: it returns the upper middle entry for a nonempty even family and zero for the empty family. Every median in the source results has the nonempty odd length $2n+1$. The raw `uniformPhantom` formula at $n=0$ evaluates to zero; every source theorem using it assumes $n\ge1$.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, pp. 6, 8–9, 17–18, condition (1), Definitions 5, 8, 9, 10 and §7

import Mathlib

namespace BudgetAgg.NashChar.Supplement

open Finset

/-- With two alternatives `a, b`, a peak or outcome is the share of `b`, a point of
`[0, 1]` (§7, p. 17). A profile lists the peaks of the `n` agents. -/
abbrev Profile2 (n : ℕ) := Fin n → unitInterval

/-- A tops-only mechanism for two alternatives (§7, p. 17). -/
abbrev Mechanism2 (n : ℕ) := Profile2 n → unitInterval

/-- `u` is single-peaked at `p ∈ [0, 1]`: the star-shapedness condition (1) of p. 6
on `[0, 1]`, i.e. for every `q ≠ p` in `[0, 1]` and `λ ∈ (0, 1)`,
`u(p) > u(λ p + (1 - λ) q) > u(q)`. -/
def IsSinglePeakedAt (u : ℝ → ℝ) (p : unitInterval) : Prop :=
  ∀ q : unitInterval, (q : ℝ) ≠ p → ∀ t : ℝ, 0 < t → t < 1 →
    u (t * p + (1 - t) * q) < u p ∧ u q < u (t * p + (1 - t) * q)

/-- An admissible domain `U ⊆ U_SP` (§7, p. 17): every utility in `U` is
single-peaked at some peak in `[0, 1]`, and every peak in `[0, 1]` is the peak of at
least one utility in `U`. -/
def IsSPDomain (U : Set (ℝ → ℝ)) : Prop :=
  (∀ u ∈ U, ∃ p : unitInterval, IsSinglePeakedAt u p) ∧
  (∀ p : unitInterval, ∃ u ∈ U, IsSinglePeakedAt u p)

/-- Strategyproofness on the domain `U` (Definition 8 with `|N'| = 1`): for every
agent `i`, profile `P`, misreport `p'` and every utility `u ∈ U` single-peaked at the
true peak `P i`, `u(f(P)) ≥ u(f(P'))`, where `P'` replaces `P i` by `p'`. -/
def IsSP2 {n : ℕ} (U : Set (ℝ → ℝ)) (f : Mechanism2 n) : Prop :=
  ∀ (i : Fin n) (P : Profile2 n) (p' : unitInterval) (u : ℝ → ℝ),
    u ∈ U → IsSinglePeakedAt u (P i) →
      u (f (Function.update P i p')) ≤ u (f P)

/-- Anonymity (Definition 5, p. 8): permuting the agents does not change the outcome. -/
def IsAnonymous2 {n : ℕ} (f : Mechanism2 n) : Prop :=
  ∀ (P : Profile2 n) (σ : Equiv.Perm (Fin n)), f (P ∘ σ) = f P

/-- Single-minded two-alternative profile (Definition 9): every peak is `0` or `1`. -/
def IsSingleMinded2 {n : ℕ} (P : Profile2 n) : Prop :=
  ∀ i, (P i : ℝ) = 0 ∨ (P i : ℝ) = 1

/-- Proportionality for two alternatives (Definition 10): on single-minded profiles
the share of `b` is `∑_i p_i / n` (the share of `a` is then `∑_i (1 - p_i)/n`). -/
def IsProportional2 {n : ℕ} (f : Mechanism2 n) : Prop :=
  ∀ P : Profile2 n, IsSingleMinded2 P → (f P : ℝ) = (∑ i, (P i : ℝ)) / (n : ℝ)

/-- The median of a finite family of reals with an odd number `2k + 1` of entries:
the `(k+1)`-th smallest entry, i.e. index `⌊card / 2⌋` of the ascending sort. -/
noncomputable def med {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ((Finset.univ.val.map x).sort (· ≤ ·)).getD (Fintype.card ι / 2) 0

/-- The generalized median rule `med(p_1, …, p_n, α_0, …, α_n)` (Theorem 5, p. 18):
the median of the `n` peaks and the `n + 1` phantoms `α`. -/
noncomputable def genMedian {n : ℕ} (α : Fin (n + 1) → ℝ) (P : Profile2 n) : ℝ :=
  med (Sum.elim (fun i : Fin n => (P i : ℝ)) α)

/-- The uniform phantom rule (p. 18): the generalized median rule with phantoms
`α_k = k / n`, `k = 0, …, n`. -/
noncomputable def uniformPhantom {n : ℕ} (P : Profile2 n) : ℝ :=
  genMedian (fun k : Fin (n + 1) => (k : ℝ) / (n : ℝ)) P

end BudgetAgg.NashChar.Supplement


