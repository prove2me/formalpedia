-- Prove2me | Definitions.Def_SubsampleSubmod_SampleGreedy_Model
-- name    : SubsampleSubmod_SampleGreedy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:24.703045+00:00
-- url     : https://prove2.me/theorems/4e4e2948-db83-45dc-af64-dd993042eacb
-- title:
--   §3, §4.1, pp. 5–6, 9–10 — marginal gain, linear set functions, p-extendible independence systems, the greedy run with order tie-break, SampleGreedy and its expected value
-- statement:
--   This file fixes the model of Harshaw, Kazemi, Feldman and Karbasi for submodular maximization over $p$-extendible systems, and the algorithm SampleGreedy.
--
--   Let $\mathcal N$ be a finite ground set of size $n$, carrying a fixed linear order $u_1 < u_2 < \dots < u_n$. A set function is a map $f : 2^{\mathcal N} \to \mathbb R$.
--
--   1. **Marginal gain.** $f(u \mid S) = f(S \cup \{u\}) - f(S)$.
--   2. **Linear set function.** $f$ is linear if the diminishing-returns inequality holds with equality: $f(A \cup \{e\}) - f(A) = f(B \cup \{e\}) - f(B)$ for all $A \subseteq B \subseteq \mathcal N$ and $e \notin B$. The value $f(\emptyset)$ is not constrained.
--   3. **Independence system.** A predicate $\mathcal I$ on subsets with $\emptyset \in \mathcal I$ and $A \subseteq B \in \mathcal I \Rightarrow A \in \mathcal I$.
--   4. **$p$-extendible system.** For all $A \in \mathcal I$, every $B \in \mathcal I$ with $A \subseteq B$, and every $e \notin A$ with $A \cup \{e\} \in \mathcal I$, there is $Y \subseteq B \setminus A$ with $|Y| \le p$ and $(B \setminus Y) \cup \{e\} \in \mathcal I$.
--   5. **The greedy loop on a pool $P$.** At the current set $S$, the candidates are the $u \in P$ with $u \notin S$, $S \cup \{u\} \in \mathcal I$ and $f(u \mid S) > 0$. If there is a candidate, the loop adds the candidate of largest marginal gain, ties broken in favour of the element that comes first in the fixed order; otherwise $S$ is left unchanged.
--   6. **SampleGreedy (Algorithm 1).** Given a sample $\mathcal N' \subseteq \mathcal N$, run the greedy loop on the pool $\mathcal N'$ from $S = \emptyset$ for $n$ iterations. Only sampled elements can ever be added.
--   7. **Sampling weights and expected value.** Each element enters $\mathcal N'$ independently with probability $q$, so $\Pr[\mathcal N'] = q^{|\mathcal N'|}(1-q)^{n - |\mathcal N'|}$, and
--   $$\mathbb E[f(S)] \;=\; \sum_{\mathcal N' \subseteq \mathcal N} q^{|\mathcal N'|}(1-q)^{n-|\mathcal N'|}\, f\big(\mathrm{SampleGreedy}(\mathcal N')\big).$$
--
--   These are the objects the main theorem talks about: the expected value of the set returned by SampleGreedy is compared with $f(T)$ for every independent $T$.
--
--   **Formalization Note** The ground set is a `Fintype` with a `LinearOrder`, which is the paper's tie-breaking order (p. 10). Sets are `Finset`s; $\mathcal I$ is a predicate `Finset α → Prop`. The while loop is run for exactly $n$ iterations: each iteration that changes $S$ adds a new element, and an iteration with no candidate is the identity, so the loop has terminated after $n$ iterations. The expectation is the exact finite sum over all $2^n$ samples. Submodularity is the published lattice form $f(S\cup T)+f(S\cap T) \le f(S)+f(T)$, which on a finite ground set is equivalent to the paper's diminishing-returns form (1).
-- source:
--   Harshaw et al., arXiv:2104.02772v1, pp. 5–6 (§3: eq. (1), marginal gain, monotone, linear, independence system, p-extendible system; problem (2)), p. 9 (Algorithm 1), p. 10 (tie-breaking by an ordering of the ground set)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace SubsampleSubmod.SampleGreedy

open Finset

/-- Marginal gain `f(u | S) = f(S ∪ {u}) − f(S)` (Harshaw et al., arXiv:2104.02772v1, p. 5, §3). -/
def marg {α : Type} [DecidableEq α] (f : Finset α → ℝ) (u : α) (S : Finset α) : ℝ :=
  f (insert u S) - f S

/-- A set function is *linear* if the diminishing-returns inequality (1) holds with equality:
`f(A ∪ {e}) − f(A) = f(B ∪ {e}) − f(B)` for all `A ⊆ B` and `e ∉ B` (p. 5, §3).
No condition on `f(∅)` is imposed. -/
def IsLinear {α : Type} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, ∀ e : α, A ⊆ B → e ∉ B → f (insert e A) - f A = f (insert e B) - f B

/-- `(𝒩, ℐ)` is an independence system: `∅ ∈ ℐ`, and `ℐ` is closed under subsets (p. 5, §3). -/
def IsIndepSystem {α : Type} (I : Finset α → Prop) : Prop :=
  I ∅ ∧ ∀ A B : Finset α, A ⊆ B → I B → I A

/-- `p`-extendibility (p. 5, §3): for all `A ∈ ℐ`, every extension `B ∈ ℐ` of `A` (`A ⊆ B`) and every
`e ∉ A` with `A ∪ {e} ∈ ℐ`, there is `Y ⊆ B \ A` with `|Y| ≤ p` and `(B \ Y) ∪ {e} ∈ ℐ`. -/
def IsPExtendible {α : Type} [DecidableEq α] (p : ℕ) (I : Finset α → Prop) : Prop :=
  ∀ A B : Finset α, ∀ e : α, I A → I B → A ⊆ B → e ∉ A → I (insert e A) →
    ∃ Y : Finset α, Y ⊆ B \ A ∧ Y.card ≤ p ∧ I (insert e (B \ Y))

open Classical in
/-- The candidates of the greedy loop (Algorithm 1, line 6; Algorithm 2, line 2): the elements `u` of
the pool with `u ∉ S`, `S + u ∈ ℐ` and `f(u | S) > 0`. -/
noncomputable def cands {α : Type} [DecidableEq α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (pool S : Finset α) : Finset α :=
  pool.filter (fun u => u ∉ S ∧ I (insert u S) ∧ 0 < marg f u S)

open Classical in
/-- The element chosen by the greedy loop (Algorithm 1, line 7; Algorithm 2, line 3): among the
candidates, those maximizing `f(u | S)`, and among those the least one in the fixed linear order of
the ground set (the tie-breaking rule of p. 10). `none` when there is no candidate. -/
noncomputable def pick {α : Type} [LinearOrder α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (pool S : Finset α) : Option α :=
  let C := cands f I pool S
  let M := C.filter (fun u => ∀ v ∈ C, marg f v S ≤ marg f u S)
  if h : M.Nonempty then some (M.min' h) else none

/-- One iteration of the while loop of Algorithm 1 (lines 6–8) with sampled pool `𝒩′`: add the
chosen element to `S`; if there is no candidate, `S` is returned unchanged. -/
noncomputable def greedyStep {α : Type} [LinearOrder α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (pool : Finset α) (S : Finset α) : Finset α :=
  match pick f I pool S with
  | some u => insert u S
  | none => S

/-- The output of SampleGreedy (Algorithm 1, p. 9) on the sample `𝒩′`: the greedy loop started from
`S = ∅`, run for `n = |𝒩|` iterations (every effective iteration adds a new element, and an iteration
without candidate leaves `S` unchanged, so the loop has terminated after `n` iterations). -/
noncomputable def sampleGreedy {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (N' : Finset α) : Finset α :=
  (greedyStep f I N')^[Fintype.card α] ∅

/-- Probability `q^{|𝒩′|} (1 − q)^{n − |𝒩′|}` that the independent sampling of Algorithm 1
(lines 2–5) produces exactly `𝒩′` (`ℕ` subtraction is exact since `|𝒩′| ≤ n`). -/
noncomputable def sampleWeight {α : Type} [Fintype α] (q : ℝ) (N' : Finset α) : ℝ :=
  q ^ N'.card * (1 - q) ^ (Fintype.card α - N'.card)

/-- Expected value `E[f(S)]` of the output `S` of SampleGreedy with sampling probability `q`, as an
exact sum over the `2^n` possible samples. -/
noncomputable def expectedValue {α : Type} [Fintype α] [LinearOrder α] (q : ℝ)
    (f : Finset α → ℝ) (I : Finset α → Prop) : ℝ :=
  ∑ N' : Finset α, sampleWeight q N' * f (sampleGreedy f I N')

end SubsampleSubmod.SampleGreedy


