-- Prove2me | Definitions.Def_MinorityDynamics_Agents
-- name    : MinorityDynamics_Agents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:48.212947+00:00
-- url     : https://prove2.me/theorems/ed23c149-41d5-4465-ba76-726d09d4431b
-- title:
--   The k-Minority dynamics on configurations, with sources; consensus, minority count, orientation
-- statement:
--   There are $n$ agents, each holding one of two opinions (here `true`/`false`); a **configuration** is a map $\omega:\{1,\dots,n\}\to\{0,1\}$. In each synchronous round every non-source agent independently samples $k$ agents uniformly **with replacement** among all $n$ agents (itself and the sources included) and adopts the **less frequent opinion present in its sample**; a unanimous sample causes adoption of its single opinion. If $m$ is the number of `true` in a sample, `true` is adopted iff $m=k$, or $1\le m$ and $2m<k$. Agents in a fixed **source set** $\mathrm{Src}$ never change their opinion.
--
--   The module defines:
--
--   1. `minorityOf k c`, the opinion adopted after seeing the sample $c\in\{0,1\}^k$;
--   2. `agentStep n k Src ω ω'`, the probability that one round turns $\omega$ into $\omega'$: the samples of all agents form an array in $\{1,\dots,n\}^{n\times k}$ drawn uniformly, and $\omega'$ is the resulting configuration;
--   3. **consensus** (all agents hold the same opinion);
--   4. the **minority count** $\min\{\#\{i:\omega_i=1\},\#\{i:\omega_i=0\}\}$;
--   5. the **orientation** of $\omega$ with respect to the sources' opinion $b$: $1$ if $b$ is held by fewer than $n/2$ agents (the sources hold the minority opinion), $0$ otherwise.
--
--   This is the process of Theorem 1.1: the source-free dynamics is $\mathrm{Src}=\emptyset$; the dynamics with $\varrho$ sources sharing opinion $b$ takes $|\mathrm{Src}|=\varrho$ and a configuration in which every source holds $b$.
--
--   **Formalization Note** The rule is stated for every $k$; the paper takes $n$ and $k$ odd, so neither the population nor a sample has a tie.
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), §1, p.1 (k-Minority, sources); §2.1, p.10 (the dynamics); §8.1, p.41 (orientation)

import Mathlib

set_option autoImplicit false

namespace MinorityDynamics

open Classical

/-- The **k-Minority update rule** for one agent (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority
Dynamics with Small Samples*, manuscript (STOC 2027 submission), §1, p.1 = PDF p.3, and §2.1,
p.10 = PDF p.12): "It adopts the less frequent opinion present in its sample. Thus a unanimous
sample causes adoption of its single opinion."

`minorityOf k c` is the opinion adopted after seeing the sample `c : Fin k → Bool`. With
`m = #{j : c j = true}`, the opinion `true` is adopted iff the sample is unanimously `true`
(`m = k`), or `true` is present (`1 ≤ m`) and less frequent than `false` (`m < k − m`, i.e.
`2m < k`).

**Formalization Note** Opinions are `Bool`. The paper assumes `k` odd, so a sample never has a
tie; the rule is stated for every `k`. -/
noncomputable def minorityOf (k : ℕ) (c : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter (fun j => c j = true)).card = k ∨
    (1 ≤ (Finset.univ.filter (fun j => c j = true)).card ∧
      2 * (Finset.univ.filter (fun j => c j = true)).card < k))

/-- The configuration after one synchronous round of k-Minority with **source set** `Src`
(manuscript, §1, p.1, §2.1, p.10, §8.1, p.41), given all the samples at once:
`smp i j : Fin n` is the `j`-th agent sampled by agent `i`.
Every agent `i ∉ Src` adopts `minorityOf k (fun j => ω (smp i j))`; every source `i ∈ Src`
keeps its opinion `ω i`. -/
noncomputable def roundUpdate {n : ℕ} (k : ℕ) (Src : Finset (Fin n)) (ω : Fin n → Bool)
    (smp : Fin n → Fin k → Fin n) : Fin n → Bool :=
  fun i => if i ∈ Src then ω i else minorityOf k (fun j => ω (smp i j))

/-- **One round of k-Minority** as a transition matrix on configurations `Fin n → Bool`
(manuscript, §2.1, p.10 = PDF p.12: "In each synchronous round, every agent independently samples
k agents uniformly with replacement, including itself among the possible samples"; §8.1, p.41:
sources keep their opinion and are sampled like every other agent).

`agentStep n k Src ω ω'` is the probability that the configuration after one round is `ω'` when it
is `ω` before: the samples `smp : Fin n → Fin k → Fin n` are drawn uniformly from all `n^{nk}`
arrays, i.e. every agent draws `k` agents independently and uniformly from all `n` agents (itself
and the sources included), independently of the other agents.

**Formalization Note** With `Src = ∅` this is the source-free dynamics. Agents in `Src` do not
update. The source-free case of the paper takes `Src = ∅`; the case with `ϱ` sources sharing an
opinion takes `Src.card = ϱ` and a configuration in which all agents of `Src` hold that
opinion. -/
noncomputable def agentStep (n k : ℕ) (Src : Finset (Fin n)) (ω ω' : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter (fun smp : Fin n → Fin k → Fin n => roundUpdate k Src ω smp = ω')).card
      : ℝ) / (Fintype.card (Fin n → Fin k → Fin n) : ℝ)

/-- A configuration is at **consensus** if all agents hold the same opinion (manuscript, §1,
p.1). -/
def IsConsensus {n : ℕ} (ω : Fin n → Bool) : Prop := ∀ i j, ω i = ω j

/-- The number of agents holding opinion `b` in configuration `ω`. -/
noncomputable def opinionCount {n : ℕ} (ω : Fin n → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun i => ω i = b)).card

/-- The **minority count** of a configuration: the number of agents holding the less frequent
opinion, `min{#true, #false}` (manuscript, §2.1, p.10: `Xₜ` is the minority fraction, so
`n Xₜ` is this count). -/
noncomputable def minCount {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  min (opinionCount ω true) (opinionCount ω false)

/-- The **orientation** of a configuration with respect to the sources' opinion `b` (manuscript,
§8.1, p.41 = PDF p.43): `true` (orientation 1) if the sources' opinion `b` is the minority
opinion, i.e. fewer than `n/2` agents hold it, and `false` (orientation 0) otherwise. At
consensus on `b` the orientation is `false`, as on p.41. -/
noncomputable def orientation {n : ℕ} (b : Bool) (ω : Fin n → Bool) : Bool :=
  decide (2 * opinionCount ω b < n)

end MinorityDynamics


