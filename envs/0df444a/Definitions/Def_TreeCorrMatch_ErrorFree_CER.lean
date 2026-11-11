-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_CER
-- name    : TreeCorrMatch_ErrorFree_CER
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:05.526318+00:00
-- url     : https://prove2.me/theorems/541ea39d-f682-4e19-b3b3-e1f8430f2c5b
-- title:
--   The correlated Erdős–Rényi graph-pair model CER$(n,\lambda,s)$ and the union graph
-- statement:
--   Let $n\ge1$, $s\in(0,1]$ and $\lambda\in(0,ns]$. In the **correlated Erdős–Rényi model** CER$(n,\lambda,s)$ a parent graph on $[n]$ contains each of the $\binom n2$ pairs independently with probability $\lambda/(ns)$; two graphs $G$ and $G'$ on $[n]$ each keep every parent edge independently with probability $s$. A permutation $\pi$ of $[n]$ is drawn uniformly at random, independently of the edges, and $\tilde G$ is $G'$ relabeled by $\pi$: $\{\pi(i),\pi(j)\}\in E(\tilde G)$ iff $\{i,j\}\in E(G')$. One observes $(G,\tilde G)$; $\tilde u=\pi(u)$ is the counterpart of $u$. A pair is an edge of both $G$ and $G'$ with probability $\lambda s/n$, of exactly one of them with probability $\lambda(1-s)/n$ each, and each of $G,\tilde G$ is marginally Erdős–Rényi with edge probability $\lambda/n$.
--
--   The probability of an outcome $(G,\tilde G,\pi)$ is
--
--   $$\frac1{n!}\prod_{1\le i<j\le n} w\big(\mathbf 1\{\{i,j\}\in E(G)\},\ \mathbf 1\{\{\pi(i),\pi(j)\}\in E(\tilde G)\}\big),$$
--
--   with $w(1,1)=ps^2$, $w(1,0)=w(0,1)=ps(1-s)$, $w(0,0)=1-ps(2-s)$ and $p=\lambda/(ns)$. The file defines the probability of an event of $(G,\tilde G,\pi)$, and the joint probability of an event of $(G,\tilde G,\pi)$ and of independent algorithmic randomness $\omega\sim\nu$, $\sum_x \mathrm{CER}(x)\,\nu\{\omega: E(x,\omega)\}$.
--
--   The **union graph** $\bar G$ on $[n]$ has edge set $E\cup\{\{i,j\}: \{\pi(i),\pi(j)\}\in\tilde E\}$.
--
--   **Formalization Note** Outcomes are triples `(G, G̃, π)` of `SimpleGraph (Fin n)`, `SimpleGraph (Fin n)` and `Equiv.Perm (Fin n)`. The parent probability is clamped to $[0,1]$, which changes nothing when $0<\lambda\le ns$ (the model's range, true for all large $n$ under the mission's assumptions).
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 1, §1 (PDF p. 3); p. 5, §2.1 (PDF p. 7); p. 15, App. A.1 (PDF p. 17)

import Mathlib

/-!
The correlated Erdős–Rényi graph-pair model `CER(n, λ, s)` with a uniformly random planted
permutation, and the union graph `Ḡ`.

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), §1, p. 1; §2.1, p. 5;
App. A.1, p. 15.
-/

namespace TreeCorrMatch.ErrorFree

open MeasureTheory
open scoped Classical

/-- An outcome of `CER(n, λ, s)`: the observed graphs `G` and `G̃` on the node set `[n]`
(`Fin n`), and the planted permutation `π`. -/
abbrev CEROutcome (n : ℕ) : Type :=
  SimpleGraph (Fin n) × SimpleGraph (Fin n) × Equiv.Perm (Fin n)

/-- The parent edge probability `λ/(ns)`, clamped to `[0, 1]` (the model requires `λ ∈ (0, ns]`;
the clamp only affects the finitely many `n` with `λ_n > ns`). -/
noncomputable def parentProb (n : ℕ) (lam s : ℝ) : ℝ := max 0 (min 1 (lam / (n * s)))

/-- The joint probability of the events `{i,j} ∈ E(G)` (`a`) and `{i,j} ∈ E(G′)` (`b`) for one
unordered pair: the parent edge is present with probability `p`, and each of `G`, `G′` keeps it
independently with probability `s`. -/
noncomputable def pairWeight (p s : ℝ) : Bool → Bool → ℝ
  | true, true => p * s ^ 2
  | true, false => p * s * (1 - s)
  | false, true => p * (1 - s) * s
  | false, false => 1 - p * s * (2 - s)

/-- The probability of the outcome `(G, G̃, π)` under `CER(n, λ, s)`: `π` is uniform on the `n!`
permutations of `[n]`, independent of the edges; every unordered pair `{i, j}` independently carries
the pair of indicators (`{i,j} ∈ E(G)`, `{i,j} ∈ E(G′)`), and `G̃` is `G′` relabeled by `π`, so that
`{i,j} ∈ E(G′)` iff `{π i, π j} ∈ E(G̃)`. -/
noncomputable def cerWeight (n : ℕ) (lam s : ℝ) (x : CEROutcome n) : ℝ :=
  (1 / (n.factorial : ℝ)) *
    ∏ i : Fin n, ∏ j : Fin n,
      if i < j then
        pairWeight (parentProb n lam s) s (decide (x.1.Adj i j))
          (decide (x.2.1.Adj (x.2.2 i) (x.2.2 j)))
      else 1

/-- The probability under `CER(n, λ, s)` of an event of `(G, G̃, π)`. -/
noncomputable def cerProb (n : ℕ) (lam s : ℝ) (E : CEROutcome n → Prop) : ℝ :=
  ∑ x : CEROutcome n, if E x then cerWeight n lam s x else 0

/-- The probability of an event of `(G, G̃, π)` and of algorithmic randomness `ω ∼ ν` independent
of `(G, G̃, π)`: `∑_x CER(x) · ν{ω : E x ω}`. -/
noncomputable def cerSeedProb {Ω : Type} [MeasurableSpace Ω] (n : ℕ) (lam s : ℝ) (ν : Measure Ω)
    (E : CEROutcome n → Ω → Prop) : ℝ :=
  ∑ x : CEROutcome n, cerWeight n lam s x * (ν {ω | E x ω}).toReal

/-- The union graph `Ḡ` on `[n]`: edge set `E ∪ {(i, j) : (π(i), π(j)) ∈ Ẽ}`. -/
def unionGraph {n : ℕ} (x : CEROutcome n) : SimpleGraph (Fin n) :=
  x.1 ⊔ x.2.1.comap x.2.2

end TreeCorrMatch.ErrorFree


