-- Prove2me | Definitions.Def_RendezvousKn_Sym_Model
-- name    : RendezvousKn_Sym_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:58.014487+00:00
-- url     : https://prove2.me/theorems/cb3f2c01-24f4-4315-8b30-d29f1f077fcb
-- title:
--   §2–§3, pp. 2–9 — rendezvous game on n locations: tactics, uniform binding, waiting time T, W, E T⟨σ_A, σ_B⟩, Definition 3, F, X, Var X, disjoint pairs
-- statement:
--   There are $n$ locations and two players $A$ and $B$, each with a private numbering of the locations by $[n]=\{1,\dots,n\}$.
--
--   1. A **tactic** is a function $\tau:[n]\to[n]$; $\tau(i)$ is the location, in the player's own numbering, visited in round $i$. The set of tactics is $\Theta_n$.
--   2. The **binding** is a permutation $\pi$ of $[n]$, drawn uniformly at random, that translates $A$'s labels into $B$'s labels. For a function $g$ of the binding, $\mathbb E[g(\pi)]=\frac1{n!}\sum_{\pi}g(\pi)$.
--   3. For tactics $\tau_A,\tau_B$ and a binding $\pi$, the **waiting time** is
--   $$T=\min\bigl(\{\,i\in[n]:\ \pi(\tau_A(i))=\tau_B(i)\,\}\cup\{n+1\}\bigr),$$
--   the first round in which both players stand at the same location, and $n+1$ if they never meet in the $n$ rounds. Its expectation over the binding is $W(\tau_A,\tau_B)=\mathbb E_\pi[T]$.
--   4. A **strategy** is a probability vector $\sigma$ on $\Theta_n$. For strategies $\sigma_A,\sigma_B$, the players draw $\tau_A\sim\sigma_A$ and $\tau_B\sim\sigma_B$ independently of each other and of $\pi$, and
--   $$\mathbb E\,T\langle\sigma_A,\sigma_B\rangle=\sum_{\tau_A,\tau_B\in\Theta_n}\sigma_A(\tau_A)\,\sigma_B(\tau_B)\,W(\tau_A,\tau_B).$$
--   5. (Definition 3) A tactic $\tau$ is **passive** if $|\tau([n])|\le n/2$ and **active** otherwise.
--   6. The probability of no rendezvous is $\mathbb P\bigl(\pi(\tau_A(i))\neq\tau_B(i)\ \text{for all } i\in[n]\bigr)$.
--   7. The **pair set** is $F=\{(\tau_A(i),\tau_B(i)):i\in[n]\}\subseteq[n]\times[n]$, with $m=|F|$. For $E(\pi)=\{(i,\pi(i)):i\in[n]\}$, $X_f$ is the indicator of $f\in E(\pi)$ and $X=|F\cap E(\pi)|=\sum_{f\in F}X_f$. Further $\operatorname{Var}X=\mathbb E X^2-(\mathbb E X)^2$ and $\mathbb P(X=0)$ are taken over the binding.
--   8. Two pairs $(i,j)$ and $(i',j')$ are **disjoint** if $i\neq i'$ and $j\neq j'$; the number of disjoint pairs in $F$ counts unordered pairs $\{e,f\}$ of distinct elements of $F$ that are disjoint.
--
--   These objects are shared by every statement of the mission: the goal is about $\mathbb E\,T\langle\sigma,\sigma\rangle$, and the lemmas about $W$, $F$ and $X$.
--
--   **Formalization Note** Locations and rounds are `Fin n`; Lean round $i$ is round $i+1$ of the paper, so the waiting time is the least $i+1$ with a meeting, or $n+1$. The uniform expectation over bindings is the finite average `avgPerm` over `Equiv.Perm (Fin n)`. Passivity is written $2\,|\tau([n])|\le n$. Strategies enter the theorems as elements of `stdSimplex ℝ (Fin n → Fin n)`.
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, pp. 2–9 (PDF 3–10), §2 (tactics, strategies, binding, T), §3.1 (W, Φ, Definition 3), §3.3 (F, m, E(π), X_f, X), §3.4 (disjoint pairs)

import Mathlib

namespace RendezvousKn.Sym

open Finset

/-- A tactic on `n` locations: `τ i` is the location (in the player's own numbering) visited in
round `i.val + 1`. Locations are `Fin n`, rounds are `Fin n` (round `i` of Lean is round `i + 1`
of the paper). -/
abbrev Tactic (n : ℕ) := Fin n → Fin n

/-- `avgPerm n g` is the expectation `E[g(π)]` of `g` at a uniformly random permutation
(binding) `π` of `Fin n`: the average of `g` over all `n!` permutations. -/
noncomputable def avgPerm (n : ℕ) (g : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ π : Equiv.Perm (Fin n), g π) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

/-- The waiting time till rendezvous for fixed tactics `τA`, `τB` and binding `π`:
`min ({i ∈ {1,…,n} : π(τA(i)) = τB(i)} ∪ {n + 1})`. The binding `π` translates A's location
labels into B's; the players meet in round `i + 1` when the location A visits is the location B
visits. If they never meet in the `n` rounds the time is `n + 1`. -/
def waitTime {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) : ℕ :=
  ((univ.filter fun i : Fin n => π (τA i) = τB i).image (fun i => i.val + 1) ∪ {n + 1}).min'
    ⟨n + 1, mem_union_right _ (mem_singleton_self _)⟩

/-- `W(τA, τB)`: the expected waiting time for fixed tactics, the expectation being over the
uniformly random binding only. -/
noncomputable def W {n : ℕ} (τA τB : Tactic n) : ℝ :=
  avgPerm n (fun π => (waitTime τA τB π : ℝ))

/-- `E T⟨σA, σB⟩`: the expected waiting time when A draws `τA ~ σA`, B draws `τB ~ σB` and the
binding `π` is uniform, all three independent. Strategies are probability vectors on tactics
(elements of `stdSimplex ℝ (Tactic n)` in the theorems). -/
noncomputable def expWait {n : ℕ} (σA σB : Tactic n → ℝ) : ℝ :=
  ∑ τA : Tactic n, ∑ τB : Tactic n, σA τA * σB τB * W τA τB

/-- Definition 3: a tactic is passive if it visits at most `n/2` distinct locations,
`|τ([n])| ≤ n/2` (written `2·|τ([n])| ≤ n`); otherwise it is active. -/
def IsPassive {n : ℕ} (τ : Tactic n) : Prop :=
  2 * (univ.image τ).card ≤ n

instance {n : ℕ} (τ : Tactic n) : Decidable (IsPassive τ) := by
  unfold IsPassive; infer_instance

/-- Probability, over the uniform binding, that no rendezvous occurs in the `n` rounds:
`P(π(τA(i)) ≠ τB(i) for all i)`. -/
noncomputable def noRdvProb {n : ℕ} (τA τB : Tactic n) : ℝ :=
  avgPerm n (fun π => if ∀ i, π (τA i) ≠ τB i then 1 else 0)

/-- The pair set `F = {(τA(i), τB(i)) : i ∈ [n]} ⊆ [n] × [n]`; `m = |F|`. -/
def pairSet {n : ℕ} (τA τB : Tactic n) : Finset (Fin n × Fin n) :=
  univ.image fun i => (τA i, τB i)

/-- `X = |F ∩ E(π)|` with `E(π) = {(i, π(i))}`: the number of pairs `f ∈ F` with `π f.1 = f.2`. -/
def matchCount {n : ℕ} (F : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) : ℕ :=
  (F.filter fun f => π f.1 = f.2).card

/-- The indicator `X_e` of the event `e ∈ E(π)`, i.e. `π e.1 = e.2`. -/
noncomputable def matchInd {n : ℕ} (e : Fin n × Fin n) (π : Equiv.Perm (Fin n)) : ℝ :=
  if π e.1 = e.2 then 1 else 0

/-- `Var X = E X² − (E X)²` for `X = matchCount F π`, `π` uniform. -/
noncomputable def varX {n : ℕ} (F : Finset (Fin n × Fin n)) : ℝ :=
  avgPerm n (fun π => (matchCount F π : ℝ) ^ 2) - (avgPerm n (fun π => (matchCount F π : ℝ))) ^ 2

/-- `P(X = 0)` for `X = matchCount F π`, `π` uniform. -/
noncomputable def probXZero {n : ℕ} (F : Finset (Fin n × Fin n)) : ℝ :=
  avgPerm n (fun π => if matchCount F π = 0 then 1 else 0)

/-- Two pairs `(i, j)` and `(i', j')` are disjoint if `i ≠ i'` and `j ≠ j'`. -/
def PairsDisjoint {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  e.1 ≠ f.1 ∧ e.2 ≠ f.2

instance {n : ℕ} (e f : Fin n × Fin n) : Decidable (PairsDisjoint e f) := by
  unfold PairsDisjoint; infer_instance

/-- The number of unordered pairs `{e, f}` of distinct elements of `F` that are disjoint. -/
def disjointPairCount {n : ℕ} (F : Finset (Fin n × Fin n)) : ℕ :=
  ((F.powersetCard 2).filter fun s => ∀ e ∈ s, ∀ f ∈ s, e ≠ f → PairsDisjoint e f).card

end RendezvousKn.Sym


