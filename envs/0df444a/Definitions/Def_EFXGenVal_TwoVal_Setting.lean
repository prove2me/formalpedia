-- Prove2me | Definitions.Def_EFXGenVal_TwoVal_Setting
-- name    : EFXGenVal_TwoVal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:16.108292+00:00
-- url     : https://prove2.me/theorems/ecec9e4b-0777-46f0-a7ec-4ef13a7882d8
-- title:
--   §2–§4 and Appendix A, pp. 6–12, 25 — non-degeneracy, EFX envy, Pareto domination, κ_X, most envious agents, champions, PI cycles, semi-EFX, partition leximin ψ, perturbation
-- statement:
--   This file fixes the vocabulary of Mahara's proof that complete EFX allocations exist when every agent has one of two general valuations. Throughout, there are $n$ agents $0,\dots,n-1$ and $m$ indivisible items $0,\dots,m-1$; agent $i$ has a valuation $v_i : 2^M \to \mathbb R$, and an allocation is a family $X=(X_0,\dots,X_{n-1})$ of bundles (pairwise disjointness, the pool of unallocated items, envy and EFX come from the published file `LittleCharity.EFX.Setting`). We write $S <_i T$ for $v_i(S) < v_i(T)$.
--
--   1. **Non-degeneracy** (Definition 4). The profile is non-degenerate if $S \neq T$ implies $v_i(S) \neq v_i(T)$ for every agent $i$.
--   2. **EFX envy** (§2). Agent $i$ EFX envies agent $j$ in $X$ if $X_i <_i X_j \setminus \{h\}$ for some $h \in X_j$.
--   3. **Pareto domination** (§2.1). $Y$ Pareto dominates $X$ if $Y_i \ge_i X_i$ for all $i$ and $Y_j >_j X_j$ for some $j$.
--   4. **Minimum preferred sets and $\kappa_X$** (§2.2). For $S >_i X_i$, a minimum preferred set of $i$ for $S$ is a smallest-cardinality $P \subseteq S$ with $P >_i X_i$ (there may be several). Then
--   $$\kappa_X(i,S)=\begin{cases}|P_X(i,S)| & \text{if } S>_i X_i,\\ +\infty & \text{otherwise,}\end{cases}$$
--   valued in $\mathbb N\cup\{+\infty\}$.
--   5. **Most envious agents** (§2.2). Agent $i$ is a most envious agent for $S$ if $S >_i X_i$ and $\kappa_X(i,S) \le \kappa_X(j,S)$ for every agent $j$.
--   6. **Champions** (§2.3). Agent $i$ $g$-champions $j$ (possibly $i=j$) if $i$ is a most envious agent for $X_j \cup \{g\}$; $i$ is a self $g$-champion if it $g$-champions itself.
--   7. **Decomposition** (§2.3). Agent $i$ $g$-decomposes $j$ if $i$ $g$-champions $j$ and every minimum preferred set $P$ of $i$ for $X_j\cup\{g\}$ satisfies $\{g\} \subsetneq P \subsetneq X_j \cup \{g\}$.
--   8. **Pareto improvable cycles** (Definitions 6–7). A cycle $a_1 \xrightarrow{H_1} a_2 \xrightarrow{H_2} \cdots \xrightarrow{H_k} a_1$ of distinct agents in the champion graph $M_X$, where each label $H_t$ is either $\emptyset$ (an envy edge: $a_t$ envies $a_{t+1}$) or a singleton $\{g\}$ of an unallocated item (a champion edge: $a_t$ $g$-champions $a_{t+1}$), and labels of distinct edges are disjoint.
--   9. **Semi-EFX** (§4). With the agents split into $N_a$ and $N_b$, $X$ is semi-EFX if no agent of $N_a$ EFX envies anyone and no agent of $N_b$ EFX envies an agent of $N_a$.
--   10. **Partition leximin potential** (§4, Definition 13). For two set functions $v_a, v_b$ and the split $N_a, N_b$,
--   $$\psi(X)=\bigl(v_a(X_{a_0}),\dots,v_a(X_{a_s}),\,v_b(X_{b_0}),\dots,v_b(X_{b_t})\bigr),$$
--   with each block in increasing order; $Y \succ_{\mathrm{p.lexmin}} X$ if $\psi(Y)$ is strictly lexicographically larger than $\psi(X)$.
--   11. **Perturbation** (Appendix A). For $\varepsilon>0$,
--   $$v'_i(S) = v_i(S) + \varepsilon \sum_{j \in S} 2^{j}.$$
--
--   These are the objects of the potential-function argument: champions and PI cycles produce Pareto improvements, semi-EFX allocations are repaired into EFX ones, and $\psi$ measures progress.
--
--   **Formalization Note** Agents are `Fin n` and items `Fin m`, both 0-indexed; the page's item $g_j$ of Appendix A is the item `j`. Valuations are real-valued; the page's codomain $\mathbb R_{\ge 0}$ follows from normalization and monotonicity. $\kappa$ takes values in `ℕ∞`, with $\top$ for $+\infty$. The membership "$\kappa_X(i,S)=\kappa_X(S)$" is written as "$\kappa_X(i,S)\le\kappa_X(j,S)$ for all $j$", together with $S>_iX_i$. In a PI cycle the edge label is an `Option` item (`none` for $\emptyset$, `some g` for $\{g\}$), the successor of the last vertex is the first (`finRotate`), the vertices are distinct, and the page's "for every $i,j\in[k]$, $H_i\cap H_j=\emptyset$" is read for $i\neq j$ (read literally with $i=j$ it would force every label empty). Decomposition quantifies over every minimum preferred set, which the proof of Lemma 5 establishes. $N_a$ is a finset `A` of agents and $N_b$ its complement; $\psi$ sorts each block increasingly, which handles ties (two empty bundles) that the page's strict chain $X_{a_0}<_a X_{a_1}<_a\cdots$ leaves implicit.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, §2 and Definition 4 (p. 6), §2.1–§2.2 (p. 7), §2.3 and Definitions 6–7 (pp. 7–8), §4 and Definition 13 (pp. 11–12), Appendix A (pp. 24–25)

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

/-- Definition 4 (p. 6): an instance is non-degenerate if distinct bundles have distinct
values for every agent. -/
def IsNonDegenerate {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i S T, S ≠ T → v i S ≠ v i T

/-- §2, p. 6: agent `i` EFX envies agent `j` in `X` if `i` envies `X j \ h` for some
`h ∈ X j`. -/
def EFXEnvies {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (X : Fin n → Finset (Fin m))
    (i j : Fin n) : Prop :=
  ∃ h ∈ X j, v i (X i) < v i ((X j).erase h)

/-- §2.1, p. 7: `Y` Pareto dominates `X`. -/
def ParetoDominates {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (Y X : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, v i (X i) ≤ v i (Y i)) ∧ ∃ j, v j (X j) < v j (Y j)

/-- §2.2, p. 7: `P` is a minimum preferred set of agent `i` for `S` with respect to `X`:
a smallest-cardinality subset of `S` that `i` strictly prefers to `X i`. -/
def IsMinPreferredSet {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (i : Fin n) (S P : Finset (Fin m)) : Prop :=
  P ⊆ S ∧ v i (X i) < v i P ∧ ∀ T ⊆ S, v i (X i) < v i T → P.card ≤ T.card

/-- §2.2, p. 7: `κ_X(i, S)`, the size of a minimum preferred set of `i` for `S` if
`S >_i X_i`, and `+∞` otherwise. -/
noncomputable def kappa {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (i : Fin n) (S : Finset (Fin m)) : ℕ∞ :=
  if v i (X i) < v i S then
    ⨅ (T : Finset (Fin m)) (_ : T ⊆ S ∧ v i (X i) < v i T), (T.card : ℕ∞)
  else ⊤

/-- §2.2, p. 7: `i ∈ A_X(S)`, i.e. `i` is a most envious agent for `S`. -/
def IsMostEnvious {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) (i : Fin n) : Prop :=
  v i (X i) < v i S ∧ ∀ j, kappa v X i S ≤ kappa v X j S

/-- §2.3, p. 7: `i` g-champions `j` (possibly `i = j`): `i` is a most envious agent for
`X j ∪ {g}`. That `g` is unallocated is a separate hypothesis wherever it is needed. -/
def Champions {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (g : Fin m) (i j : Fin n) : Prop :=
  IsMostEnvious v X (insert g (X j)) i

/-- §2.3, p. 8: `i` g-decomposes `j`: `i` g-champions `j`, and every minimum preferred set
`P` of `i` for `X j ∪ {g}` satisfies `{g} ⊊ P ⊊ X j ∪ {g}`. -/
def Decomposes {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (g : Fin m) (i j : Fin n) : Prop :=
  Champions v X g i j ∧
    ∀ P, IsMinPreferredSet v X i (insert g (X j)) P → {g} ⊂ P ∧ P ⊂ insert g (X j)

/-- Definitions 6–7, p. 8: a Pareto improvable cycle `a 0 → a 1 → ⋯ → a (k-1) → a 0` in the
champion graph `M_X`. The edge leaving `a t` carries label `H t`: `none` is an envy edge
(`a t` envies `a (t+1)`), `some g` is a champion edge (`g` unallocated and `a t`
g-champions `a (t+1)`). The vertices are distinct and the labels of distinct edges are
disjoint. -/
def IsPICycle {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (X : Fin n → Finset (Fin m))
    (k : ℕ) (a : Fin k → Fin n) (H : Fin k → Option (Fin m)) : Prop :=
  0 < k ∧ Function.Injective a ∧
    (∀ t, match H t with
      | none => Envies v X (a t) (a (finRotate k t))
      | some g => g ∈ pool X ∧ Champions v X g (a t) (a (finRotate k t))) ∧
    (∀ s t, s ≠ t → ∀ g, H s = some g → H t ≠ some g)

/-- §4, p. 12: `X` is semi-EFX with respect to the class `N_a = A`, `N_b = Aᶜ`: no agent of
`N_a` EFX envies anyone, and no agent of `N_b` EFX envies an agent of `N_a`. -/
def IsSemiEFX {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (X : Fin n → Finset (Fin m)) : Prop :=
  (∀ i ∈ A, ∀ j, ¬ EFXEnvies v X i j) ∧ (∀ i ∉ A, ∀ j ∈ A, ¬ EFXEnvies v X i j)

/-- §4, p. 11: the partition leximin potential `ψ(X)`: the `v_a`-values of the bundles of
`N_a = A` in increasing order, followed by the `v_b`-values of the bundles of `N_b = Aᶜ` in
increasing order. -/
noncomputable def psi {n m : ℕ} (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (X : Fin n → Finset (Fin m)) : List ℝ :=
  (A.val.map (fun i => va (X i))).sort (· ≤ ·) ++
    (Aᶜ.val.map (fun i => vb (X i))).sort (· ≤ ·)

/-- Definition 13, p. 11: `Y ≻_{p.lexmin} X`, i.e. `ψ(Y)` is lexicographically (strictly)
larger than `ψ(X)`. -/
def PLexGT {n m : ℕ} (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (Y X : Fin n → Finset (Fin m)) : Prop :=
  List.Lex (· < ·) (psi va vb A X) (psi va vb A Y)

/-- Appendix A, p. 25: the perturbed valuations `v'_i(S) = v_i(S) + ε ∑_{g_j ∈ S} 2^j`, with
item `g_j` the element `j : Fin m`. -/
noncomputable def perturb {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (ε : ℝ) :
    Fin n → Finset (Fin m) → ℝ :=
  fun i S => v i S + ε * ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ)

end EFXGenVal.TwoVal


