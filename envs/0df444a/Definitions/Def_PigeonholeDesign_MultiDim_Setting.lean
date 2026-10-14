-- Prove2me | Definitions.Def_PigeonholeDesign_MultiDim_Setting
-- name    : PigeonholeDesign_MultiDim_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:37.333204+00:00
-- url     : https://prove2.me/theorems/8eb1b0db-bc2e-4c74-870a-b6d25c321fd5
-- title:
--   pp. 10–11, 13, 16, 21, 25–26 — discrepancy (1), completely randomized and pigeonhole designs, the grid pigeonholes of Theorem 9, the family 𝒳
-- statement:
--   This file sets up the model of Zhao and Zhou's *Pigeonhole Design* for several covariates.
--
--   **Subjects and assignments.** An even number $T$ of subjects arrive one at a time; subject $t$ carries a covariate vector $x_t$, and the whole sequence $x=(x_1,\dots,x_T)$ is fixed in advance. Each subject is assigned to control (group $A$) or treatment (group $B$) on arrival.
--
--   **Discrepancy (display (1)).** For a split $(A,B)$ with $|A|=|B|$, the discrepancy $d_{A,B}$ is the minimum total Euclidean distance of a perfect matching between $A$ and $B$,
--   $$d_{A,B}=\min_{\sigma:A\to B\ \text{bijective}}\ \sum_{t\in A}\lVert x_t-x_{\sigma(t)}\rVert_2 .$$
--   The integer program (1) is an assignment problem, whose optimum is attained at a permutation matrix, so this is its value. The same quantity for the subjects of a subset $U$ is $d_{A\cap U,B\cap U}$.
--
--   **Completely randomized design (Definition 2).** A uniformly random set of $T/2$ subjects is put in control and the rest in treatment; $\mathrm{ALG}^C(x)$ is the average of $d_{A,B}$ over the $\binom{T}{T/2}$ such splits.
--
--   **Pigeonhole design (Definition 3).** Given a partition of the covariate space into pigeonholes, subject $t$ is assigned as follows. (1) If the control or the treated group already has $T/2$ subjects, $t$ goes to the other group. (2) Otherwise let $n^0_{k,t-1}$, $n^1_{k,t-1}$ be the numbers of control and treated subjects so far in the pigeonhole $k$ of $x_t$: $t$ goes to control if $n^0_{k,t-1}<n^1_{k,t-1}$, to treatment if $n^0_{k,t-1}>n^1_{k,t-1}$, and to either with probability $1/2$ on a tie. Its expected discrepancy is the average of $d_{A,B}$ over all $2^T$ vectors of fair coins, one coin per subject, used only on a tie.
--
--   **Covariates (§2, §6.1).** There are $q$ discrete covariates, the $i$-th taking values in a finite set $S_i$ of size $m_i$, and $p$ continuous covariates in $[0,1]$. The covariate space is $\mathbb R^{q+p}$ with the Euclidean distance.
--
--   **Theorem 9's pigeonholes.** For an integer $m\ge1$ the pigeonholes are
--   $$S_1\times\cdots\times S_q\times\Big\{\big[0,\tfrac1m\big),\big[\tfrac1m,\tfrac2m\big),\dots,\big[1-\tfrac1m,1\big]\Big\}^p ,$$
--   so two subjects share a pigeonhole iff they have the same discrete values and the same cell on every continuous axis. The number of cells per axis is $m=\lceil c^{-1/p}T^{\varphi}\rceil$, so each cell has edge $1/m\le c^{1/p}T^{-\varphi}$.
--
--   **The family $\mathcal X$ (p. 25).** With no discrete covariates and $T=m^p$, $\mathcal X^{(T)}$ is the set of sequences in $[0,1]^p$ with exactly one subject in each of the $m^p$ cells of edge $T^{-1/p}=1/m$.
--
--   These are the objects of Theorem 9, Lemma 5 and their proofs. The discrepancy, the completely randomized design and the pigeonhole design are the shared definitions of `PigeonholeDesign.Upper.Setting` (with `PigeonholeDesign.Lower.assign` as an alias of the design's run), which this file imports; it adds the covariate space, admissibility, the grid pigeonholes, the cell count and the family $\mathcal X$.
--
--   **Formalization Note** Subjects are indexed $0,\dots,T-1$ (`Fin T`); the paper's subject $t$ is $t-1$ here. An assignment is a map to `Bool`, `false` = control, `true` = treated. The discrepancy is an infimum over bijections between the two groups; if the groups differ in size there is no bijection and the value is the junk $0$. The pigeonhole design is always balanced (milestone `assign_balanced`), and so are the matched set and its complement used in the proof, so the junk is never reached by the objects of this mission. The pigeonhole design is a recursion over prefixes that checks Step 1 before Step 2. A pigeonhole is the value of `gridHole m`: the exact discrete coordinates and the index $\min(\lfloor z_j m\rfloor, m-1)$ on each continuous axis. The printed cells have edge $c^{1/p}T^{-\varphi}$, a partition only when $c^{-1/p}T^{\varphi}$ is an integer; the ceiling $m$ is the formalization's reading. "Exactly one subject per cell" in $\mathcal X$ is stated as injectivity of the cell map together with $T=m^p$, which is equivalent to a bijection onto the cells; the printed `x′_t ∉ 𝕏` is read as $x_{t'}\notin\mathbb X$.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. 10–11 display (1), p. 13 Definition 2, p. 16 Definition 3, p. 21 §6.1, p. 25 family 𝒳, p. 26 Theorem 9, p. ec2 Algorithm 2

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Lower_Setting

namespace PigeonholeDesign.MultiDim

/-!
Zhao and Zhou, *Pigeonhole Design*, arXiv:2201.12936v6: the model of §2 (pp. 9–12), display (1)
(p. 11), Definition 2 (p. 13), Definition 3 (p. 16), §6.1 (p. 21), the family 𝒳 of §6.3.2 (p. 25)
and the pigeonholes of Theorem 9 / Algorithm 2 (p. 26, p. ec2). Subjects are indexed from 0
(`Fin T`); the paper's subject `t` is `t - 1` here. An assignment is `w : Fin T → Bool`, with
`w t = false` for control (group A) and `w t = true` for treatment (group B).
-/

/-- Covariate space with `q` discrete and `p` continuous coordinates, with the Euclidean (L2)
distance of display (1). -/
abbrev Cov (q p : ℕ) := EuclideanSpace ℝ (Fin q ⊕ Fin p)

/-- Admissible arrival sequences: the `i`-th discrete coordinate lies in the finite support `S i`
(§6.1, p. 21), every continuous coordinate in `[0,1]` (p. 10). -/
def Admissible {q p T : ℕ} (S : Fin q → Finset ℝ) (x : Fin T → Cov q p) : Prop :=
  (∀ t i, x t (Sum.inl i) ∈ S i) ∧ (∀ t j, x t (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1)

/-- Theorem 9's pigeonholes `S₁ × … × S_q × {[0,1/m), [1/m,2/m), …, [1-1/m,1]}^p`: a point is
keyed by its exact discrete values and, on each continuous axis, by the cell index
`min ⌊z·m⌋ (m-1)` (the last cell is closed). -/
noncomputable def gridHole {q p : ℕ} (m : ℕ) (z : Cov q p) : (Fin q → ℝ) × (Fin p → ℕ) :=
  (fun i => z (Sum.inl i), fun j => min ⌊z (Sum.inr j) * m⌋₊ (m - 1))

/-- Cells per continuous axis: `c^{-1/p} T^φ`, rounded up, so each cell has edge
`1/m ≤ c^{1/p} T^{-φ}`. -/
noncomputable def cellsPerAxis (p : ℕ) (c φ : ℝ) (T : ℕ) : ℕ :=
  ⌈c ^ (-(1 : ℝ) / p) * (T : ℝ) ^ φ⌉₊

/-- The family `𝒳^{(T)}` of §6.3.2 (p. 25) for `T = m^p`: no discrete coordinates, every `x_t` in
`[0,1]^p`, and exactly one subject in each of the `m^p` cells
`[k₁/m,(k₁+1)/m) × … × [k_p/m,(k_p+1)/m)` (last cell closed on each axis). Exactly one per cell is
stated as injectivity of the cell index map, which with `T = m^p` is bijectivity onto the cells. -/
def InGridFamily {p T : ℕ} (m : ℕ) (x : Fin T → EuclideanSpace ℝ (Fin p)) : Prop :=
  T = m ^ p ∧ (∀ t j, x t j ∈ Set.Icc (0 : ℝ) 1) ∧
    Function.Injective (fun t : Fin T => fun j : Fin p => min ⌊x t j * m⌋₊ (m - 1))

end PigeonholeDesign.MultiDim


