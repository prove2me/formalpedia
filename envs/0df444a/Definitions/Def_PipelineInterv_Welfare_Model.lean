-- Prove2me | Definitions.Def_PipelineInterv_Welfare_Model
-- name    : PipelineInterv_Welfare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:23.140073+00:00
-- url     : https://prove2.me/theorems/58db6991-9b95-461e-9c5a-f506e4d7d3f4
-- title:
--   §2–§4, pp. 4–10 — pipeline intervention instance, ℓ1 cost, feasible set F(B, M⁰), welfare, budget grid, ε-net, Algorithm 1 as a run relation
-- statement:
--   This file sets up the pipeline intervention model of Arunachaleswaran, Kannan, Roth and Ziani and the dynamic program (Algorithm 1) that approximately maximizes social welfare in it.
--
--   **Distributions and norms.** The simplex $\mathcal D$ is the set of vectors $D\in\mathbb R^w$ with $D(i)\ge 0$ and $\sum_i D(i)=1$. For $x\in\mathbb R^w$ write $\|x\|_1=\sum_i |x(i)|$ and $\|x\|_\infty=\max_i |x(i)|$. A matrix $M\in\mathbb R^{w\times w}$ is **left stochastic**, $M\in\mathcal M$, if its entries are nonnegative and every column sums to one; $M(i,j)$ is the probability of moving from node $j$ to node $i$, and distributions are multiplied on the right, $D\mapsto MD$.
--
--   **Instances.** A layered graph has $k$ layers $L_1,\dots,L_k$ of width $w$. An instance consists of initial transition matrices $M^0_1,\dots,M^0_{k-1}\in\mathcal M$, an initial distribution $D_1\in\mathcal D$ on $L_1$, a reward vector $R\in\mathbb R^w$ with $R\ge 0$ on the last layer, and for each transition $t$ a set $E^t_{mal}$ of malleable entries. The cost of replacing $M^0_t$ by $M_t$ is
--   $$c(M_t,M^0_t)=\sum_{(i,j)\in[w]^2}|M_t(i,j)-M^0_t(i,j)|.$$
--   The feasible set $\mathcal F(B,M^0_1,\dots,M^0_{k-1})$ consists of the tuples $(M_1,\dots,M_{k-1})$ with every $M_t\in\mathcal M$, $M_t(i,j)=M^0_t(i,j)$ for every non-malleable entry $(i,j)\notin E^t_{mal}$, and $\sum_t c(M_t,M^0_t)\le B$. The social welfare of a tuple is
--   $$W(M_1,\dots,M_{k-1})=R^\top M_{k-1}\cdots M_1 D_1 .$$
--
--   **Discretization.** For $\varepsilon>0$ and $B\ge 0$ the budget grid is $\{n\varepsilon: n\in\mathbb N,\ n\varepsilon\le B\}$ and $B^\varepsilon=\lfloor B/\varepsilon\rfloor\,\varepsilon$ is its largest element. A finite set $S\subseteq\mathcal D$ is an **$\varepsilon$-net** of $\mathcal D$ in $\ell_1$ (Definition 1) if every $D\in\mathcal D$ has some $D'\in S$ with $\|D-D'\|_1\le\varepsilon$.
--
--   **Algorithm 1.** Program (7) at transition $t$ with budget $b$ asks for $M_t\in\mathcal M$ that agrees with $M^0_t$ off $E^t_{mal}$ and has $c(M_t,M^0_t)\le b$. A run of Algorithm 1 is a table $M(B_{\ge t},D_t)$, indexed by the transition, a grid budget and a distribution (the net $S$, or $D_1$ at the first layer), such that $M(B_{\ge k},D_k)=I$ and each entry equals $M(B_{\ge t+1},D_{t+1})\,M_t$ for some grid budget $B_{\ge t+1}\le B_{\ge t}$, some $D_{t+1}\in S$ and some $M_t$ feasible for Program (7) with budget $B_{\ge t}-B_{\ge t+1}$, chosen to maximize $R^\top M(B_{\ge t+1},D_{t+1})M_tD_t$ over all such choices (ties broken arbitrarily). The output is $M(B^\varepsilon,D_1)$. The file also counts the instances of Program (7) the algorithm solves.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Transitions are 0-based: `Fin K` with $K=k-1$, and Lean index $t$ is the paper's transition $t+1$. A table entry is stored as the full tuple of transitions, with $M^0$ in the positions before $t$; the suffix product $M_{K-1}\cdots M_t$ recovers the paper's matrix $M(B_{\ge t},D_t)$. The §2 conventions "$D_1(u)>0$ for all $u$" and "rewards pairwise distinct", which the paper takes without loss of generality, are not imposed. The grid is cut at $B$ because Algorithm 1 only uses grid budgets $\le B$. Mathlib's `Matrix.colStochastic` is the paper's $\mathcal M$; `l1` and `supNorm` are written out because the default norm on `Fin w → ℝ` is the sup norm.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, pp. 4–10, §2 (instance, c(M_t, M⁰_t), F(B, M⁰), W), §3 (𝔅(ε), Definition 1), Algorithm 1, Program (7)

import Mathlib

namespace PipelineInterv.Welfare

open Matrix

/-- `D` is a probability distribution on `Fin w`: an element of the simplex 𝒟 (p. 4). -/
def IsDist {w : ℕ} (D : Fin w → ℝ) : Prop :=
  (∀ i, 0 ≤ D i) ∧ ∑ i, D i = 1

/-- The ℓ1 norm `‖x‖₁ = ∑ᵢ |x i|` (written out; the default norm on `Fin w → ℝ` is the sup norm). -/
def l1 {w : ℕ} (x : Fin w → ℝ) : ℝ :=
  ∑ i, |x i|

/-- The sup norm `‖R‖∞ = maxᵢ |R i|` (equal to `0` when `w = 0`). -/
noncomputable def supNorm {w : ℕ} (R : Fin w → ℝ) : ℝ :=
  ⨆ i, |R i|

/-- Definition 1 (p. 8), with `K = 𝒟`: `S` is a finite subset of the simplex such that every
distribution lies within ℓ1 distance `ε` of some element of `S`. -/
def IsEpsNet {w : ℕ} (ε : ℝ) (S : Finset (Fin w → ℝ)) : Prop :=
  (∀ D ∈ S, IsDist D) ∧ ∀ D, IsDist D → ∃ D' ∈ S, l1 (D - D') ≤ ε

/-- The intervention cost `c(M, M⁰) = ∑_{(i,j)} |M(i,j) − M⁰(i,j)|` (p. 5). -/
def cost {w : ℕ} (M M0 : Matrix (Fin w) (Fin w) ℝ) : ℝ :=
  ∑ i, ∑ j, |M i j - M0 i j|

/-- An instance of the pipeline intervention problem (§2, pp. 4–5) with `k = K + 1` layers of width
`w`. Transition `t : Fin K` (0-based) is the paper's transition `t + 1`, from layer `L_{t+1}` to
`L_{t+2}`. `M0 t i j` is the probability of moving from node `j` to node `i`; `mal t` is the set
`E^t_mal` of malleable entries of transition `t`. -/
structure Instance (w K : ℕ) where
  M0 : Fin K → Matrix (Fin w) (Fin w) ℝ
  D1 : Fin w → ℝ
  R : Fin w → ℝ
  mal : Fin K → Set (Fin w × Fin w)

variable {w K : ℕ}

/-- Standing assumptions of §2 (p. 4): every `M⁰_t` is left stochastic (columns sum to one,
entries nonnegative), `D1` is a distribution, and rewards are nonnegative. -/
def Instance.Standing (I : Instance w K) : Prop :=
  (∀ t, I.M0 t ∈ colStochastic ℝ (Fin w)) ∧ IsDist I.D1 ∧ ∀ v, 0 ≤ I.R v

/-- `M` agrees with `M⁰_t` on every non-malleable entry (the complement of `E^t_mal`). -/
def Respects (I : Instance w K) (t : Fin K) (M : Matrix (Fin w) (Fin w) ℝ) : Prop :=
  ∀ i j, (i, j) ∉ I.mal t → M i j = I.M0 t i j

/-- Membership in the feasible set `F(B, M⁰_1, …, M⁰_{k−1})` (p. 5). -/
def Feasible (I : Instance w K) (B : ℝ) (M : Fin K → Matrix (Fin w) (Fin w) ℝ) : Prop :=
  (∀ t, M t ∈ colStochastic ℝ (Fin w)) ∧ (∀ t, Respects I t (M t)) ∧
    ∑ t, cost (M t) (I.M0 t) ≤ B

/-- The suffix product `M_{K−1} ⋯ M_t` (0-based; the identity when `t ≥ K`). -/
def sufProd (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  (((List.finRange K).filter (fun s => t ≤ s.val)).reverse.map M).prod

/-- The prefix product `M_{t−1} ⋯ M_0` (0-based; the identity when `t = 0`). -/
def prefProd (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ) : Matrix (Fin w) (Fin w) ℝ :=
  (((List.finRange K).filter (fun s => s.val < t)).reverse.map M).prod

/-- `R⊤ M_{K−1} ⋯ M_t D`: the expected final reward of a distribution `D` on the layer before
transition `t`. -/
def valueFrom (I : Instance w K) (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (t : ℕ)
    (D : Fin w → ℝ) : ℝ :=
  I.R ⬝ᵥ (sufProd M t *ᵥ D)

/-- Social welfare `W(M_1, …, M_{k−1}) = R⊤ M_{k−1} ⋯ M_1 D_1` (p. 6). -/
def welfare (I : Instance w K) (M : Fin K → Matrix (Fin w) (Fin w) ℝ) : ℝ :=
  valueFrom I M 0 I.D1

/-- The budget grid `{nε : n ∈ ℕ, nε ≤ B}`, i.e. the elements of `𝔅(ε)` (p. 7) not exceeding `B`
(for `ε > 0`, `B ≥ 0`). -/
noncomputable def budgetGrid (ε B : ℝ) : Finset ℝ :=
  (Finset.range (⌊B / ε⌋₊ + 1)).image (fun n : ℕ => (n : ℝ) * ε)

/-- `B^ε = max{x ∈ 𝔅(ε) : x ≤ B} = ⌊B/ε⌋ ε` (Algorithm 1, p. 10). -/
noncomputable def Beps (ε B : ℝ) : ℝ :=
  (⌊B / ε⌋₊ : ℝ) * ε

/-- The constraints of Program (7) (p. 10) for transition `t` with budget `b = B≥t − B≥t+1`:
`M` is left stochastic, agrees with `M⁰_t` off the malleable set, and `c(M, M⁰_t) ≤ b`. -/
def Prog7Feasible (I : Instance w K) (t : Fin K) (b : ℝ) (M : Matrix (Fin w) (Fin w) ℝ) : Prop :=
  M ∈ colStochastic ℝ (Fin w) ∧ Respects I t M ∧ cost M (I.M0 t) ≤ b

/-- A table of Algorithm 1: `tab t b D` stores `M(B≥t, D_t)` as a full tuple of transitions whose
entries `t, …, K−1` are the chosen matrices and whose entries below `t` are `M⁰`. -/
abbrev Table (w K : ℕ) := ℕ → ℝ → (Fin w → ℝ) → (Fin K → Matrix (Fin w) (Fin w) ℝ)

/-- The distributions Algorithm 1 loops over at (0-based) transition `t`: `{D1}` at the first
layer, the net `S` otherwise. -/
def startSet (I : Instance w K) (S : Finset (Fin w → ℝ)) (t : ℕ) : Finset (Fin w → ℝ) :=
  if t = 0 then {I.D1} else S

/-- `tab` is a run of Algorithm 1 (p. 10) with budget `B`, discretization `ε` and net `S`:
the base entries are `M⁰` (so the suffix product is the identity), and for every transition
`t < K`, every grid budget `b` and every start distribution `D`, the stored entry is
`M(b', D') · M_t` for some grid budget `b' ≤ b`, some `D' ∈ S` and some `M_t` feasible for
Program (7) with budget `b − b'`, and it attains the maximum of `R⊤ M(b'', D'') M'' D` over all
such triples `(b'', D'', M'')`. Ties are broken arbitrarily. -/
def IsAlg1Run (I : Instance w K) (B ε : ℝ) (S : Finset (Fin w → ℝ)) (tab : Table w K) : Prop :=
  (∀ b ∈ budgetGrid ε B, ∀ D, tab K b D = I.M0) ∧
  ∀ t (ht : t < K), ∀ b ∈ budgetGrid ε B, ∀ D ∈ startSet I S t,
    ∃ b' ∈ budgetGrid ε B, b' ≤ b ∧ ∃ D' ∈ S, ∃ Mt, Prog7Feasible I ⟨t, ht⟩ (b - b') Mt ∧
      tab t b D = Function.update (tab (t + 1) b' D') ⟨t, ht⟩ Mt ∧
      ∀ b'' ∈ budgetGrid ε B, b'' ≤ b → ∀ D'' ∈ S, ∀ M'', Prog7Feasible I ⟨t, ht⟩ (b - b'') M'' →
        valueFrom I (Function.update (tab (t + 1) b'' D'') ⟨t, ht⟩ M'') t D ≤
          valueFrom I (tab t b D) t D

/-- The output `M(B^ε, D_1)` of Algorithm 1, as a tuple of transition matrices. -/
noncomputable def alg1Output (I : Instance w K) (B ε : ℝ) (tab : Table w K) :
    Fin K → Matrix (Fin w) (Fin w) ℝ :=
  tab 0 (Beps ε B) I.D1

/-- The number of instances of Program (7) Algorithm 1 solves: one per transition `t`, start
budget `B≥t`, start distribution `D_t`, next budget `B≥t+1 ≤ B≥t` and next distribution
`D_{t+1} ∈ S`. -/
noncomputable def alg1LPCount (I : Instance w K) (B ε : ℝ) (S : Finset (Fin w → ℝ)) : ℕ :=
  ∑ t ∈ Finset.range K, ∑ b ∈ budgetGrid ε B,
    (startSet I S t).card * (((budgetGrid ε B).filter (· ≤ b)).card * S.card)

end PipelineInterv.Welfare


