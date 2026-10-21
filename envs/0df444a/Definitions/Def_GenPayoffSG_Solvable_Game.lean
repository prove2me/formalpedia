-- Prove2me | Definitions.Def_GenPayoffSG_Solvable_Game
-- name    : GenPayoffSG_Solvable_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:09.17084+00:00
-- url     : https://prove2.me/theorems/3cfaeb50-1946-49d6-bbba-155faade01bc
-- title:
--   Definition 2.1 and §2, pp. 4–7 — stochastic game with bounded Borel payoffs on runs, histories, strategies, P_{h,σ}, E_{h,σ}[f_i], minmax value (1), ε-equilibrium in Γ_h
-- statement:
--   This file sets up the model of §2 of Flesch and Solan together with the two solution notions of §4 that the mission needs.
--
--   **The game (Definition 2.1).** A stochastic game is $\Gamma=(I,S,(A_i)_{i\in I},p,(f_i)_{i\in I})$, where
--   1. $I$ is a nonempty finite set of players;
--   2. $S$ is a nonempty finite or countably infinite set of states;
--   3. $A_i$ is a nonempty finite set of actions of player $i$, the same in every state; $A=\prod_{i\in I}A_i$ is the set of action profiles;
--   4. $p:S\times A\to\Delta(S)$ is the transition function, $p(s'\mid s,a)$ the probability of moving to $s'$;
--   5. $f_i$ is a bounded, Borel-measurable payoff function of player $i$ on the space of runs $(s^1,a^1,s^2,a^2,\dots)$, endowed with the product of the discrete topologies.
--
--   **Histories.** A history in stage $n$ is $h=(s^1,a^1,\dots,s^{n-1},a^{n-1},s^n)$ with $p(s^{k+1}\mid s^k,a^k)>0$ for $k=1,\dots,n-1$; $H$ is the set of all histories, $s_h$ the final state of $h$, and $h'\preceq h$ means that $h$ extends $h'$. The cylinder $C(h)$ is the set of runs whose prefix of the length of $h$ is $h$.
--
--   **Strategies and payoffs.** A (behavior) strategy of player $i$ is a map $\sigma_i:H\to\Delta(A_i)$; a strategy profile is $\sigma=(\sigma_i)_{i\in I}$. At a history $h$ the players draw their actions independently from $\sigma_i(h)$, and the next state is drawn from $p(\cdot\mid s_h,a)$. Together with $h$ this determines (Ionescu-Tulcea) a probability measure $\mathbf P_{h,\sigma}$ on runs that begin with $h$, and player $i$'s expected payoff in the subgame $\Gamma_h$ is
--   $$\mathbf E_{h,\sigma}[f_i]=\int f_i(hr)\,\mathbf P_{h,\sigma}(dr).$$
--   For an initial state $s$, $\mathbf P_{s,\sigma}$ is the case where $h=(s)$.
--
--   **Minmax value (1).** Player $i$'s minmax value in the subgame $\Gamma_h$ is
--   $$\overline v_i(h)=\inf_{\sigma_{-i}\in\Sigma_{-i}}\ \sup_{\sigma_i\in\Sigma_i}\ \mathbf E_{h,\sigma_i,\sigma_{-i}}[f_i].$$
--
--   **Equilibrium (p. 7) and Definitions 4.3, 4.8.** For $\varepsilon\ge 0$, $\sigma$ is an $\varepsilon$-equilibrium in $\Gamma_h$ if $\mathbf E_{h,\sigma}[f_i]\ge\mathbf E_{h,\sigma_i',\sigma_{-i}}[f_i]-\varepsilon$ for every player $i$ and every strategy $\sigma_i'$. The subgame $\Gamma_h$ is **$\varepsilon$-solvable** if it has an $\varepsilon$-equilibrium. A profile $\sigma$ is **minmax $\varepsilon$-acceptable** if $\mathbf E_{h,\sigma}[f_i]\ge\overline v_i(h)-\varepsilon$ for every player $i$ and every history $h\in H$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Coordinates are indexed from $0$: coordinate $0$ is $s^1$ and coordinate $n+1$ is the pair $(a^{n+1},s^{n+2})$. A Lean history `Hist I S A n` (coordinates $0,\dots,n$) is the paper's history of stage $n+1$, and `Preorder.frestrictLe n r` is the prefix $r^{n+1}$. Every coordinate carries the discrete σ-algebra; the product σ-algebra on runs is then the Borel σ-algebra of the product of the countable discrete spaces. The payoffs are defined on all sequences in $(S\times A)^{\mathbb N}$, not only on the closed set $R$ of runs with positive transitions: a bounded Borel function on $R$ extends (e.g. by $0$) to one on the product, and $R$ has full $\mathbf P_{h,\sigma}$-measure from every feasible $h$, so nothing changes. Strategies are defined on all finite sequences, and the predicate `Feasible` singles out the paper's $H$. `playMeasure G σ n h` is `Kernel.traj` of the one-stage kernel started at $h$, so the run it produces begins with $h$ and $\int f_i\,d\mathbf P$ is $\mathbf E_{h,\sigma}[f_i]$; strategies see the full history, which is the paper's continuation strategy in $\Gamma_h$. The $\inf$ and $\sup$ in $\overline v_i$ are real `⨅`/`⨆`; they are the paper's values because the payoffs are bounded (field `f_bdd`) and strategies exist (every $A_i$ is nonempty). The deviation $\sigma_i'$ in an $\varepsilon$-equilibrium ranges over all strategies; its values before $h$ do not affect $\mathbf P_{h,\cdot}$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, pp. 4–7, Definition 2.1, Histories, Subgames, Strategies, Expected payoffs, (1), Equilibrium; p. 11, Definition 4.3; p. 16, Definition 4.8; p. 17, C(h)

import Mathlib

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory Finset

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Coordinate `n` of a play. Coordinate `0` is the initial state `s¹`; coordinate `n + 1` is
the action profile `aⁿ⁺¹` of paper stage `n + 1` followed by the state `sⁿ⁺²` of stage `n + 2`. -/
def Coord (I S : Type) (A : I → Type) : ℕ → Type
  | 0 => S
  | _ + 1 => (∀ i, A i) × S

/-- Every coordinate space carries the discrete σ-algebra. -/
instance instMeasurableSpaceCoord (n : ℕ) : MeasurableSpace (Coord I S A n) := ⊤

instance instDiscreteMeasurableSpaceCoord (n : ℕ) :
    DiscreteMeasurableSpace (Coord I S A n) :=
  ⟨fun _ => trivial⟩

instance instCountableCoord (n : ℕ) : Countable (Coord I S A n) := by
  cases n
  · exact (inferInstance : Countable S)
  · exact (inferInstance : Countable ((∀ i, A i) × S))

/-- The run space `(S × A)^ℕ`, written as the sequence of coordinates. -/
abbrev Run (I S : Type) (A : I → Type) := ∀ n, Coord I S A n

/-- A history of paper stage `n + 1`: the coordinates `0, …, n`, i.e.
`(s¹, a¹, s², …, aⁿ, sⁿ⁺¹)`. -/
abbrev Hist (I S : Type) (A : I → Type) (n : ℕ) := ∀ k : Iic n, Coord I S A k

/-- **Definition 2.1** (multiplayer stochastic game with general payoffs). Finite nonempty
player set `I`, countable nonempty state set `S`, finite nonempty action sets `A i`
(the same in every state), transition `p`, and for every player a bounded measurable payoff on
runs. -/
structure Game (I S : Type) (A : I → Type)
    [Fintype I] [DecidableEq I] [Nonempty I] [Countable S] [Nonempty S]
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)] where
  /-- `p s a s'` is `p(s' | s, a)`. -/
  p : S → (∀ i, A i) → PMF S
  /-- The payoff function `fᵢ` of player `i`. -/
  f : I → Run I S A → ℝ
  f_meas : ∀ i, Measurable (f i)
  f_bdd : ∃ C : ℝ, ∀ i r, |f i r| ≤ C

/-- The state carried by a coordinate. -/
def coordState : (n : ℕ) → Coord I S A n → S
  | 0, c => c
  | _ + 1, c => c.2

/-- The action profile carried by a coordinate `n + 1`. -/
def coordAction {n : ℕ} (c : Coord I S A (n + 1)) : ∀ i, A i := c.1

/-- Coordinate `k ≤ n` of a history of length `n`. -/
def histCoord {n : ℕ} (h : Hist I S A n) (k : ℕ) (hk : k ≤ n) : Coord I S A k :=
  h ⟨k, Finset.mem_Iic.2 hk⟩

/-- The final state `s_h` of a history. -/
def lastState {n : ℕ} (h : Hist I S A n) : S :=
  coordState n (histCoord h n le_rfl)

/-- The history `(h, a, s)` of the next stage. -/
def extend {n : ℕ} (h : Hist I S A n) (a : ∀ i, A i) (s : S) : Hist I S A (n + 1) :=
  fun k =>
    if hk : (k : ℕ) ≤ n then h ⟨k, Finset.mem_Iic.2 hk⟩
    else cast (congrArg (Coord I S A)
        (show n + 1 = (k : ℕ) by have := Finset.mem_Iic.1 k.2; omega))
      (show Coord I S A (n + 1) from (a, s))

/-- The history of stage 1 consisting of the initial state `s` only. -/
def initHist (s : S) : Hist I S A 0 :=
  fun k => cast (congrArg (Coord I S A)
      (show 0 = (k : ℕ) by have := Finset.mem_Iic.1 k.2; omega))
    (show Coord I S A 0 from s)

/-- The paper's set `H` contains only histories all of whose transitions have positive
probability, `p(sᵏ⁺¹ | sᵏ, aᵏ) > 0` (p. 5). -/
def Feasible (G : Game I S A) {n : ℕ} (h : Hist I S A n) : Prop :=
  ∀ k (hk : k < n),
    0 < G.p (coordState k (histCoord h k hk.le))
      (coordAction (histCoord h (k + 1) hk)) (coordState (k + 1) (histCoord h (k + 1) hk))

/-- `Extends h' h` is the paper's `h' ⪯ h`: `h` extends `h'` (possibly `h = h'`). -/
def Extends {m n : ℕ} (h' : Hist I S A m) (h : Hist I S A n) : Prop :=
  ∃ hmn : m ≤ n, ∀ k (hk : k ≤ m), histCoord h' k hk = histCoord h k (hk.trans hmn)

/-- The cylinder `C(h)` of runs whose prefix of the length of `h` is `h`. -/
def cylinder {n : ℕ} (h : Hist I S A n) : Set (Run I S A) :=
  {r | Preorder.frestrictLe n r = h}

/-- A behavior strategy of player `i`: a mixed action at every history. -/
abbrev Strategy (_G : Game I S A) (i : I) := (n : ℕ) → Hist I S A n → PMF (A i)

/-- A strategy profile. -/
abbrev Profile (G : Game I S A) := ∀ i, Strategy G i

/-- The product distribution of the players' independent mixed actions at `h`. -/
noncomputable def actionPMF (G : Game I S A) (σ : Profile G) (n : ℕ)
    (h : Hist I S A n) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun a => ∏ i, σ i n h (a i)) (by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun i _ => by
      have h1 := PMF.tsum_coe (σ i n h)
      rwa [tsum_fintype] at h1))

/-- One stage of play at `h`: draw the action profile, then the next state. -/
noncomputable def stepPMF (G : Game I S A) (σ : Profile G) (n : ℕ)
    (h : Hist I S A n) : PMF (Coord I S A (n + 1)) :=
  (actionPMF G σ n h).bind
    (fun a => (G.p (lastState h) a).map (fun s => (show Coord I S A (n + 1) from (a, s))))

/-- The one-stage transition kernel induced by `σ`. -/
noncomputable def stepKernel (G : Game I S A) (σ : Profile G) (n : ℕ) :
    Kernel (Hist I S A n) (Coord I S A (n + 1)) :=
  Kernel.ofFunOfCountable (fun h => (stepPMF G σ n h).toMeasure)

instance instIsMarkovKernelStepKernel (G : Game I S A) (σ : Profile G) (n : ℕ) :
    IsMarkovKernel (stepKernel G σ n) :=
  ⟨fun h => by
    change IsProbabilityMeasure ((stepPMF G σ n h).toMeasure)
    infer_instance⟩

/-- `P_{h,σ}`: the law of the run when the play has followed `h` and continues under `σ`
(Ionescu-Tulcea). The run begins with `h` itself, so integrating `fᵢ` against it is
`E_{h,σ}[fᵢ] = ∫ fᵢ(hr) P_{h,σ}(dr)`. -/
noncomputable def playMeasure (G : Game I S A) (σ : Profile G) (n : ℕ)
    (h : Hist I S A n) : Measure (Run I S A) :=
  Kernel.traj (stepKernel G σ) n h

/-- Player `i`'s expected payoff `E_{h,σ}[fᵢ]` in the subgame `Γ_h`. -/
noncomputable def payoff (G : Game I S A) (σ : Profile G) (n : ℕ)
    (h : Hist I S A n) (i : I) : ℝ :=
  ∫ r, G.f i r ∂(playMeasure G σ n h)

/-- (1): player `i`'s minmax value `v̄ᵢ(h)` in the subgame `Γ_h`. The opponents' part of
`τ` is `σ₋ᵢ`; the `i`-th component of `τ` is overwritten by `σᵢ`. -/
noncomputable def minmax (G : Game I S A) (i : I) (n : ℕ) (h : Hist I S A n) : ℝ :=
  ⨅ τ : Profile G, ⨆ σi : Strategy G i, payoff G (Function.update τ i σi) n h i

/-- `σ` is an `ε`-equilibrium in the subgame `Γ_h` (p. 7, for the initial state `s_h`). -/
def IsEpsEquilibriumAt (G : Game I S A) (ε : ℝ) (σ : Profile G)
    (n : ℕ) (h : Hist I S A n) : Prop :=
  ∀ i (σi : Strategy G i), payoff G (Function.update σ i σi) n h i ≤ payoff G σ n h i + ε

/-- **Definition 4.8**: the subgame `Γ_h` is `ε`-solvable. -/
def IsEpsSolvable (G : Game I S A) (ε : ℝ) (n : ℕ) (h : Hist I S A n) : Prop :=
  ∃ σ : Profile G, IsEpsEquilibriumAt G ε σ n h

/-- **Definition 4.3**: `σ` is minmax `ε`-acceptable. -/
def IsMinmaxAcceptable (G : Game I S A) (ε : ℝ) (σ : Profile G) : Prop :=
  ∀ i n (h : Hist I S A n), Feasible G h → minmax G i n h - ε ≤ payoff G σ n h i

end GenPayoffSG.Solvable


