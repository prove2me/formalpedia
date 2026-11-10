-- Prove2me | Definitions.Def_LoadBalMatch_Main_Algorithm4
-- name    : LoadBalMatch_Main_Algorithm4
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:51.683206+00:00
-- url     : https://prove2.me/theorems/e71f069f-4afb-44b6-8a04-e6121790fa3d
-- title:
--   Algorithm 4 as a randomized process with arbitrary admissible choices; high- and low-mass iterations (Algorithm 4, Definition 8.2)
-- statement:
--   Fix a graph $G$ on $V$ with $n=|V|$, edge set $E$, and an edge stream $\sigma$ of $G$. **Algorithm 4** (p. 46) keeps a subgraph $H$, a balanced fractional matching $x$ on $H$ and probabilities $p_e$:
--
--   1. $H^{(1)}$ is a maximal matching of $G$, $x^{(1)}$ a balanced fractional matching on $H^{(1)}$, and $p^{(1)}_e=1/n$ for $e\in E$.
--   2. In iteration $t$: $M^{(t)}$ is a matching of $G$ whose weight (eq. (36), for $H^{(t)},x^{(t)}$) is at least $1/3$ of the maximum weight of a matching of $G$; $T^{(t)}$ is a spanning forest of $\widehat G_{H^{(t)}}$; $R^{(t)}\subseteq E$ contains each $e$ independently with probability $\min\{1,p^{(t)}_e\}$; $p^{(t+1)}_e=2p^{(t)}_e$ if $e$ violates $x^{(t)}$ and $p^{(t+1)}_e=p^{(t)}_e$ otherwise; the stabilizing pass over $\sigma$ is applied to $H^{(t)}\cup M^{(t)}\cup T^{(t)}\cup R^{(t)}$; $x^{(t+1)}$ is a balanced fractional matching on the result, and $H^{(t+1)}=\operatorname{supp}(x^{(t+1)})$.
--
--   The only randomness is in the samples $R^{(t)}$; every other choice may be any choice the algorithm allows and may depend on the past. For a balanced fractional matching $x^\star$ of $G$ and $\delta=\sqrt{\log_2 n}\cdot\varepsilon$ (Definition 8.2), iteration $t$ is **high-mass** if
--   $$\sum_{e\in F(x^{(t)})}x^\star_e\ \ge\ \delta\cdot\mu(G),$$
--   and **low-mass** otherwise; $N(t)$ is the number of low-mass iterations among the first $t$.
--
--   **Formalization Note.** A history `hs = [R⁽¹⁾, …, R⁽ᵏ⁾]` determines the state at the start of iteration `k+1`. `Alg4Choices` holds `H⁽¹⁾`, `x⁽¹⁾` and the rules `chooseM`, `chooseT` (functions of the history before the sample) and `chooseX` (function of the history including the new sample); `Admissible G σ` requires every choice, for every history, to be one the algorithm allows. `xAt hs`, `HAt hs` are $x^{(k+1)}$, $H^{(k+1)}$ ($H^{(1)}$, then $\operatorname{supp}(x^{(t)})$); `pAt G hs` is $p^{(k+1)}$ in closed form, $p_e=\frac1n2^{\#\{s\le k:\,e\text{ violates }x^{(s)}\}}$ on $E$ and $0$ off $E$; `qAt` is $\min\{1,p\}$. `InSupport G hs`: every sample in `hs` has positive probability given its past. `probAfter G P k A hs`: the probability, over the next `k` samples, that the history satisfies `A`. `highCount`, `lowCount` count high- and low-mass iterations among iterations $1,\dots,|hs|$ for the reference vector $x^\star$; `delta n ε` $=\sqrt{\log_2 n}\cdot\varepsilon$. The algorithm's "succinct" requirement on $x^{(t+1)}$ is not imposed: the lemmas hold for every balanced choice.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 46, Algorithm 4 and Definition 8.2; p. 45, §8.2 (notation)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_Stable
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
import Definitions.Def_LoadBalMatch_Main_Violation
import Definitions.Def_LoadBalMatch_Main_Sampling

/-!
# Algorithm 4 as a randomized process; high-mass and low-mass iterations (Definition 8.2)

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), Algorithm 4, p. 46:
1. Initialize `H` to be a maximal matching and `x` a balanced fractional matching on `H`; `p_e = 1/n`.
2. For `1026 √log n / ε` iterations:
   (a) `M`: a (1/3)-approximate maximum weight matching of `G` for the weights `w` of eq. (36);
   (b) `T`: a spanning forest of `Ĝ_H`;
   (c) sample each `e ∈ E` independently with probability `min{1, p_e}`; for every `e` that violates
       `x`, `p_e ← 2 p_e`; `R` is the set of sampled edges;
   (d) `H ← H ∪ M ∪ T ∪ R`;
   (e) the stabilizing pass;
   (f) `x`: a succinct balanced fractional matching on `H`; `H ← supp(x)`.
§8.2 notation, p. 45: `H⁽ᵗ⁾, R⁽ᵗ⁾, M⁽ᵗ⁾, T⁽ᵗ⁾`, `p⁽ᵗ⁾` at the start of iteration `t`, `x⁽ᵗ⁾`.
Definition 8.2, p. 46: `δ = √log(n) · ε`; iteration `t` is high-mass if
`Σ_{e∈F(x⁽ᵗ⁾)} x⋆_e ≥ δ · µ(G)`, low-mass otherwise.

Formalization Note.
* The only randomness is the samples `R⁽¹⁾, R⁽²⁾, …`. A history `hs = [R⁽¹⁾, …, R⁽ᵏ⁾]` determines
  the state at the start of iteration `k + 1`. All other choices (`H⁽¹⁾`, `x⁽¹⁾`, and in every
  iteration `M⁽ᵗ⁾`, `T⁽ᵗ⁾`, `x⁽ᵗ⁺¹⁾`) are made by an arbitrary rule `Alg4Choices` that may depend on
  the history; `Admissible` requires each choice to be one the algorithm allows. Statements quantify
  over every admissible rule.
* `xAt hs` is `x⁽ᵏ⁺¹⁾` and `HAt hs` is `H⁽ᵏ⁺¹⁾` (`H⁽¹⁾` the initial maximal matching, later
  `supp(x⁽ᵗ⁾)`); `pAt G hs` is `p⁽ᵏ⁺¹⁾` in closed form: `p⁽¹⁾_e = 1/n` on `E`, doubled once for each
  earlier iteration `s` in which `e` violates `x⁽ˢ⁾` (with respect to `H⁽ˢ⁾`). `n = |V|`.
* `x⁽ᵗ⁺¹⁾` is any balanced fractional matching on the stabilized graph; succinctness is not
  required (the lemmas below hold for every balanced choice).
* `InSupport G P hs`: every sample in `hs` has positive probability given the past (in particular
  `R⁽ˢ⁾ ⊆ E` and `R⁽ˢ⁾` contains every edge with `p⁽ˢ⁾_e ≥ 1`).
* `probAfter G P k A hs`: the probability, over the next `k` samples drawn from history `hs`, that
  the resulting history satisfies `A`.
* `highCount G P z δ hs` and `lowCount G P z δ hs`: the number of high-mass and of low-mass iterations among iterations
  `1, …, |hs|`, for the reference vector `z = x⋆`.
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A choice rule for the non-random steps of Algorithm 4, as functions of the history of samples. -/
structure Alg4Choices (V : Type*) where
  /-- `H⁽¹⁾`. -/
  H1 : SimpleGraph V
  /-- `x⁽¹⁾`. -/
  x1 : Sym2 V → ℝ
  /-- `M⁽ᵗ⁾` after the history `[R⁽¹⁾, …, R⁽ᵗ⁻¹⁾]`. -/
  chooseM : List (Finset (Sym2 V)) → Finset (Sym2 V)
  /-- `T⁽ᵗ⁾` after the history `[R⁽¹⁾, …, R⁽ᵗ⁻¹⁾]`. -/
  chooseT : List (Finset (Sym2 V)) → Finset (Sym2 V)
  /-- `x⁽ᵗ⁺¹⁾` after the history `[R⁽¹⁾, …, R⁽ᵗ⁾]`. -/
  chooseX : List (Finset (Sym2 V)) → Sym2 V → ℝ

namespace Alg4Choices

/-- `x⁽ᵏ⁺¹⁾` after the history `hs` of length `k`. -/
def xAt (P : Alg4Choices V) (hs : List (Finset (Sym2 V))) : Sym2 V → ℝ :=
  match hs with
  | [] => P.x1
  | _ :: _ => P.chooseX hs

/-- `H⁽ᵏ⁺¹⁾` after the history `hs` of length `k`: `H⁽¹⁾`, and `supp(x⁽ᵏ⁺¹⁾)` for `k ≥ 1`. -/
def HAt (P : Alg4Choices V) (hs : List (Finset (Sym2 V))) : SimpleGraph V :=
  match hs with
  | [] => P.H1
  | _ :: _ => supportGraph (P.chooseX hs)

/-- `p⁽ᵏ⁺¹⁾_e = (1/n) · 2^{#\{s ≤ k : e violates x⁽ˢ⁾\}}` for `e ∈ E`, and `0` off `E`. -/
noncomputable def pAt (G : SimpleGraph V) (P : Alg4Choices V) (hs : List (Finset (Sym2 V)))
    (e : Sym2 V) : ℝ := by
  classical
  exact (if e ∈ G.edgeSet then 1 / (Fintype.card V : ℝ) else 0) *
    2 ^ ((Finset.range hs.length).filter
      (fun s => IsViolating G (P.HAt (hs.take s)) (P.xAt (hs.take s)) e)).card

/-- The sampling probabilities `min{1, p_e}` after the history `hs`. -/
noncomputable def qAt (G : SimpleGraph V) (P : Alg4Choices V) (hs : List (Finset (Sym2 V)))
    (e : Sym2 V) : ℝ :=
  min 1 (P.pAt G hs e)

/-- Every choice of the rule is one Algorithm 4 allows, for the graph `G` and stream order `σ`. -/
def Admissible (G : SimpleGraph V) (σ : List (Sym2 V)) (P : Alg4Choices V) : Prop :=
  (∃ M₀, IsMaximalMatching G M₀ ∧ P.H1 = SimpleGraph.fromEdgeSet ↑M₀) ∧
  IsBalanced P.H1 P.x1 ∧
  ∀ hs : List (Finset (Sym2 V)),
    (IsMatchingIn G (P.chooseM hs) ∧
      ∀ M', IsMatchingIn G M' →
        ∑ e ∈ M', extWeight (P.HAt hs) (P.xAt hs) e ≤
          3 * ∑ e ∈ P.chooseM hs, extWeight (P.HAt hs) (P.xAt hs) e) ∧
    IsContractedSpanningForest G (P.HAt hs) (P.chooseT hs) ∧
    ∀ R : Finset (Sym2 V),
      IsBalanced (stabilize (addEdges (P.HAt hs) ↑(P.chooseM hs ∪ P.chooseT hs ∪ R)) σ)
        (P.chooseX (hs ++ [R]))

/-- Every sample of the history has positive probability given the past. -/
def InSupport (G : SimpleGraph V) (P : Alg4Choices V) (hs : List (Finset (Sym2 V))) : Prop :=
  ∀ (s : ℕ) (h : s < hs.length), 0 < sampleProb G (P.qAt G (hs.take s)) (hs[s]'h)

/-- The probability, over the next `k` samples drawn from the history `hs`, of the event `A`
on the resulting history. -/
noncomputable def probAfter (G : SimpleGraph V) (P : Alg4Choices V) :
    ℕ → (List (Finset (Sym2 V)) → Prop) → List (Finset (Sym2 V)) → ℝ
  | 0, A, hs => by classical exact if A hs then 1 else 0
  | k + 1, A, hs => ∑ R, sampleProb G (P.qAt G hs) R * probAfter G P k A (hs ++ [R])

/-- Definition 8.2: the iteration whose state follows the history `hs` is high-mass:
`Σ_{e ∈ F(x)} z_e ≥ δ · µ(G)`. -/
def IsHighMass (G : SimpleGraph V) (P : Alg4Choices V) (z : Sym2 V → ℝ) (δ : ℝ)
    (hs : List (Finset (Sym2 V))) : Prop :=
  δ * (matchingNumber G : ℝ) ≤ violMass G (P.HAt hs) (P.xAt hs) z

/-- The number of high-mass iterations among iterations `1, …, |hs|`. -/
noncomputable def highCount (G : SimpleGraph V) (P : Alg4Choices V) (z : Sym2 V → ℝ) (δ : ℝ)
    (hs : List (Finset (Sym2 V))) : ℕ := by
  classical
  exact ((Finset.range hs.length).filter (fun s => IsHighMass G P z δ (hs.take s))).card

/-- `N(t)`: the number of low-mass iterations among iterations `1, …, |hs|`. -/
noncomputable def lowCount (G : SimpleGraph V) (P : Alg4Choices V) (z : Sym2 V → ℝ) (δ : ℝ)
    (hs : List (Finset (Sym2 V))) : ℕ := by
  classical
  exact ((Finset.range hs.length).filter (fun s => ¬ IsHighMass G P z δ (hs.take s))).card

end Alg4Choices

/-- `δ = √(log₂ n) · ε` (Definition 8.2). -/
noncomputable def delta (n : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt (Real.logb 2 n) * ε

end LoadBalMatch.Main


