-- Prove2me | Definitions.Def_SemiStreamMWM_Algorithms
-- name    : SemiStreamMWM_Algorithms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:53.78159+00:00
-- url     : https://prove2.me/theorems/6f215569-3315-4976-86bd-60a3b353ba86
-- title:
--   Definitions 2.3, 2.4 and Algorithms 2.1, 2.2 — oracles and phased optimization as trace relations
-- statement:
--   **Definition 2.3.** Given $x\in\mathcal P_{G,\delta}$, $t$ and a direction $d$, an admissible answer of $\mathtt{Eval}(x,t,d)$ is any $v$ with $|v-\nabla F_t(x)^\top d|\le\delta\mu_w(G)/1024$.
--
--   **Definition 2.4.** For an oracle constant $c\ge1$, an admissible answer of $\mathtt{Step}(x,t)$ is a direction $d$ with
--
--   1. $x+\eta d\in\mathcal P_{G,\delta}$, $\|Ad\|_\infty\le1$ and $\|Ad\|_1\le4\mu(G)$;
--   2. $\nabla F_t(x)^\top d\le\frac1c\min_{d':\,x+d'\in\mathcal P_G}\nabla F_t(x)^\top d'+c\,\delta\mu_w(G)$.
--
--   **Algorithm 2.1** (fixed $t$, with $\mu_w(G)/4\le L\le\mu_w(G)$) repeats: if $\mathtt{Eval}(x,t,x)\ge3\delta L/4$ then $d\leftarrow-x$; otherwise $d\leftarrow\mathtt{Step}(x,t)$ and, if $\mathtt{Eval}(x,t,d)>-\delta L/8$, return $x$; then $x\leftarrow x+\eta d$. One pass through the loop is an iteration. **Algorithm 2.2** starts at $x=0$, $t=1/(32\log W)$, and while $t\ge\varepsilon/(C\log W)$ replaces $x$ by the output of Algorithm 2.1 on $(x,t,L)$ and halves $t$.
--
--   The lemmas about the algorithms are statements about every run, so they hold for every implementation of the oracles.
--
--   **Formalization Note** Every oracle call may receive any admissible answer, independently of the other calls. A run of Algorithm 2.1 is a list $x^{(0)},\dots,x^{(k)}$ of iterates related by non-returning iterations; it returns $x^{(k)}$ if the returning iteration is admissible there. A run of Algorithm 2.2 is a list of such runs, one per phase $t_j=2^{-j}/(32\log W)$, for exactly the $j$ with $t_j\ge\varepsilon/(C\log W)$. The minimum in Definition 2.4 is attained, so it is stated against every $d'$ with $x+d'\in\mathcal P_G$.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §2.1 pp.10–11 (Definitions 2.3, 2.4, Algorithm 2.1); §2.2 p.12 (Algorithm 2.2)

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential

open Classical

namespace SemiStreamMWM

/-! # The oracles (Definitions 2.3, 2.4) and Algorithms 2.1, 2.2 as trace relations

J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §2.1 pp.10–11 (Definition 2.3,
Definition 2.4, Algorithm 2.1, "We call one pass through the loop in Algorithm 2.1 an iteration"),
§2.2 p.12 (Algorithm 2.2).

**Formalization Note.** The algorithms are relations on traces in which every oracle answer is
chosen adversarially among the answers Definitions 2.3 and 2.4 allow, separately at every call: a
statement about every trace holds for every oracle implementation. One loop pass of Algorithm 2.1
that does not return is `Alg21Step` (line 2's answer at least `3δL/4` and `d = −x`; or line 2's
answer below `3δL/4`, `d` a `Step` answer, and line 6's answer at most `−δL/8`), followed by
`x ← x + ηd`. The pass that returns is `Alg21Return`. A run of Algorithm 2.1 from `x⁽⁰⁾` is a list
`[x⁽⁰⁾, x⁽¹⁾, …, x⁽ᵏ⁾]` with consecutive entries related by `Alg21Step`; it has used `k` iterations
and, if `Alg21Return` holds at `x⁽ᵏ⁾`, returns `x⁽ᵏ⁾` in its `(k+1)`-st. In Definition 2.4 the
minimum over `{d′ : x + d′ ∈ P_G}` is attained (`P_G` is compact and nonempty), so for `c > 0`
"`g^⊤d ≤ (1/c) min g^⊤d′ + cδµ_w`" is the same as the bound against every such `d′`. Algorithm 2.2
runs phases `t_j = 2^{−j}/(32 log W)` for exactly the `j` with `t_j ≥ ε/(C log W)` (the loop
condition; `t_j` decreases), the first from `x = 0`, each from the previous phase's output. -/

variable {V : Type*} [Fintype V]

/-- Definition 2.3: `v` is an admissible answer of `Eval(x, t, d)`:
`|v − ∇F_t(x)^⊤d| ≤ δµ_w(G)/1024`. -/
def EvalOK (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ) (x d : G.edgeSet → ℝ) (v : ℝ) :
    Prop :=
  |v - wdot G (gradF G w W t x) d| ≤ delta W t * mwm G w / 1024

/-- Definition 2.4: `d` is an admissible answer of `Step(x, t)` for the oracle constant `c`:
1. `x + ηd ∈ P_{G,δ}`, `‖Ad‖_∞ ≤ 1` and `‖Ad‖_1 ≤ 4µ(G)`;
2. `∇F_t(x)^⊤d ≤ (1/c) min_{d′ : x+d′∈P_G} ∇F_t(x)^⊤d′ + cδµ_w(G)`. -/
def StepOK (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c t : ℝ) (x d : G.edgeSet → ℝ) : Prop :=
  x + eta W t • d ∈ truncPolytope G (delta W t) ∧ (∀ v, |deg G d v| ≤ 1) ∧
    ∑ v, |deg G d v| ≤ 4 * (mcm G : ℝ) ∧
    ∀ d' : G.edgeSet → ℝ, x + d' ∈ matchingPolytope G →
      wdot G (gradF G w W t x) d ≤
        (1 / c) * wdot G (gradF G w W t x) d' + c * delta W t * mwm G w

/-- One iteration of Algorithm 2.1 that does not return, from `x` to `x'`. -/
def Alg21Step (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c t L : ℝ)
    (x x' : G.edgeSet → ℝ) : Prop :=
  ((∃ v, EvalOK G w W t x x v ∧ 3 * delta W t * L / 4 ≤ v) ∧ x' = x + eta W t • (-x)) ∨
  ((∃ v, EvalOK G w W t x x v ∧ v < 3 * delta W t * L / 4) ∧
    ∃ d, StepOK G w W c t x d ∧ (∃ v', EvalOK G w W t x d v' ∧ v' ≤ -(delta W t * L / 8)) ∧
      x' = x + eta W t • d)

/-- The iteration of Algorithm 2.1 that returns `x` (lines 5–7). -/
def Alg21Return (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c t L : ℝ) (x : G.edgeSet → ℝ) :
    Prop :=
  (∃ v, EvalOK G w W t x x v ∧ v < 3 * delta W t * L / 4) ∧
    ∃ d, StepOK G w W c t x d ∧ ∃ v', EvalOK G w W t x d v' ∧ -(delta W t * L / 8) < v'

/-- The parameter of the `j`-th phase of Algorithm 2.2: `t_j = 2^{−j}/(32 log W)`. -/
noncomputable def phaseT (W : ℕ) (j : ℕ) : ℝ := 1 / (32 * logW W) / 2 ^ j

/-- Algorithm 2.2 runs exactly `N` phases: `t_j ≥ ε/(C log W)` for `j < N`, and not for `j = N`. -/
def IsPhaseCount (W : ℕ) (C ε : ℝ) (N : ℕ) : Prop :=
  (∀ j < N, ε / (C * logW W) ≤ phaseT W j) ∧ phaseT W N < ε / (C * logW W)

/-- A prefix of a run of Algorithm 2.2 that has entered `J ≤ N` phases: `tr j` is the trace of
Algorithm 2.1 in phase `j`, the first starts at `0`, every phase before the last entered one has
returned, and each phase starts at the previous phase's output. -/
def Alg22Prefix (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c C ε L : ℝ) (N J : ℕ)
    (tr : ℕ → List (G.edgeSet → ℝ)) : Prop :=
  IsPhaseCount W C ε N ∧ J ≤ N ∧
    (∀ j < J, tr j ≠ [] ∧ (tr j).IsChain (Alg21Step G w W c (phaseT W j) L)) ∧
    (0 < J → (tr 0).head? = some 0) ∧
    ∀ j, j + 1 < J →
      (∃ y, (tr j).getLast? = some y ∧ Alg21Return G w W c (phaseT W j) L y) ∧
        (tr (j + 1)).head? = (tr j).getLast?

/-- A complete run of Algorithm 2.2 (with `L` from line 1) that returns `x` (line 7). -/
def Alg22Output (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (c C ε L : ℝ) (N : ℕ)
    (tr : ℕ → List (G.edgeSet → ℝ)) (x : G.edgeSet → ℝ) : Prop :=
  Alg22Prefix G w W c C ε L N N tr ∧
    ((N = 0 ∧ x = 0) ∨
      (0 < N ∧ (tr (N - 1)).getLast? = some x ∧ Alg21Return G w W c (phaseT W (N - 1)) L x))

end SemiStreamMWM


