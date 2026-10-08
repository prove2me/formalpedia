-- Prove2me | Definitions.Def_SDDPConv_Doasa_Run
-- name    : SDDPConv_Doasa_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:14:10.653053+00:00
-- url     : https://prove2.me/theorems/d654335c-0cbf-4ff8-82be-faa58e6a9d8e
-- title:
--   Scenarios, the LP oracle, the induced policy, and runs of DOASA and DOASA-N with CCA (§2–§3, pp. 5–10)
-- statement:
--   This file formalizes the algorithms DOASA (p. 7) and DOASA-N (p. 9), both built on the Cut Calculation Algorithm (CCA, p. 5).
--
--   A **scenario** is a choice of one outcome in each stage $2,\dots,T-1$. A deterministic **LP oracle** `sol` returns, for a stage $t$, a set of cuts and a right-hand side, a stage-$t$ decision; its **specification** says that, for $1\le t\le T-1$, whenever the cut set is finite and contains the initial cut and the feasible region is nonempty and bounded, the decision is the $x_t$-part of an optimal solution of [AP$_t$]. The **policy induced by cut sets** $(\mathcal C_t)$ is the forward pass: $\bar x_1$ is the oracle's solution of [AP$_1$] and, along a scenario, $\bar x_t$ is its solution of [AP$_t$] with right-hand side $\omega_t-B_{t-1}\bar x_{t-1}$, for $2\le t\le T-1$.
--
--   A **run** of the batched scheme consists of cut lists and dual collections $\mathcal D_t$ for every iteration. It starts from the initial cuts and $\mathcal D_t=\emptyset$. Iteration $k$ has a list of forward scenarios and, for each of them and each stage $t$, a backward sample $\Omega^k_t\subseteq\Omega_t$. For every stage $t=2,\dots,T$:
--
--   1. (CCA step 1) for each forward scenario and each sampled outcome $\omega_{ti}\in\Omega^k_t$, an optimal extreme-point dual of [AP$_t^k$] at the scenario's forward state $x^k_{t-1}$ is added to $\mathcal D_t$ (at least one per pair, and nothing else);
--   2. (CCA steps 2–3) if $\mathcal D_t$ is nonempty, then for each forward scenario and **every** outcome $\omega_{ti}\in\Omega_t$ a best dual in $\mathcal D_t$ at $x^k_{t-1}$ is chosen (ties broken arbitrarily), and the resulting cut is appended to the stage-$(t-1)$ cut list.
--
--   **DOASA** has one forward scenario $\omega^k$ per iteration and samples $\Omega^k_t$; **DOASA-N** traverses a fixed list of $N$ scenarios in every iteration, with samples $\Omega^k_{s,t}$ per scenario $s$. The set $\mathcal G^k_t=\{(\beta^j_t,\alpha_{t,j}): j=1,\dots,k-1\}$ of distinct generated cuts (Lemma 1) is the set of entries of the cut list other than the initial one. A policy $\bar x$ is **optimal** if $\bar x_1$ solves [LP1] and, for every scenario and $2\le t\le T-1$, $\bar x_t$ solves [LP$_t(\bar x_{t-1},\omega_t)$].
--
--   **Formalization Note** Iterations are numbered from $0$ in Lean (Lean iteration $k$ is the paper's iteration $k+1$); "eventually" statements are unaffected. The run is a relation, not a function: it holds for every admissible choice of extreme-point duals and of best-dual tie-breaks. The oracle is a function of the cut *set*, so a repeated cut does not change the forward solution; this is the paper's implicit assumption ("all solutions … are the same", p. 10), made explicit. All cuts of iteration $k$ use the cut lists of iteration $k$ (the paper's $j=0,\dots,k-1$), and within an iteration the duals of the whole batch are added before its cuts are computed (relevant only for DOASA-N). If $\mathcal D_t$ is empty, CCA step 2 is undefined in the paper; we add no cut. If some $A_t$ lacks full row rank, the dual regions have no extreme points, CCA step 1 cannot be carried out and no run exists; the paper presupposes extreme-point duals. `IsOptimalPolicy` is applied only to induced policies, which are nonanticipative by construction.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 5, CCA; pp. 7–8, DOASA Steps 0–3; pp. 9–10, DOASA-N Steps 0–3; p. 6, Lemma 1 (𝒢^k_t); p. 11, optimal policy

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts

open Matrix

namespace SDDPConv.Doasa

variable (I : Instance)

/-- A scenario (pp. 7–8): one outcome for each stage `2, …, T − 1`. The coordinate `u` is the
outcome of stage `u + 2`. For `T = 2` there is exactly one (empty) scenario. -/
abbrev Scen := (u : Fin (I.T - 2)) → Fin (I.q (u + 2))

/-- A deterministic LP oracle: given a stage `t`, a set of cuts on `θ_{t+1}` and a right-hand side,
it returns a stage-`t` decision. -/
abbrev Oracle := (t : ℕ) → Set (Cut I t) → (Fin (I.m t) → ℝ) → (Fin (I.n t) → ℝ)

/-- Specification of the oracle: for every stage `1 ≤ t ≤ T − 1`, every finite cut set containing
the initial cut, and every right-hand side whose feasible region is nonempty and bounded, the
returned decision is the `x_t`-part of an optimal solution `(x_t, θ_{t+1})` of [AP_t]. The answer
depends on the cut *set*, so repeated cuts never change it. -/
def OracleSpec (L : ℕ → ℝ) (sol : Oracle I) : Prop :=
  ∀ t, 1 ≤ t → t + 1 ≤ I.T → ∀ (C : Set (Cut I t)) (h : Fin (I.m t) → ℝ),
    initCut I L t ∈ C → C.Finite → (Feas I t h).Nonempty → Bornology.IsBounded (Feas I t h) →
      ∃ θ : ℝ, IsAPOpt I t C h (sol t C h) θ

/-- The policy induced by a family of cut sets `C` (forward pass, p. 7): `x̄_1` solves [AP_1] and,
along the scenario `sc`, `x̄_t` solves [AP_t] with right-hand side `ω_t − B_{t−1} x̄_{t−1}` for
`2 ≤ t ≤ T − 1`. Stage `t` depends only on the outcomes of stages `2, …, t`. Values outside
`1 ≤ t ≤ T − 1` are `0` and never used. -/
noncomputable def policy (sol : Oracle I) (C : (t : ℕ) → Set (Cut I t)) (sc : Scen I) :
    (t : ℕ) → Fin (I.n t) → ℝ
  | 0 => 0
  | 1 => sol 1 (C 1) I.b₁
  | t + 2 =>
    if h : t < I.T - 2 then
      sol (t + 2) (C (t + 2)) (rhs I (t + 1) (policy sol C sc (t + 1)) (sc ⟨t, h⟩))
    else 0

/-- The cut set of iteration `k` at stage `t`: the distinct entries of the cut list. -/
def cutset (cuts : ℕ → (t : ℕ) → List (Cut I t)) (k t : ℕ) : Set (Cut I t) :=
  {a | a ∈ cuts k t}

/-- Lemma 1's `𝒢`: the set of distinct generated cuts on `θ_{s+1}` (the paper's `𝒢^k_{s+1}`), i.e.
the distinct entries of the stage-`s` cut list of iteration `k` other than the initial cut `j = 0`. -/
def G (cuts : ℕ → (t : ℕ) → List (Cut I t)) (k s : ℕ) : Set (Cut I s) :=
  {a | a ∈ (cuts k s).tail}

/-- A run of the batched cutting-plane scheme (DOASA, p. 7, and DOASA-N, p. 9, with CCA, p. 5).
Iteration `k = 0, 1, 2, …` here is the paper's iteration `k + 1`. `cuts k t` is the list of cuts on
`θ_{t+1}` before iteration `k` (position `0` is the initial cut) and `D k t` the collection of dual
solutions of stage `t` before iteration `k`. Iteration `k` has the forward scenario list `F k` and
the backward samples `S k sc t ⊆ Ω_t` for each scenario `sc` of the batch. For each scenario `sc`
the forward states are those of `policy` for the current cut sets. Then, for every stage
`t = s + 1` with `2 ≤ t ≤ T`:

1. (CCA step 1) a set `N` of duals is added to `D_t`; each element is an optimal extreme-point
   dual of [AP_t] (current stage-`t` list) at the forward state `x_s(sc)` and a sampled outcome
   `i ∈ S k sc t` of a scenario `sc` of the batch, and every such pair `(sc, i)` contributes at
   least one;
2. (CCA steps 2–3) if the enlarged collection is nonempty, for every scenario of the batch and
   every outcome `i ∈ Ω_t` a best dual in the collection is chosen at `x_s(sc)` (with the current
   cut heights `α`), and the resulting cut is appended to the stage-`s` list, in the order of the
   batch; if the collection is empty no cut is added.

All lists and collections of other stages stay unchanged; in particular the stage-`T` list is
always `[(0, 0)]`. -/
def IsBatchRun (L : ℕ → ℝ) (sol : Oracle I) (F : ℕ → List (Scen I))
    (S : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t)) : Prop :=
  (∀ t, cuts 0 t = [initCut I L t]) ∧ (∀ t, D 0 t = ∅) ∧ (∀ k, D (k + 1) 0 = D k 0) ∧
  ∀ k s,
    if 1 ≤ s ∧ s + 1 ≤ I.T then
      (∃ N : Set (Dual I (s + 1)), D (k + 1) (s + 1) = D k (s + 1) ∪ N ∧
        (∀ d ∈ N, ∃ sc ∈ F k, ∃ i ∈ S k sc (s + 1),
          IsOptExtDual I (s + 1) (cuts k (s + 1))
            (rhs I s (policy I sol (cutset I cuts k) sc s) i) d) ∧
        (∀ sc ∈ F k, ∀ i ∈ S k sc (s + 1), ∃ d ∈ N,
          IsOptExtDual I (s + 1) (cuts k (s + 1))
            (rhs I s (policy I sol (cutset I cuts k) sc s) i) d)) ∧
      ((D (k + 1) (s + 1) = ∅ ∧ cuts (k + 1) s = cuts k s) ∨
        ((D (k + 1) (s + 1)).Nonempty ∧
          ∃ d : Fin (F k).length → Fin (I.q (s + 1)) → Dual I (s + 1),
            (∀ j i, IsBest I (s + 1) (cuts k (s + 1)) (D (k + 1) (s + 1))
              (rhs I s (policy I sol (cutset I cuts k) ((F k).get j) s) i) (d j i)) ∧
            cuts (k + 1) s = cuts k s ++ List.ofFn (fun j => cutOf I s (cuts k (s + 1)) (d j))))
    else D (k + 1) (s + 1) = D k (s + 1) ∧ cuts (k + 1) s = cuts k s

/-- A DOASA run (p. 7): iteration `k` traverses the single forward scenario `fw k` and uses the
backward sample `Ω^k_t = bw k t` at every stage. -/
def IsDOASARun (L : ℕ → ℝ) (sol : Oracle I) (fw : ℕ → Scen I) (bw : ℕ → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t)) : Prop :=
  IsBatchRun I L sol (fun k => [fw k]) (fun k _ t => bw k t) cuts D

/-- A DOASA-N run (pp. 9–10): every iteration traverses the fixed list `Ls` of `N` scenarios, and
scenario `sc` uses the backward sample `Ω^k_{sc,t} = bw k sc t`. -/
def IsDOASANRun (L : ℕ → ℝ) (sol : Oracle I) (Ls : List (Scen I))
    (bw : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t)) : Prop :=
  IsBatchRun I L sol (fun _ => Ls) bw cuts D

/-- A policy `x̄` (indexed by scenario and stage) is optimal (p. 11): `x̄_1` solves [LP1] and, for every
scenario and every stage `2 ≤ t ≤ T − 1`, `x̄_t` solves [LP_t(x̄_{t−1}, ω_t)], where `ω_t` is the
scenario's stage-`t` outcome. -/
def IsOptimalPolicy (x : Scen I → (t : ℕ) → Fin (I.n t) → ℝ) : Prop :=
  (∀ sc, SolvesLP1 I (x sc 1)) ∧
    ∀ sc (u : ℕ) (hu : u < I.T - 2), SolvesLP I (u + 1) (x sc (u + 1)) (sc ⟨u, hu⟩) (x sc (u + 2))

end SDDPConv.Doasa


