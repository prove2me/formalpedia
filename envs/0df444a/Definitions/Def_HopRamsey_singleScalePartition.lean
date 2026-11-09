-- Prove2me | Definitions.Def_HopRamsey_singleScalePartition
-- name    : HopRamsey_singleScalePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:55.762357+00:00
-- url     : https://prove2.me/theorems/a0ce5f8b-c49f-4d72-b6ac-b738fce569b0
-- title:
--   Algorithm 2: Single-Scale-Partition$(G,X,M,h,\Delta)$
-- statement:
--   Given the active set $X$ (with $n=|X|$), padded set $M\subseteq X$, hop parameter $h$ and scale $\Delta$, Algorithm 2 runs phases $\ell=L,L-1,\dots,1$. With
--
--   $$
--   A_\ell(v,R)=X\cap B^{((k\ell+R)h)}_G\bigl(v,\;r_{\ell-1}+R\,q_\ell\bigr)
--   $$
--
--   taken against the **current** active set, phase $\ell$ repeats the following while some $x\in X$ satisfies $n/\mu_{\ell-1}\le|A_\ell(x,0)|\le|A_\ell(x,k)|\le n/\mu_\ell$:
--
--   1. a center $x_j$ satisfying this condition is chosen;
--   2. an integer $R\in[0,k)$ is drawn from the truncated geometric law with parameter $p_\ell$;
--   3. the cluster $X_j=A_\ell(x_j,R)$ with padded set $M_j=A_\ell(x_j,R-1)\cap M$ is output, $A_\ell(x_j,R+1)$ is removed from $M$, and $A_\ell(x_j,R)$ is removed from $X$.
--
--   After phase $1$, if $X\neq\emptyset$ the last cluster $(X_0,M_0)=(X,M)$ is output. The result is the list of clusters with their padded subsets.
--
--   **Formalization Note** The algorithm is a law (`PMF`) on its output list; the run itself (`sspRun`) keeps, for every carved ball, its phase, center, radius, cluster and padded set. The center is chosen by a center rule, a function of the call's input and its execution so far (footnote 7); the statements of the mission hold for every rule that returns an eligible vertex whenever one exists (`IsValidRule`). Each while loop runs with fuel $|X|+1$, which a valid rule never exhausts since every iteration removes its center.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Algorithm 2, p.16 (PDF p.18); §4.1, pp.14–15 (PDF pp.16–17); footnote 7, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `A_ℓ(v, R) = X ∩ B^{((k·ℓ+R)·h)}_G(v, r_{ℓ−1} + R·q_ℓ)` (Algorithm 2, line 2, p.16, PDF p.18),
computed against the current active set `X`, with distances in the whole graph `G`. The integer
`R` may be `−1` (line 6 uses `A_ℓ(x_j, R − 1)` at `R = 0`); the hop radius `k·ℓ + R` is then still
`≥ 0` since `k, ℓ ≥ 1`, and `Int.toNat` only guards the unused case `k·ℓ + R < 0`. -/
noncomputable def ballA (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (X : Finset V) (ℓ : ℕ)
    (v : V) (R : ℤ) : Finset V :=
  open Classical in
  X.filter fun u =>
    InHopBall G ((((P.k : ℤ) * ℓ + R).toNat) * h) v (P.r Δ (ℓ - 1) + (R : ℝ) * P.q Δ ℓ) u

/-- The density condition of Algorithm 2, line 4 (p.16): `x ∈ X` and
`n/µ_{ℓ−1} ≤ |A_ℓ(x, 0)| ≤ |A_ℓ(x, k)| ≤ n/µ_ℓ`, where `n` is the size of the call's input set. -/
def Eligible (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (n : ℕ) (X : Finset V) (ℓ : ℕ)
    (x : V) : Prop :=
  x ∈ X ∧ (n : ℝ) / (P.mu (ℓ - 1) : ℝ) ≤ ((ballA P G h Δ X ℓ x 0).card : ℝ) ∧
    (ballA P G h Δ X ℓ x 0).card ≤ (ballA P G h Δ X ℓ x P.k).card ∧
    ((ballA P G h Δ X ℓ x P.k).card : ℝ) ≤ (n : ℝ) / (P.mu ℓ : ℝ)

/-- A ball carved by Algorithm 2: its phase `ℓ`, center `x_j`, sampled radius `R`, cluster
`X_j = A_ℓ(x_j, R)` and padded set `M_j = A_ℓ(x_j, R − 1) ∩ M`. -/
structure Carve (V : Type) where
  phase : ℕ
  center : V
  radius : ℕ
  cluster : Finset V
  padded : Finset V

/-- The state of Algorithm 2 during its run: the active set `X`, the padded set `M`, and the balls
carved so far, in order. -/
structure SSPState (V : Type) where
  active : Finset V
  padded : Finset V
  carved : List (Carve V)

/-- A center rule: chooses `x_j` from the call's input `(X, M, ∆)`, the current phase `ℓ` and the
execution of the call so far (current active and padded sets and all balls carved so far, with
their centers and radii). Footnote 7 (p.20, PDF p.22): "For the analysis we fix any rule that
determines x_j as a function of the execution so far". -/
def CenterRule (V : Type) : Type := Finset V → Finset V → ℝ → ℕ → SSPState V → V

/-- A center rule is valid when it returns a vertex satisfying the condition of line 4 whenever
such a vertex exists ("A center x_j is chosen arbitrarily among all active vertices satisfying a
certain density condition", p.15, PDF p.17). -/
def IsValidRule (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V) : Prop :=
  ∀ (X₀ M₀ : Finset V) (Δ : ℝ) (ℓ : ℕ) (s : SSPState V),
    (∃ x, Eligible P G h Δ X₀.card s.active ℓ x) →
      Eligible P G h Δ X₀.card s.active ℓ (rule X₀ M₀ Δ ℓ s)

/-- Lines 6–9 of Algorithm 2 for center `x` and radius `R`: add `(A_ℓ(x,R), A_ℓ(x,R−1) ∩ M)`,
remove `A_ℓ(x, R+1)` from `M` and `A_ℓ(x, R)` from `X` (all balls taken w.r.t. the active set
before the removal). -/
noncomputable def carveStep (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (ℓ : ℕ)
    (s : SSPState V) (x : V) (R : ℕ) : SSPState V :=
  { active := s.active \ ballA P G h Δ s.active ℓ x R
    padded := s.padded \ ballA P G h Δ s.active ℓ x ((R : ℤ) + 1)
    carved := s.carved ++
      [⟨ℓ, x, R, ballA P G h Δ s.active ℓ x R,
        ballA P G h Δ s.active ℓ x ((R : ℤ) - 1) ∩ s.padded⟩] }

/-- The while loop of phase `ℓ` (lines 4–9), run for at most `fuel` iterations. -/
noncomputable def phaseLoop (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V)
    (X₀ M₀ : Finset V) (Δ : ℝ) (ℓ : ℕ) : ℕ → SSPState V → PMF (SSPState V)
  | 0, s => PMF.pure s
  | fuel + 1, s =>
    open Classical in
    if ∃ x, Eligible P G h Δ X₀.card s.active ℓ x then
      (truncGeom (P.p ℓ) P.k).bind fun R =>
        phaseLoop P G h rule X₀ M₀ Δ ℓ fuel (carveStep P G h Δ ℓ s (rule X₀ M₀ Δ ℓ s) R)
    else PMF.pure s

/-- Phases `ℓ, ℓ−1, …, 1` of the for loop (line 3), each while loop with fuel `|X₀| + 1`. -/
noncomputable def phasesFrom (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V)
    (X₀ M₀ : Finset V) (Δ : ℝ) : ℕ → SSPState V → PMF (SSPState V)
  | 0, s => PMF.pure s
  | ℓ + 1, s =>
    (phaseLoop P G h rule X₀ M₀ Δ (ℓ + 1) (X₀.card + 1) s).bind
      (phasesFrom P G h rule X₀ M₀ Δ ℓ)

/-- The run of Algorithm 2 on `(G, X, M, h, ∆)`: the law of its state after phase `1`. -/
noncomputable def sspRun (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V)
    (X M : Finset V) (Δ : ℝ) : PMF (SSPState V) :=
  phasesFrom P G h rule X M Δ P.L ⟨X, M, []⟩

/-- The clusters returned by a final state: the carved balls `(X_j, M_j)` in order, followed by
the last cluster `(X_0, M_0)` = (remaining active set, remaining padded set) if it is nonempty
(lines 10–12). -/
def sspOutput (s : SSPState V) : List (Finset V × Finset V) :=
  s.carved.map (fun c => (c.cluster, c.padded)) ++
    (if s.active.Nonempty then [(s.active, s.padded)] else [])

/-- Algorithm 2, `Single-Scale-Partition(G, X, M, h, ∆)`, as a law on its output list of clusters
with their padded subsets.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), Algorithm 2,
p.16 (PDF p.18), with the parameters of Figure 2 (p.17).

**Formalization Note.**
1. The center `x_j` is chosen by a `CenterRule`; the statements of the mission hold for every
   valid rule (footnote 7, p.20).
2. Each while loop runs with fuel `|X| + 1`. With a valid rule and `∆ ≥ 0` every iteration removes
   its center `x_j ∈ A_ℓ(x_j, 0)` from the active set, so at most `|X|` iterations happen and the
   loop always stops because no eligible center is left, never because the fuel ran out.
3. Radii are drawn from `truncGeom (p_ℓ) k`, the truncated geometric law of line 5, independently
   for every carved ball (`PMF.bind`).
4. `n` in line 4 is the size of the call's input set `X`, fixed at line 1. -/
noncomputable def singleScalePartition (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (X M : Finset V) (Δ : ℝ) : PMF (List (Finset V × Finset V)) :=
  (sspRun P G h rule X M Δ).map sspOutput

end HopRamsey


