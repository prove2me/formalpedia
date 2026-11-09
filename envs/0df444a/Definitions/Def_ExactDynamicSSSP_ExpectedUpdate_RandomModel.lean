-- Prove2me | Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel
-- name    : ExactDynamicSSSP_ExpectedUpdate_RandomModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:26.648196+00:00
-- url     : https://prove2.me/theorems/8b1e759b-eaae-49a4-9e2f-e946e64d3521
-- title:
--   §6 — the random fixed-edge-count model, random updates, expected work and the cost functionals
-- statement:
--   This file fixes the probability model of §6.
--
--   **Graph law.** For $n\ge 3$ let $N=n(n-1)$. $\mathcal G_{n,j}$ is the uniform law on the $j$-element subsets of ordered pairs $(u,v)$ with $u\ne v$ (no loops, no parallel arcs, opposite orientations distinct). Conditional on the arc set, the weights are independent $U[0,C)$ variables, $C>0$. In the sample space a $U[0,C)$ weight is drawn for every ordered pair and the graph uses those of its present arcs.
--
--   **Updates.** The operation types are fixed in advance; only valid operations are used ($m>0$ for deletion and resampling, $m<N$ for insertion). A deletion removes a uniformly chosen existing arc; an insertion adds a uniformly chosen missing arc with a fresh independent $U[0,C)$ weight; a resampling replaces the weight of a uniformly chosen existing arc by a fresh independent sample. The initial graph has law $\mathcal G_{n,m_0}$; the data structure is initialized on it with a source $s$ fixed independently of the graph and receives every update. $T$ is the actual work of the $t$-th update, and $\mathbb ET$ its expectation over the initial graph, the weights and all update choices, without any conditioning.
--
--   **Functionals.** With $H_x$ the hop count of the certified shortest path ($H_s=0$, $H_x=0$ if unreachable), $H_*=\max_xH_x$, $\mathbb E_j$ the expectation under $\mathcal G_{n,j}$,
--   $$\mathcal C_{n,j}=\frac1j\,\mathbb E_j\sum_x\bigl(D^+_x+D^-_x+\log n\bigr)H_x,\qquad J_m=\{m,m+1\}\cap\{1,\dots,N\},$$
--   $A_j=\mathbb E_j\sum_xH_x$ with $A_0=0$, $F_j=\mathbb E_j\sum_xL_x$ with $L_x$ the unweighted distance ($0$ if unreachable), $R$ the number of vertices reachable from $s$ (including $s$) and $\mathcal R_s$ the largest finite unweighted distance from $s$. $\mathbb E_e$ averages over a uniformly chosen existing arc.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals of $[0,\infty]$-valued functions, so no integrability convention can make a bound vacuous. The uniform choice of an arc is realized by an independent $U[0,1)$ variable selecting the element of index $\lfloor U k\rfloor$ in a fixed enumeration of the $k$ candidates.
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), §6, PDF pp.7–8 = printed pp.7–8 (model, eqs. (4), (6), J_m); §6.2, PDF p.9 (A_j); PDF p.9 (L_x, F_j); §6.3, PDF p.10 (R); Lemma 6.7, PDF p.11 (ℛ_s)

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Algorithm

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

noncomputable section

/-! # The random update model and the cost functionals of Section 6

Liang–Chen–Zhang, STOC 2027 submission #223, §6 (PDF pp. 7–12 = printed pp. 7–12).

* `gnm n C j` is the law `𝒢_{n,j}` with independent `U[0, C)` weights: a uniformly random
  `j`-element set of ordered pairs `(u, v)`, `u ≠ v`, together with a weight vector of
  independent `U[0, C)` coordinates for **all** `n²` ordered pairs (including the unused
  diagonal coordinates), of which only the
  coordinates of present arcs are used by the graph. Conditional on the arc set, the weights
  of the present arcs are therefore independent `U[0, C)`.
* The update process starts from `gnm n C m₀`; at step `t` an operation of the fixed type
  `ops t` is applied: a deletion removes a uniformly chosen existing arc, an insertion adds a
  uniformly chosen missing arc with a fresh `U[0, C)` weight, a resampling gives a uniformly
  chosen existing arc a fresh `U[0, C)` weight. The uniform choices are realized from
  independent `U[0, 1)` variables (`pick`), the fresh weights from independent `U[0, C)`
  variables. The data structure is initialized on the initial graph and receives every
  update; `updateWork` is the actual work of the `t`-th update and `expectedWork` its
  expectation over the initial graph, its weights and all update choices. -/

variable {n : ℕ}

/-- `N = n(n − 1)`, the number of ordered pairs of distinct vertices. -/
def numPairs (n : ℕ) : ℕ := n * (n - 1)

/-- The ordered pairs `(u, v)` with `u ≠ v`. -/
def offDiagPairs (n : ℕ) : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n)).offDiag

/-- A weighted-graph sample: an arc set and a weight for every ordered pair. -/
abbrev Sample (n : ℕ) := Finset (Fin n × Fin n) × (Fin n × Fin n → ℝ)

/-- The weighted digraph of a sample: the arcs of `g.1` other than loops, with the weights
`g.2` (truncated at `0`, which changes nothing on the support of `U[0, C)`). -/
def Sample.graph (g : Sample n) : WDigraph n where
  wt x y := if (x, y) ∈ g.1 ∧ x ≠ y then some (g.2 (x, y)).toNNReal else none
  loopless x := by
    split_ifs with h
    · exact absurd rfl h.2
    · rfl

/-- The continuous uniform law `U[0, C)`. -/
def unifIco (C : ℝ) : Measure ℝ := (volume : Measure ℝ)[|Set.Ico 0 C]

/-- The `j`-element sets of ordered pairs of distinct vertices. -/
def arcSetsOfSize (n j : ℕ) : Set (Finset (Fin n × Fin n)) :=
  {S | S ⊆ offDiagPairs n ∧ S.card = j}

/-- The law `𝒢_{n,j}` of the uniform fixed-edge-count digraph, with independent `U[0, C)`
weights. -/
def gnm (n : ℕ) (C : ℝ) (j : ℕ) : Measure (Sample n) :=
  (uniformOn (arcSetsOfSize n j)).prod (Measure.pi fun _ => unifIco C)

/-! ## The update process -/

/-- The three random update types. -/
inductive UpdKind
  | delete
  | insert
  | resample
  deriving DecidableEq

/-- The edge count before step `t` for the fixed operation-type sequence `ops`. -/
def edgeCount (m₀ : ℕ) (ops : ℕ → UpdKind) : ℕ → ℕ
  | 0 => m₀
  | t + 1 =>
    match ops t with
    | .delete => edgeCount m₀ ops t - 1
    | .insert => edgeCount m₀ ops t + 1
    | .resample => edgeCount m₀ ops t

/-- Only valid operations: `m₀ ≤ N`, and before each of the steps `0, …, T − 1` a deletion or
resampling has `m > 0` and an insertion has `m < N`. -/
def ValidOps (n m₀ : ℕ) (ops : ℕ → UpdKind) (T : ℕ) : Prop :=
  m₀ ≤ numPairs n ∧ ∀ t < T,
    (ops t = .insert → edgeCount m₀ ops t < numPairs n) ∧
    (ops t ≠ .insert → 0 < edgeCount m₀ ops t)

/-- Sample space of the first `H` updates: the initial weighted graph, the fresh weights
`ν_t`, and the selection variables `U_t`. -/
abbrev Omega (n H : ℕ) := Sample n × (Fin H → ℝ) × (Fin H → ℝ)

/-- The law of the initial graph and of the first `H` update choices: `𝒢_{n,m₀}` with
independent `U[0,C)` weights, fresh weights i.i.d. `U[0, C)`, selection variables i.i.d.
`U[0, 1)`, all independent. -/
def procMeasure (n : ℕ) (C : ℝ) (m₀ H : ℕ) : Measure (Omega n H) :=
  (gnm n C m₀).prod
    ((Measure.pi fun _ : Fin H => unifIco C).prod (Measure.pi fun _ : Fin H => unifIco 1))

/-- A uniform choice from the finite set `S` driven by `U ∈ [0, 1)`: the element of index
`⌊U |S|⌋` of a fixed enumeration of `S`. -/
def pick (S : Finset (Fin n × Fin n)) (U : ℝ) : Option (Fin n × Fin n) :=
  S.toList[⌊U * S.card⌋₊]?

/-- One random update of the given type on the sample `g`, with fresh weight `ν` and selection
variable `U`: the new sample, the update request handed to the data structure, and the
selected arc (`none` only on the null event that `U ∉ [0, 1)`). -/
def stepSample (k : UpdKind) (g : Sample n) (ν U : ℝ) :
    Sample n × Option (Update n) × Option (Fin n × Fin n) :=
  match k with
  | .delete =>
    match pick g.1 U with
    | none => (g, none, none)
    | some a => ((g.1.erase a, g.2), some (.delete a.1 a.2), some a)
  | .insert =>
    match pick (offDiagPairs n \ g.1) U with
    | none => (g, none, none)
    | some a =>
      ((insert a g.1, Function.update g.2 a ν), some (.insert a.1 a.2 ν.toNNReal), some a)
  | .resample =>
    match pick g.1 U with
    | none => (g, none, none)
    | some a => ((g.1, Function.update g.2 a ν), some (.reweight a.1 a.2 ν.toNNReal), some a)

/-- The process after `t` updates: the current sample and the data-structure state (initialized
on the initial graph with source `s`, then updated by every request). -/
def procState (s : Fin n) (ops : ℕ → UpdKind) (H : ℕ) (ω : Omega n H) : ℕ → Sample n × DS n
  | 0 => (ω.1, (initDS ω.1.graph s).ds)
  | t + 1 =>
    let p := procState s ops H ω t
    if h : t < H then
      let r := stepSample (ops t) p.1 (ω.2.1 ⟨t, h⟩) (ω.2.2 ⟨t, h⟩)
      (r.1, match r.2.1 with
        | none => p.2
        | some u => (applyUpdate p.2 u).ds)
    else p

/-- The arc selected at step `t`. -/
def procArc (s : Fin n) (ops : ℕ → UpdKind) (H : ℕ) (ω : Omega n H) (t : ℕ) :
    Option (Fin n × Fin n) :=
  if h : t < H then
    (stepSample (ops t) (procState s ops H ω t).1 (ω.2.1 ⟨t, h⟩) (ω.2.2 ⟨t, h⟩)).2.2
  else none

/-- `T`: the actual work of the data structure on the `t`-th update (`0` on the null event of
a failed selection, and for `t ≥ H`). -/
def updateWork (s : Fin n) (ops : ℕ → UpdKind) (H : ℕ) (ω : Omega n H) (t : ℕ) : ℕ :=
  if h : t < H then
    let p := procState s ops H ω t
    match (stepSample (ops t) p.1 (ω.2.1 ⟨t, h⟩) (ω.2.2 ⟨t, h⟩)).2.1 with
    | none => 0
    | some u => (applyUpdate p.2 u).cost
  else 0

/-- `𝔼T` for the `t`-th update: expectation over the initial graph, its weights and every
update choice up to and including step `t`, without conditioning. -/
def expectedWork (n : ℕ) (C : ℝ) (s : Fin n) (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (updateWork s ops (t + 1) ω t : ℝ≥0∞) ∂(procMeasure n C m₀ (t + 1))

/-! ## Hop counts and the cost functionals (§6.1–6.3) -/

/-- `H_x`: the hop count of the certified shortest path to `x` in the shortest-path tree
computed on the sample's graph (`H_s = 0`, `H_x = 0` when `x` is unreachable). -/
def hop (s : Fin n) (g : Sample n) (x : Fin n) : ℕ := treeDepth (spt g.graph s) s x

/-- `H_* = max_x H_x`. -/
def hopMax (s : Fin n) (g : Sample n) : ℕ := Finset.univ.sup (hop s g)

/-- `L_x`: the unweighted directed distance from `s` (`0` when unreachable). -/
def udistFrom (s : Fin n) (g : Sample n) (x : Fin n) : ℕ := g.graph.udist s x

/-- `R`: the number of vertices reachable from `s`, including `s`. -/
def reachCount (s : Fin n) (g : Sample n) : ℕ :=
  by classical exact (Finset.univ.filter fun x => g.graph.Reach s x).card

/-- `ℛ_s`: the largest finite unweighted distance from `s`. -/
def maxFinDist (s : Fin n) (g : Sample n) : ℕ := Finset.univ.sup (udistFrom s g)

/-- `𝒞_{n,j} = (1/j) 𝔼_j Σ_x (D⁺_x + D⁻_x + log n) H_x` (eq. (6), PDF p. 8). -/
def costFunctional (n : ℕ) (C : ℝ) (s : Fin n) (j : ℕ) : ℝ≥0∞ :=
  (j : ℝ≥0∞)⁻¹ * ∫⁻ g, ∑ x, ENNReal.ofReal (((g.graph.outDeg x + g.graph.inDeg x : ℕ) : ℝ) +
    Real.log n) * (hop s g x : ℝ≥0∞) ∂(gnm n C j)

/-- `J_m = {m, m + 1} ∩ {1, …, N}`. -/
def Jset (n m : ℕ) : Finset ℕ := ({m, m + 1} : Finset ℕ).filter fun j => 1 ≤ j ∧ j ≤ numPairs n

/-- `A_j = 𝔼_j Σ_x H_x`, with `A_0 = 0`. -/
def totalHop (n : ℕ) (C : ℝ) (s : Fin n) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then 0 else ∫⁻ g, ((∑ x, hop s g x : ℕ) : ℝ≥0∞) ∂(gnm n C j)

/-- `F_j = 𝔼_j Σ_x L_x`. -/
def totalUdist (n : ℕ) (C : ℝ) (s : Fin n) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ g, ((∑ x, udistFrom s g x : ℕ) : ℝ≥0∞) ∂(gnm n C j)

/-- The average `𝔼_e φ(e)` over a uniformly chosen existing arc `e` of the graph. -/
def arcAverage (G : WDigraph n) (φ : Fin n × Fin n → ℕ) : ℝ≥0∞ :=
  (G.numArcs : ℝ≥0∞)⁻¹ * ∑ e ∈ G.arcs, (φ e : ℝ≥0∞)

end

end ExactDynamicSSSP.ExpectedUpdate


