-- Prove2me | Definitions.Def_ImpatientMatching_Construction
-- name    : ImpatientMatching_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:27.442969+00:00
-- url     : https://prove2.me/theorems/14644858-65f2-4cb9-965e-06a1ecff8488
-- title:
--   The reduction instance, its constants, and the cover rule $\pi_U$
-- statement:
--   Given a source $(H,K)$ with $n$ vertices and $m$ edges, and $\varepsilon=1/100$, set
--   $$\Gamma=nL-(1+\varepsilon/2)K .$$
--   The instance has a supplier type $s_i$ of rate $L$ for each vertex $i$, a customer type $c_e$ of rate one for each edge $e$, compatible with the two endpoints of $e$, and a flexible customer type $c_0$ of rate $\Gamma-m$, compatible with every supplier. In Finite-Finite, $L=6000$, $n_0=6\cdot10^{13}$ and
--   $$\sigma=\frac{\varepsilon}{8(L+1)}-\frac{6(L+1)}{(L+4)(L-2)^2}.$$
--   In Finite-Zero, $L=96/\varepsilon=9600$ and $n_0=8\cdot10^{10}$.
--
--   Given a vertex set $U$ and an endpoint $o(e)\in e\cap U$ of every edge, the **cover rule** matches a customer $c_e$ to a supplier at $o(e)$ as soon as both are available, with priority. A flexible customer is matched when a supplier is available outside $U$ or a queue in $U$ holds at least two. Ties go by fixed index orders.
--
--   The module also defines the time integrals $\mathbb E\int_0^T|P(t)|\,dt$, $\mathbb E\int_0^T u(P(t))\,dt$ and $\mathbb E\int_0^T\Phi(P(t))\,dt$, in $[0,\infty]$.
--
--   **Formalization Note** Edges are numbered in lexicographic order on pairs $i<j$. The customer index $0$ is $c_0$. The rate of $c_0$ is $\Gamma-m$ whenever that is positive, which holds on the source range; the value $1$ outside it is never read by any statement. The rule makes one match per event, which is all the source's rule makes from a state reachable from empty, by (25) of the source.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §4.1, pp.10–11; §4.4.1, p.15; §C.1, pp.28–29; §C.4, p.31

import Definitions.Def_ImpatientMatching_MarkovRule
import Definitions.Def_ImpatientMatching_Source

open NSWApxHard.Reduction
open MeasureTheory
open scoped ENNReal
open DynStochMatching.Reward

namespace ImpatientMatching

/-- `L = 6000`, the Finite-Finite supplier rate, (9), p.11. -/
def LFF : ℚ := 6000

/-- `n₀ = 6·10¹³`, the Finite-Finite source size, (9), p.11. -/
def n0FF : ℕ := 6 * 10 ^ 13

/-- `σ := ε/(8(L + 1)) − 6(L + 1)/((L + 4)(L − 2)²)`, (10), p.11. Finite-Finite only. -/
def sigmaFF : ℚ := eps / (8 * (LFF + 1)) - 6 * (LFF + 1) / ((LFF + 4) * (LFF - 2) ^ 2)

/-- `L = 96/ε = 9600`, the Finite-Zero supplier rate, (37), p.28. -/
def LFZ : ℚ := 9600

/-- `n₀ = 8·10¹⁰`, the Finite-Zero source size, (37), p.28. -/
def n0FZ : ℕ := 8 * 10 ^ 10

open Classical in
/-- The edges `(i, j)`, `i < j`, of `H` in lexicographic order: one fixed edge order. -/
noncomputable def edgeList (H : GraphInput) : List (Fin H.N × Fin H.N) :=
  ((List.finRange H.N).product (List.finRange H.N)).filter fun p => p.1 < p.2 ∧ H.G.Adj p.1 p.2

/-- `m = |E_H|`, computed from the fixed edge order. -/
noncomputable def edgeCount (H : GraphInput) : ℕ := (edgeList H).length

/-- The two endpoints of the `e`-th edge. -/
noncomputable def edgeEnds (H : GraphInput) (e : Fin (edgeCount H)) : Fin H.N × Fin H.N :=
  (edgeList H).get e

/-- `Γ := nL − (1 + ε/2)K`, (7), p.10, and (40), p.29. -/
noncomputable def Gamma (L : ℚ) (H : GraphInput) (K : ℕ) : ℚ :=
  (H.N : ℚ) * L - (1 + eps / 2) * (K : ℚ)

/-- The rate `Γ − m` of the flexible customer type.

**Formalization Note.** `Γ − m` is positive on the source range (p.10, p.29). An input needs positive
rates on every `(H, K)`, so outside that range the value `1` is used; no statement reads it there. -/
noncomputable def flexRate (L : ℚ) (H : GraphInput) (K : ℕ) : ℚ :=
  if 0 < Gamma L H K - (edgeCount H : ℚ) then Gamma L H K - (edgeCount H : ℚ) else 1

theorem flexRate_pos (L : ℚ) (H : GraphInput) (K : ℕ) : 0 < flexRate L H K := by
  unfold flexRate
  split_ifs with h
  · exact h
  · exact one_pos

open Classical in
/-- The construction of §4.1, p.10, and §C.1, p.29: `n` supplier types of rate `L`, a flexible
customer type `c₀` of rate `Γ − m` compatible with every supplier (customer index `0`), and a rate-one
customer type `c_e` for each edge `e`, compatible with its two endpoints (customer index `e + 1`). -/
noncomputable def construction (L : ℚ) (hL : 0 < L) (H : GraphInput) (K : ℕ) : MatchInput where
  nS := H.N
  nC := edgeCount H + 1
  edge := fun i => Fin.cases true
    (fun e => decide (i = (edgeEnds H e).1 ∨ i = (edgeEnds H e).2))
  rateS := fun _ => L
  rateC := Fin.cases (flexRate L H K) (fun _ => 1)
  posS := fun _ => hL
  posC := by
    refine Fin.cases ?_ (fun _ => ?_)
    · simpa using flexRate_pos L H K
    · simp

/-- The Finite-Finite instance of §4.1, with `L = 6000`, on the flat type index `Fin (n + (m + 1))`. -/
noncomputable def ffInstance (H : GraphInput) (K : ℕ) :
    Instance (H.N + (edgeCount H + 1)) :=
  toInstance Regime.finiteFinite (construction LFF (by norm_num [LFF]) H K)

/-- The Finite-Zero instance of §C.1, with `L = 9600`, on the flat type index `Fin (n + (m + 1))`. -/
noncomputable def fzInstance (H : GraphInput) (K : ℕ) :
    Instance (H.N + (edgeCount H + 1)) :=
  toInstance Regime.finiteZero (construction LFZ (by norm_num [LFZ]) H K)

/-- The flat index of the supplier type `s_i`. -/
abbrev suppIdx {N m : ℕ} (i : Fin N) : Fin (N + (m + 1)) := Fin.castAdd (m + 1) i

/-- The flat index of the flexible customer type `c₀`. -/
abbrev flexIdx {N m : ℕ} : Fin (N + (m + 1)) := Fin.natAdd N 0

/-- The flat index of the edge customer type `c_e`. -/
abbrev edgeIdx {N m : ℕ} (e : Fin m) : Fin (N + (m + 1)) := Fin.natAdd N e.succ

/-- The decision with one match between the types `a` and `b`, read for `a < b`. -/
def oneMatch {n : ℕ} (a b : Fin n) : Decision n :=
  fun i j => if i = a ∧ j = b then 1 else 0

/-- The pre-decision rule of `π_U` (§4.4.1, p.15; §C.4, p.31). First, a customer `c_e` takes a
supplier at `o(e)` if both are available, the edge customers having priority. Otherwise a flexible
customer takes a supplier outside `U`, or from a queue in `U` holding at least two. All ties go by the
fixed index orders. From a state reachable from empty, an event creates at most one such pair
((25), p.17), so one match per event is what the source's rule makes. -/
def coverDecision {N m : ℕ} (U : Finset (Fin N)) (o : Fin m → Fin N)
    (q : State (N + (m + 1))) : Decision (N + (m + 1)) :=
  match (List.finRange m).find? (fun e => decide (0 < q (edgeIdx e) ∧ 0 < q (suppIdx (o e)))) with
  | some e => oneMatch (suppIdx (o e)) (edgeIdx e)
  | none =>
    match (List.finRange N).find? (fun i => decide (0 < q flexIdx ∧
        ((i ∉ U ∧ 0 < q (suppIdx i)) ∨ (i ∈ U ∧ 2 ≤ q (suppIdx i))))) with
    | some i => oneMatch (suppIdx i) flexIdx
    | none => 0

/-- **The cover policy `π_U` as a Markov rule** (§4.4.1, p.15; §C.4, p.31): deterministic, and reading
only the queue vector just after the event. The same rule serves both regimes: in Finite-Zero a
customer not served at its arrival is dropped by `postState`. -/
def coverRule {N m : ℕ} (U : Finset (Fin N)) (o : Fin m → Fin N) : MarkovRule (N + (m + 1)) where
  decide := fun q ev _ => coverDecision U o (preState q ev)
  measurable := fun _ _ => measurable_const

/-- `o(e) ∈ e ∩ U` for every edge `e` (p.15, p.31). This forces `U` to be a vertex cover. -/
def IsCoverAssignment (H : GraphInput) (U : Finset (Fin H.N))
    (o : Fin (edgeCount H) → Fin H.N) : Prop :=
  ∀ e, o e ∈ U ∧ (o e = (edgeEnds H e).1 ∨ o e = (edgeEnds H e).2)

/-- `E ∫₀ᵀ |P(t)| dt` of (19), p.13, as an iterated lower integral in `ℝ≥0∞`. -/
noncomputable def intOccupied {nS nC : ℕ} (D : Instance (nS + nC)) (π : MatchingPolicy)
    (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioc 0 T, ((occupied D π ω t).card : ℝ≥0∞) ∂MeasureTheory.volume ∂seedLaw

/-- `E ∫₀ᵀ u(P(t)) dt` of (20), p.13, as an iterated lower integral in `ℝ≥0∞`. -/
noncomputable def intUncovered (H : GraphInput) (D : Instance (H.N + (edgeCount H + 1)))
    (π : MatchingPolicy) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioc 0 T, (uncovered H (occupied D π ω t) : ℝ≥0∞)
    ∂MeasureTheory.volume ∂seedLaw

/-- `E ∫₀ᵀ Φ(P(t)) dt` of (21), p.15, as an iterated lower integral in `ℝ≥0∞`. -/
noncomputable def intPhi (H : GraphInput) (D : Instance (H.N + (edgeCount H + 1)))
    (π : MatchingPolicy) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioc 0 T, (Phi H (occupied D π ω t) : ℝ≥0∞)
    ∂MeasureTheory.volume ∂seedLaw

end ImpatientMatching


