-- Prove2me | Definitions.Def_KTaxi_Competitive_Algorithm1
-- name    : KTaxi_Competitive_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:03.768172+00:00
-- url     : https://prove2.me/theorems/d75c8d9e-319d-478d-8566-34f874f1fe94
-- title:
--   Algorithm 1 (Online $k$-Taxi): weights, exponential clocks and the list update
-- statement:
--   Algorithm 1 keeps the taxis in an **ordered list** $x=(x_1,\dots,x_k)$ of locations. The taxi in position $i$ has weight
--   $$
--   w_1=1,\qquad w_i=2\cdot3^{\,i-2}\quad(2\le i\le k),
--   $$
--   so that $w_i=2\sum_{j<i}w_j$ and $\sum_{i\le m}w_i=3^{m-1}$.
--
--   On a request $(r,s)$, let $d_i=d(x_i,r)$. Independently for each $i$, the clock $\zeta_i$ is $0$ if $d_i=0$, and otherwise $\zeta_i\sim\mathrm{Exp}(w_i/d_i)$ (exponential distribution with rate $w_i/d_i$). The clocks stay attached to the taxis. The list is then updated by a scan over $i=1,\dots,k$: if the taxi in position $i$ has a strictly smaller clock than the taxi currently in position $1$, the two are swapped. Finally the taxi in position $1$ serves the request: it moves to $r$ and then to $s$.
--
--   1. The **list update** for clock values $\zeta$ is the permutation $\pi$ giving, for each new position, the old position whose taxi now occupies it. Its law $\mathrm{scanLaw}(x,r)$ is the distribution of $\pi$ when the clocks are drawn as above.
--   2. The list **after the round** is the list $(x_{\pi(1)},\dots,x_{\pi(k)})$ with its first entry moved to $r$.
--   3. As an online algorithm, Algorithm 1 has as state the ordering of the labels (which label is in which position), starting from the identity ordering; the serving taxi is the one in the new first position.
--
--   **Formalization Note** Positions are 0-based slots `Fin k`; `weight j` is the weight of slot `j` (rank `j + 1`). The clock law is `Measure.pi` of `Measure.dirac 0` or `ProbabilityTheory.expMeasure (w/d)`; the scan `scanPerm` is a left fold of `scanStep` over `List.finRange k`; `scanLaw x r` is the push-forward of the clock law by `scanPerm`, converted with `Measure.toPMF` on the finite type `Equiv.Perm (Fin k)`. The measurability of the scan is proved inside the definition (with the discrete σ-algebra on permutations), so the push-forward is a genuine probability measure. The state of `algorithm1` is `Equiv.Perm (Fin k)` (slot ↦ label), initially `1`. The algorithm needs `k ≥ 1` (`[NeZero k]`).
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §3 Algorithm Description and Algorithm 1 (PDF p. 5); exponential distribution, §2 (PDF p. 4)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace KTaxi.Competitive

/-! # Algorithm 1 (Online k-Taxi)

Coester, Huang, Poon, STOC 2027 submission #96, §3, PDF p. 5 (Algorithm 1).

Indices are 0-based: the paper's rank `i ∈ {1, …, k}` is the slot `i - 1 : Fin k` of the
ordered list. An **ordered list** is `x : Fin k → V`, slot ↦ location.
-/

/-- The weights, 0-based: slot `0` (rank 1) has weight `w₁ = 1`, slot `j + 1` (rank `j + 2`)
has weight `w_{j+2} = 2 · 3^j` (paper: `w_i = 2 · 3^{i-2}` for `2 ≤ i ≤ k`). -/
def weight : ℕ → ℝ
  | 0 => 1
  | j + 1 => 2 * 3 ^ j

lemma weight_pos (j : ℕ) : 0 < weight j := by
  cases j <;> simp [weight]

/-- Law of one clock `ζ`: the point mass at `0` if the taxi is already at the pickup (`d = 0`),
otherwise the exponential distribution of rate `w / d`. -/
noncomputable def clockLaw (w d : ℝ) : Measure ℝ :=
  if d = 0 then Measure.dirac 0 else expMeasure (w / d)

lemma isProbabilityMeasure_clockLaw {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    IsProbabilityMeasure (clockLaw w d) := by
  unfold clockLaw
  split_ifs with h
  · infer_instance
  · exact isProbabilityMeasure_expMeasure (div_pos hw (lt_of_le_of_ne hd (Ne.symm h)))

variable {V : Type*} [MetricSpace V] {k : ℕ}

/-- Joint law of the clocks `(ζ_j)_{j}` for the ordered list `x` and pickup `r`: independent,
`ζ_j = 0` if `d(x j, r) = 0`, else `ζ_j ∼ Exp(w_j / d(x j, r))`. -/
noncomputable def clocksLaw (x : Fin k → V) (r : V) : Measure (Fin k → ℝ) :=
  Measure.pi fun j => clockLaw (weight j) (dist (x j) r)

instance isProbabilityMeasure_clocksLaw (x : Fin k → V) (r : V) :
    IsProbabilityMeasure (clocksLaw x r) := by
  have : ∀ j : Fin k, IsProbabilityMeasure (clockLaw (weight j) (dist (x j) r)) := fun j =>
    isProbabilityMeasure_clockLaw (weight_pos j) dist_nonneg
  unfold clocksLaw
  infer_instance

variable [NeZero k]

/-- One step of the scan (loop body of Algorithm 1 at index `i`). `π` maps current slots to
original slots; the clocks stay attached to the original slots. If the taxi now in slot `i` has a
strictly smaller clock than the taxi in the first slot, the two slots are swapped. -/
noncomputable def scanStep (ζ : Fin k → ℝ) (π : Equiv.Perm (Fin k)) (i : Fin k) : Equiv.Perm (Fin k) :=
  if ζ (π i) < ζ (π 0) then π * Equiv.swap 0 i else π

/-- The list update of Algorithm 1 for clock values `ζ` (indexed by the original slots): scan
`i = 0, 1, …, k - 1` in order (the step at `i = 0` does nothing). The result `π` maps each new
slot to the original slot whose taxi now occupies it. -/
noncomputable def scanPerm (ζ : Fin k → ℝ) : Equiv.Perm (Fin k) :=
  (List.finRange k).foldl (scanStep ζ) 1

/-- The discrete σ-algebra on permutations, used only to push the clock law forward. -/
local instance : MeasurableSpace (Equiv.Perm (Fin k)) := ⊤

local instance : DiscreteMeasurableSpace (Equiv.Perm (Fin k)) := ⟨fun _ => trivial⟩

lemma measurable_foldl_scanStep (l : List (Fin k)) (π₀ : Equiv.Perm (Fin k)) :
    Measurable fun ζ : Fin k → ℝ => l.foldl (scanStep ζ) π₀ := by
  induction l using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton l i ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hstep : Measurable fun p : (Fin k → ℝ) × Equiv.Perm (Fin k) => scanStep p.1 p.2 i := by
      refine measurable_from_prod_countable_left fun π => ?_
      show Measurable fun ζ : Fin k → ℝ => scanStep ζ π i
      unfold scanStep
      exact Measurable.ite (measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _))
        (measurable_const (a := π * Equiv.swap 0 i)) (measurable_const (a := π))
    exact hstep.comp (measurable_id.prodMk ih)

lemma measurable_scanPerm : Measurable (scanPerm : (Fin k → ℝ) → Equiv.Perm (Fin k)) :=
  measurable_foldl_scanStep _ _

/-- **One round of Algorithm 1**, as a law: the distribution of the list update `π`
(new slot ↦ original slot) when the ordered list is `x` and the pickup is `r`. It is the
push-forward of the clock law `clocksLaw x r` under the deterministic scan `scanPerm`. -/
noncomputable def scanLaw (x : Fin k → V) (r : V) : PMF (Equiv.Perm (Fin k)) :=
  haveI : IsProbabilityMeasure ((clocksLaw x r).map scanPerm) :=
    Measure.isProbabilityMeasure_map measurable_scanPerm.aemeasurable
  ((clocksLaw x r).map scanPerm).toPMF

/-- The ordered list after a round with list update `π` and pickup `r`: the taxi of original
slot `π j` is in new slot `j`, and the taxi in the first slot has moved to `r`. -/
def afterRound (x : Fin k → V) (π : Equiv.Perm (Fin k)) (r : V) : Fin k → V :=
  Function.update (fun j => x (π j)) 0 r

/-- **Algorithm 1** as an online algorithm. Its state `σ` maps each slot of the ordered list to
the label of the taxi in that slot; initially the identity. On request `(r, s)` with labelled
configuration `xlab`, the ordered list is `xlab ∘ σ`; a list update `π ∼ scanLaw (xlab ∘ σ) r`
is drawn, the new state is `σ * π` (new slot ↦ label) and the serving taxi is the one in the new
first slot. -/
noncomputable def algorithm1 (V : Type*) [MetricSpace V] (k : ℕ) [NeZero k] : OnlineAlg V k where
  State := Equiv.Perm (Fin k)
  init := 1
  step σ xlab r _ := (scanLaw (fun j => xlab (σ j)) r).map fun π => (σ * π, (σ * π) 0)

end KTaxi.Competitive


