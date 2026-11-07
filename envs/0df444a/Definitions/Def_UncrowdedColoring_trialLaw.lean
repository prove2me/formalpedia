-- Prove2me | Definitions.Def_UncrowdedColoring_trialLaw
-- name    : UncrowdedColoring_trialLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:21.301338+00:00
-- url     : https://prove2.me/theorems/d8137504-ddf7-48b9-8a47-6b8c830fb72d
-- title:
--   The trials of Algorithm 4.1: activations, colors, equalizing coin flips
-- statement:
--   For a list assignment $L$ on $U$, one nibble step draws, mutually independently: a set $A\subseteq U$ containing each vertex with probability $\alpha$; a color $c_v$ uniform on $L(v)$ for each $v\in U$; and for each $v\in U$, $c\in L(v)$ a Bernoulli variable $\mathrm{eq}(v,c)$ with
--   $$\mathbb P(\mathrm{eq}(v,c)=1)=\frac{\mathrm{keep}_i}{\mathbb P(c\notin D(v))}.$$
--   A color $c$ is **discarded** at $v$, written $c\in D(v)$, if some edge $e\in E(F_c,v)$ has $u\in A$ and $c_u=c$ for all $u\in e-v$.
--
--   This product law is the probability space of all the concentration lemmas of the mission.
--
--   **Formalization Note** The sample space is a finite product of discrete spaces. `coin` clips its parameter to $[0,1]$, and a uniform color on an empty list is a Dirac mass, so the law is always a probability measure; by Lemma 4.9 and (Q2) neither default is reached under $P(i)$ for large $d$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Algorithm 4.1, Steps (1)–(3), eq. (31), p.24; trials listed on p.29

import Mathlib
import Definitions.Def_UncrowdedColoring_paramState

open scoped Classical
open MeasureTheory

namespace UncrowdedColoring

/-- The activation and color trials of Step (1) of Algorithm 4.1 (p.24): one Boolean and one color
per vertex of `U`. -/
abbrev ActColSpace {V : Type*} (U : Finset V) : Type _ := (↥U → Bool) × (↥U → ℕ)

/-- The index set `{(v, c) : v ∈ U, c ∈ L(v)}` of the equalizing coin flips of Step (3) (p.24). -/
abbrev EqIndex {V : Type*} (U : Finset V) (L : V → Finset ℕ) : Type _ := Σ u : ↥U, ↥(L u)

/-- The sample space of Algorithm 4.1 (p.24): "for all vertices u ∈ U, the inclusion of u in A, the
color choice c_u, and the equalizing coin flips for all colors c′ ∈ L(u) at u" (trials listed on
p.29). (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, pp.24, 29.) -/
abbrev TrialSpace {V : Type*} (U : Finset V) (L : V → Finset ℕ) : Type _ :=
  ActColSpace U × (EqIndex U L → Bool)

/-- The activated set `A ⊆ U` read from the trials (Step (1), p.24). -/
def activeSet {V : Type*} {U : Finset V} (a : ↥U → Bool) : Set V :=
  {u | ∃ h : u ∈ U, a ⟨u, h⟩ = true}

/-- The color `c_u` read from the trials (Step (1), p.24); the value off `U` is never used. -/
noncomputable def colourRead {V : Type*} {U : Finset V} (col : ↥U → ℕ) (u : V) : ℕ :=
  if h : u ∈ U then col ⟨u, h⟩ else 0

/-- `eq(u, c) = 1`, read from the trials (Step (3), p.24), for `u ∈ U`, `c ∈ L(u)`. -/
def eqRead {V : Type*} {U : Finset V} {L : V → Finset ℕ} (e : EqIndex U L → Bool) (u : V) (c : ℕ) :
    Prop :=
  ∃ (hu : u ∈ U) (hc : c ∈ L u), e ⟨⟨u, hu⟩, ⟨c, hc⟩⟩ = true

/-- The law on `Bool` of a coin with `P(true) = p`.

**Formalization Note.** `p` is clipped to `[0, 1]`, so `coin p` is a probability measure for every
real `p` and there is no junk measure. The clip is inactive on `α` for large `d` and on the bias (31)
by Lemma 4.9. -/
noncomputable def coin (p : ℝ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)

/-- The law on `ℕ` of a uniform choice from the list `s`.

**Formalization Note.** The value on an empty list is a Dirac mass, which keeps the law a probability
measure for all data. It is not reached: (Q2) of `P(i)` gives `|L(v)| = ⌈q_i⌉ ≥ 1` once `q_i > 0`. -/
noncomputable def uniformColour (s : Finset ℕ) : Measure ℕ :=
  if h : s.Nonempty then (PMF.uniformOfFinset s h).toMeasure else Measure.dirac 0

instance (p : ℝ) : IsProbabilityMeasure (coin p) := by
  unfold coin; infer_instance

instance (s : Finset ℕ) : IsProbabilityMeasure (uniformColour s) := by
  unfold uniformColour; split <;> infer_instance

/-- The joint law of the activations and colors (Step (1), p.24): each `v ∈ U` is activated
independently with probability `α`, and independently chooses `c_v` uniformly from `L(v)`. -/
noncomputable def actColLaw {V : Type*} (U : Finset V) (L : V → Finset ℕ) (ε d : ℝ) :
    Measure (ActColSpace U) :=
  (Measure.pi fun _ : ↥U => coin (alpha ε d)).prod
    (Measure.pi fun u : ↥U => uniformColour (L u))

/-- `c` **is discarded at `v`** (Step (2), p.24): "there exists an edge e ∈ E(F_c, v) for which u ∈ A
and c_u = c for all u ∈ e − v." The set `D(v)` is `{c | IsDiscarded F A col v c}`. (Dhawan, Methuku,
Vo, manuscript sha256 2e7243ce…, p.24.) -/
def IsDiscarded {V : Type*} (F : ℕ → Finset (Finset V)) (A : Set V) (col : V → ℕ) (v : V) (c : ℕ) :
    Prop :=
  ∃ e ∈ F c, v ∈ e ∧ ∀ u ∈ e.erase v, u ∈ A ∧ col u = c

/-- `P(c ∈ D(v))` under the law of Step (1) (p.24); the event depends only on the activations and
colors. -/
noncomputable def discardProb {V : Type*} (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) (ε d : ℝ) (v : V) (c : ℕ) : ℝ :=
  (actColLaw U L ε d).real
    {x | IsDiscarded F (activeSet x.1) (colourRead x.2) v c}

/-- The bias of the equalizing coin flip, `P(eq(v, c) = 1) = keep_i / P(c ∉ D(v))` (eq. (31), p.24).

**Formalization Note.** The event in the denominator is written as printed. By Lemma 4.9 the ratio
lies in `[0, 1]` under `P(i)`; `coin` clips it otherwise, which never occurs for the instances of the
mission. -/
noncomputable def eqBias {V : Type*} (k : ℕ) (ε d : ℝ) (i : ℕ) (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) (v : V) (c : ℕ) : ℝ :=
  keep k ε d i /
    (actColLaw U L ε d).real
      {x | ¬ IsDiscarded F (activeSet x.1) (colourRead x.2) v c}

/-- The law of all trials of Algorithm 4.1 (Steps (1) and (3), p.24): the activations, the colors and
the equalizing coin flips with biases (31) are mutually independent.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Algorithm 4.1, p.24. -/
noncomputable def trialLaw {V : Type*} (k : ℕ) (ε d : ℝ) (i : ℕ) (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) : Measure (TrialSpace U L) :=
  (actColLaw U L ε d).prod
    (Measure.pi fun x : EqIndex U L => coin (eqBias k ε d i U L F (x.1 : V) (x.2 : ℕ)))

end UncrowdedColoring


