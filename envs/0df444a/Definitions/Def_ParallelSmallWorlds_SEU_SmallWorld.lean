-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld
-- name    : ParallelSmallWorlds_SEU_SmallWorld
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:12.07599+00:00
-- url     : https://prove2.me/theorems/85f80442-afb9-4cf1-8a73-749dd43c8b7d
-- title:
--   A small world $\{\Theta_w,C_w,A_w,\succeq_{\Theta_w},\succeq_{C_w}\}$ with its extended relations
-- statement:
--   A **small world** consists of a set of states $\Theta$ and a set of consequences $C$ together with
--
--   1. a field (or σ-field) $Q$ of **events** on $\Theta$;
--   2. a **likelihood relation** $\succeq_\Theta$ ("at least as likely as") on the set union $Q\cup\mathcal B$ of events of $\Theta$ and reference events;
--   3. a **conditional likelihood** relation $(R\mid T)\succeq_\Theta(S\mid T)$ on triples of events;
--   4. a **preference** $\succeq_C$ on consequences, and its extension $\succeq_S$ to consequences and gambles;
--   5. a set $A$ of **acts**, functions $a:\Theta\to C$, with a preference $\succeq_A$ on acts.
--
--   Strict and indifference relations are derived as usual: $x\succ y$ iff $x\succeq y$ and not $y\succeq x$; $x\sim y$ iff $x\succeq y$ and $y\succeq x$.
--
--   Each scenario of a scenario-planning exercise is modelled by its own small world; worlds share only the reference experiment $\mathcal B$.
--
--   **Formalization Note** All relations are primitive. Events of $\Theta$ and reference events live in the disjoint sum `Set Θ ⊕ Set ℝ`; the relation $\succeq_\Theta$ is only constrained on its domain $Q\cup\mathcal B$ (`LikDom`), and the paper's single empty set is recovered by the axiom field `empty_identified`.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), §4, pp.18–20 (PDF pp.19–21), and p.27 (PDF p.28) for ⪰Aw

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_RefEvents
import Definitions.Def_ParallelSmallWorlds_SEU_Gamble

namespace ParallelSmallWorlds.SEU

/-- **A small world `{Θw, Cw, Aw, ⪰Θw, ⪰Cw}` with its events, reference comparisons and the
extended preference relations.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), §4, pp.18–27 (PDF pp.19–28).

A `SmallWorld Θ C` over a state set `Θ` and a consequence set `C` consists of

* `Q` — the field (or σ-field) `Qw` of events on `Θ` (p.19);
* `lik` — the likelihood relation `⪰Θw` on the set union `Qw ∪ B` (p.20); an event `R` of `Θ` is
  `Sum.inl R`, a reference event `E ⊆ [0,1]` is `Sum.inr E`;
* `condLik R S T` — the conditional likelihood `(R | T) ⪰Θw (S | T)` (p.22);
* `prefC` — the preference `⪰Cw` on consequences (p.18);
* `prefS` — its extension `⪰Sw` to consequences and gambles `C ∪ PSw` (p.24);
* `A` — the acts `Aw`, functions `Θ → C` (p.11, (4));
* `prefA` — the preference `⪰Aw` on acts (p.27).

The derived relations follow p.18: `x ≻ y ⟺ x ⪰ y ∧ ¬ y ⪰ x` and `x ∼ y ⟺ x ⪰ y ∧ y ⪰ x`
(`strictLik`, `indiffLik`, `strictC`, `strictS`, `indiffS`). `LikDom` is the domain `Qw ∪ B`.

**Formalization Note.** The relations are primitive: nothing here derives them from a measure or
a utility. Events of `Θ` and reference events are kept apart by the disjoint sum
`Set Θ ⊕ Set ℝ`; in the paper's set union `Qw ∪ B` the empty set is a single element, and the
identification `∅_Θ ∼ ∅_B` is imposed as a field of `LikelihoodAxioms`. `lik` is only
constrained on `LikDom`. -/
structure SmallWorld (Θ : Type*) (C : Type*) where
  /-- The field of events `Qw` on `Θ`. -/
  Q : Set (Set Θ)
  /-- The likelihood relation `⪰Θw` on `Qw ∪ B`. -/
  lik : Set Θ ⊕ Set ℝ → Set Θ ⊕ Set ℝ → Prop
  /-- Conditional likelihood: `condLik R S T` is `(R | T) ⪰Θw (S | T)`. -/
  condLik : Set Θ → Set Θ → Set Θ → Prop
  /-- The preference `⪰Cw` on consequences. -/
  prefC : C → C → Prop
  /-- The preference `⪰Sw` on consequences and gambles. -/
  prefS : Obj C → Obj C → Prop
  /-- The acts `Aw`. -/
  A : Set (Θ → C)
  /-- The preference `⪰Aw` on acts. -/
  prefA : (Θ → C) → (Θ → C) → Prop

namespace SmallWorld

variable {Θ C : Type*} (W : SmallWorld Θ C)

/-- The domain `Qw ∪ B` of `⪰Θw`. -/
def LikDom : Set (Set Θ ⊕ Set ℝ) :=
  {x | Sum.elim (fun R => R ∈ W.Q) (fun E => E ∈ RefEvents) x}

/-- Strictly more likely, `≻Θw` (p.18). -/
def strictLik (x y : Set Θ ⊕ Set ℝ) : Prop := W.lik x y ∧ ¬ W.lik y x

/-- Equally likely, `∼Θw` (p.18). -/
def indiffLik (x y : Set Θ ⊕ Set ℝ) : Prop := W.lik x y ∧ W.lik y x

/-- Strictly better, `≻Cw` (p.18). -/
def strictC (c c' : C) : Prop := W.prefC c c' ∧ ¬ W.prefC c' c

/-- Strictly better, `≻Sw`. -/
def strictS (x y : Obj C) : Prop := W.prefS x y ∧ ¬ W.prefS y x

/-- Indifferent, `∼Sw`. -/
def indiffS (x y : Obj C) : Prop := W.prefS x y ∧ W.prefS y x

end SmallWorld

end ParallelSmallWorlds.SEU


