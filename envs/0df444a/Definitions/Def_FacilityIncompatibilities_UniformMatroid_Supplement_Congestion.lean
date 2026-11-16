-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_Congestion
-- name    : FacilityIncompatibilities_UniformMatroid_Supplement_Congestion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:07.148083+00:00
-- url     : https://prove2.me/theorems/b0438ed7-f107-48ba-9f27-93cab84f1b94
-- title:
--   §4.1 — the greedy eight-slot map ν, minimum-cost injections mc(T, O), and dist(s, X)
-- statement:
--   Let $P,O\subseteq V_F$ be finite facility sets and $Q:=P\cap O$. Write $d$ for the facility–facility distance.
--
--   1. For a facility $s$ and a finite set $X$, $\mathrm{dist}(s,X)=\min_{x\in X}d(s,x)$, with $\mathrm{dist}(s,\emptyset):=+\infty$.
--   2. For $T\subseteq P$, with $\mathcal E(T,O)$ the family of injections $T\to O$,
--   $$\mathrm{mc}(T,O)=\min_{\eta\in\mathcal E(T,O)}\sum_{s\in T}d(s,\eta(s)).$$
--   3. **The greedy map** $\nu:P\to O$: fix $\nu(q)=q$ for $q\in Q$; the elements of $O\setminus Q$ are *targets*, each with eight slots. Repeatedly select a globally shortest pair $(s,o)$ among unassigned $s\in P\setminus Q$ and targets $o$ with an available slot, set $\nu(s)=o$ and consume one slot; ties may be broken arbitrarily.
--
--   The predicate "$\nu$ is a greedy map" says that $\nu$ fixes $Q$ and that there is an order $s_0,\dots,s_{k-1}$ of the elements of $P\setminus Q$ (the order of assignment) such that at every step $t$: $\nu(s_t)\in O\setminus Q$; fewer than eight of $s_0,\dots,s_{t-1}$ are mapped to $\nu(s_t)$; and $d(s_t,\nu(s_t))\le d(s_u,o)$ for every $u\ge t$ and every target $o$ to which fewer than eight of $s_0,\dots,s_{t-1}$ are mapped. These are exactly the outputs of the procedure under all tie-breaking rules.
--
--   These objects enter Lemma 16, the simultaneous subset bound behind Theorem 4.
--
--   **Formalization Note** $\mathrm{dist}$ and $\mathrm{mc}$ take values in $\mathbb R_{\ge0}\cup\{\infty\}$ (`ℝ≥0∞`): the empty minimum is $+\infty$ and $\mathrm{mc}(T,O)=\infty$ exactly when no injection exists. $\nu$ is a function on all facilities; only its values on $P$ matter.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, §4.1, printed pp.14–15 / PDF pp.15–16 (construction of ν, definition of mc(T, O), dist(s, ∅) := +∞ in Lemma 16)

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

variable {C F : Type*}

/-- `dist(s, X) = min_{x ∈ X} d(s, x)` for a facility `s` and a finite facility set `X`
(§4.1, printed p.15 / PDF p.16), with `dist(s, ∅) := +∞`.

**Formalization Note** Valued in `ℝ≥0∞`: the infimum over the empty set is `⊤ = +∞`, the
paper's convention, never a junk `0`. -/
noncomputable def setDist (I : Instance C F) (s : F) (X : Finset F) : ℝ≥0∞ :=
  ⨅ x ∈ X, ENNReal.ofReal (I.fdist s x)

/-- `mc(T, O) = min_{η ∈ E(T, O)} ∑_{s ∈ T} d(s, η(s))` (§4.1, printed p.15 / PDF p.16): the
minimum total facility–facility distance of an injection `η : T → O`.

**Formalization Note** Valued in `ℝ≥0∞`; it is `⊤` exactly when there is no injection
(`|T| > |O|`), otherwise the infimum is over a finite nonempty set and is attained. -/
noncomputable def mc (I : Instance C F) (T O : Finset F) : ℝ≥0∞ :=
  ⨅ (η : T → O) (_ : Function.Injective η), ENNReal.ofReal (∑ s : T, I.fdist s (η s))

/-- **The greedy bounded-congestion map** `ν : P → O` of §4.1 (printed pp.14–15 / PDF pp.15–16),
with `Q = P ∩ O`: `ν(q) = q` for `q ∈ Q`; the targets are `O \ Q`, each with eight slots;
repeatedly a globally shortest pair `(s, o)` is selected among unassigned `s ∈ P \ Q` and
targets `o ∈ O \ Q` with an available slot, `ν(s) := o`, and one slot is consumed (ties
arbitrary).

`IsGreedyMap I P O ν` says that `ν` is an output of this procedure for some tie-breaking: `ν`
fixes `Q`, and there is an enumeration `s_0, …, s_{k−1}` (a duplicate-free list) of `P \ Q`, the
order of assignment, such that for every step `t`:
* `ν(s_t)` is a target in `O \ Q`;
* fewer than eight of `s_0, …, s_{t−1}` were assigned to `ν(s_t)` (a slot was available);
* `d(s_t, ν(s_t)) ≤ d(s_u, o)` for every still unassigned `s_u` (`u ≥ t`) and every target `o`
  with fewer than eight of `s_0, …, s_{t−1}` assigned to it (the pair is globally shortest). -/
def IsGreedyMap [DecidableEq F] (I : Instance C F) (P O : Finset F) (ν : F → F) : Prop :=
  (∀ q ∈ P ∩ O, ν q = q) ∧
  ∃ l : List F, l.Nodup ∧ l.toFinset = P \ (P ∩ O) ∧
    ∀ (t : ℕ) (ht : t < l.length),
      ν l[t] ∈ O \ (P ∩ O) ∧
      (l.take t).countP (fun u => decide (ν u = ν l[t])) < 8 ∧
      ∀ (u : ℕ) (hu : u < l.length), t ≤ u → ∀ o ∈ O \ (P ∩ O),
        (l.take t).countP (fun u' => decide (ν u' = o)) < 8 →
        I.fdist l[t] (ν l[t]) ≤ I.fdist l[u] o

end FacilityIncompatibilities.UniformMatroid.Supplement


