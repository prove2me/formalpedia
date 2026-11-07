-- Prove2me | Definitions.Def_UncrowdedColoring_nibblePsi
-- name    : UncrowdedColoring_nibblePsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:15:18.978186+00:00
-- url     : https://prove2.me/theorems/2fc1d526-d243-4326-8c6a-665da68b8d6b
-- title:
--   One nibble step: kept colors, $\psi$, $\tilde U$, $F'_c$, trimming, $\tilde F_c$
-- statement:
--   Given an outcome of the trials, the kept colors are $L'(v)=\{c\in L(v):c\notin D(v),\ \mathrm{eq}(v,c)=1\}$. The assignment $\psi$ sets $\psi(v)=c_v$ for $v\in A$ with $c_v\in L'(v)$, and $\tilde U=U\setminus\mathrm{supp}(\psi)$. For each $2\le\ell\le k$ the edges of $F'_c$ of size $\ell$ are the $\ell$-subsets $e'$ of $\tilde U$ with $e'\subseteq e\in E(F_c)$, $c\in\bigcap_{v\in e'}L'(v)$ and $\psi(v)=c$ on $e\setminus e'$. The list $\tilde L(v)$ is obtained from $L'(v)$ by removing colors arbitrarily down to size $\lceil q_{i+1}\rceil$, and $E(\tilde F_c)=\{e'\in E(F'_c):c\in\bigcap_{v\in e'}\tilde L(v)\}$.
--
--   This is the deterministic part of one step of the nibble.
--
--   **Formalization Note** "Arbitrarily" is a predicate `IsTrimming`, and statements quantify over every trimming. The target size is $\lceil q_{i+1}\rceil$, as in the corrected (Q2).
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Algorithm 4.1, Steps (3)–(7), p.24

import Mathlib
import Definitions.Def_UncrowdedColoring_trialLaw

open scoped Classical

namespace UncrowdedColoring

variable {V : Type*} {U : Finset V} {L : V → Finset ℕ}

/-- The kept colors `L′(v) := {c ∈ L(v) : c ∉ D(v), eq(v, c) = 1}` (Step (3), p.24). (Dhawan, Methuku,
Vo, manuscript sha256 2e7243ce…, Algorithm 4.1, p.24.) -/
noncomputable def keptColours (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (v : V) : Finset ℕ :=
  (L v).filter fun c =>
    ¬ IsDiscarded F (activeSet T.1.1) (colourRead T.1.2) v c ∧ eqRead T.2 v c

/-- The partial color assignment `ψ` of Step (4) (p.24): `ψ(v) := c_v` for every `v ∈ A` with
`c_v ∈ L′(v)`. -/
noncomputable def nibblePsi (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (v : V) : Option ℕ :=
  if v ∈ activeSet T.1.1 ∧ colourRead T.1.2 v ∈ keptColours F T v then
    some (colourRead T.1.2 v)
  else none

/-- `Ũ := U \ supp(ψ)` (Step (4), p.24). -/
noncomputable def uTilde (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) : Finset V :=
  U.filter fun v => nibblePsi F T v = none

/-- The edges of `F′_c` (Step (5), p.24): for each `2 ≤ ℓ ≤ k`, the `ℓ`-subsets `e′` of `Ũ` with
`e′ ⊆ e ∈ E(F_c)`, `c ∈ ⋂_{v∈e′} L′(v)`, and `ψ(v) = c` for all `v ∈ e \ e′`. -/
noncomputable def fPrime (k : ℕ) (F : ℕ → Finset (Finset V)) (T : TrialSpace U L) (c : ℕ) :
    Finset (Finset V) :=
  (uTilde F T).powerset.filter fun e' =>
    (2 ≤ e'.card ∧ e'.card ≤ k) ∧
      ∃ e ∈ F c, e' ⊆ e ∧ (∀ v ∈ e', c ∈ keptColours F T v) ∧
        ∀ v ∈ e \ e', nibblePsi F T v = some c

/-- `L̃` is a **trimming** of `L′` on `Ũ` (Step (6), p.24), "removing max{|L′(v)| − q_{i+1}, 0} colors
from L′(v) arbitrarily": `L̃(v) ⊆ L′(v)` and `|L̃(v)| = min{|L′(v)|, ⌈q_{i+1}⌉}`.

**Formalization Note (correction).** The target size is `⌈q_{i+1}⌉`, matching the correction of (Q2)
in `SatisfiesP`. Statements quantify over every trimming, which is what "arbitrarily" asks. -/
def IsTrimming (Ũ : Finset V) (L' Lt : V → Finset ℕ) (q' : ℝ) : Prop :=
  ∀ v ∈ Ũ, Lt v ⊆ L' v ∧ (Lt v).card = min (L' v).card ⌈q'⌉₊

/-- The edges of `F̃_c` (Step (7), p.24): `e′ ∈ E(F′_c)` with `c ∈ ⋂_{v∈e′} L̃(v)`. -/
noncomputable def fTilde (k : ℕ) (F : ℕ → Finset (Finset V)) (T : TrialSpace U L)
    (Lt : V → Finset ℕ) (c : ℕ) : Finset (Finset V) :=
  (fPrime k F T c).filter fun e' => ∀ v ∈ e', c ∈ Lt v

end UncrowdedColoring


