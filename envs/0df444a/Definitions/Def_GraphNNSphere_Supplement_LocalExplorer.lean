-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_LocalExplorer
-- name    : GraphNNSphere_Supplement_LocalExplorer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:46:49.874166+00:00
-- url     : https://prove2.me/theorems/b6ebc260-4b60-43a3-b7aa-a310ecc46eef
-- title:
--   Local exploration algorithms, budgets and distinct-evaluation cost
-- statement:
--   A **local exploration algorithm** works on a fixed graph of the sample ($G_\rho$ or $N_\Delta$) and a fixed query $q$, with internal randomness independent of the data. At each step it either
--
--   1. requests an entry: the label is taken from a sequence fixed before sampling or drawn afresh uniformly, independently of the coordinates and the history, and its distance to $q$ is evaluated; or
--   2. expands an already evaluated point whose list has not been scanned: the whole neighbor list is scanned and evaluated; or
--   3. stops.
--
--   The choice may depend on $q$, the internal randomness and the complete history (requested and expanded labels, scanned lists, positions of evaluated points). Success is recorded after the first operation whose evaluated points include a member of $\mathrm{Top}_k(q)$. The **cost** $V$ counts the distinct points evaluated through that operation across all operations (a shared cache), and $V=\infty$ if no target is found. A **budget** $(T,E)$ allows at most $T$ expansions and $E$ entry requests.
--
--   **Formalization Note** The $j$-th entry request evaluates a label that is a function of the internal randomness only; fixed sequences and fresh uniform labels are special cases, and conditioning on the randomness reduces any such algorithm to one with a fixed sequence. An operation beyond the budget, or an invalid expansion, ends the run. A measurable algorithm is one whose entry labels and chosen operations are measurable functions of the randomness and the sample.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6; §5.2, p.59; Theorem 5.9, p.78

import Mathlib
import Definitions.Def_GraphNNSphere_NavGraph
import Definitions.Def_GraphNNSphere_IsTarget

open MeasureTheory

namespace GraphNNSphere

namespace Supplement

/-- The operations of a local exploration algorithm: request an entry, expand a label, or stop
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6, and §5.2, p.59). -/
inductive ExplAction (n : ℕ) where
  | entry
  | expand (v : Fin n)
  | stop

/-- What an operation reveals to the algorithm: an entry request reveals the requested label and its
position; an expansion reveals the expanded label and its scanned neighbor list with the positions
of the listed points (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6). -/
inductive ExplObs (n d : ℕ) where
  | entry (i : Fin n) (x : Sph d)
  | expand (v : Fin n) (scan : List (Fin n × Sph d))

/-- A local exploration algorithm with internal randomness `ω ∈ Ω` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6, and
§5.2, p.59). At each step it either requests an entry or expands an already evaluated point whose
list has not been scanned, or stops; the choice may depend on the internal randomness and the
complete exploration history (requested and expanded labels, scanned lists and positions of
evaluated points). The query is fixed, so dependence on it is dependence on the algorithm.

**Formalization Note** The `j`-th entry request evaluates the label `entryLabel ω j`, a function of
the internal randomness only, so entries are independent of the sampled coordinates. A sequence
fixed before sampling is a constant `entryLabel`; fresh uniform labels are independent uniform
coordinates of `ω`. A choice of an unevaluated or already expanded point ends the run. -/
structure LocalExplorer (n d : ℕ) (Ω : Type) where
  entryLabel : Ω → ℕ → Fin n
  policy : Ω → List (ExplObs n d) → ExplAction n

/-- The state of a local exploration: history (oldest first), evaluated labels (the shared cache),
expanded labels, numbers of entry requests and expansions, whether the run is still active, and the
number of distinct evaluated labels at the end of the first operation after which a point of
`Top_k(q)` has been evaluated, if there was one. -/
structure ExplState (n d : ℕ) where
  hist : List (ExplObs n d)
  ev : Finset (Fin n)
  ex : Finset (Fin n)
  entries : ℕ
  expansions : ℕ
  active : Bool
  firstSuccess : Option ℕ

/-- The initial state. -/
def ExplState.init {n d : ℕ} : ExplState n d := ⟨[], ∅, ∅, 0, 0, true, none⟩

open Classical in
/-- The success record after an operation that leaves the evaluated set `ev`: success is recorded
after the first operation whose evaluated points include a member of `Top_k(q)`, with cost the
number of distinct evaluated points through that operation. -/
noncomputable def succUpdate {n d : ℕ} (k : ℕ) (X : Fin n → Sph d) (q : Sph d)
    (old : Option ℕ) (ev : Finset (Fin n)) : Option ℕ :=
  match old with
  | some c => some c
  | none => if ∃ j ∈ ev, IsTarget k X q j then some ev.card else none

open Classical in
/-- One operation of the algorithm on the graph `G` of the sample `X`, with budget `(T, E)`: at
most `T` expansions and `E` entry requests (`⊤` for no budget). An operation that would exceed
the budget ends the run instead. An entry request evaluates its label. An expansion scans and
evaluates the complete list `G(v)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6, and §5.2, p.59). -/
noncomputable def explStep {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) (A : LocalExplorer n d Ω) (ω : Ω) (T E : ℕ∞) (s : ExplState n d) : ExplState n d :=
  if s.active = false then s else
  match A.policy ω s.hist with
  | .stop => { s with active := false }
  | .entry =>
    if E ≤ (s.entries : ℕ∞) then { s with active := false } else
      { hist := s.hist ++ [.entry (A.entryLabel ω s.entries) (X (A.entryLabel ω s.entries))]
        ev := insert (A.entryLabel ω s.entries) s.ev
        ex := s.ex
        entries := s.entries + 1
        expansions := s.expansions
        active := true
        firstSuccess := succUpdate k X q s.firstSuccess (insert (A.entryLabel ω s.entries) s.ev) }
  | .expand v =>
    if v ∉ s.ev ∨ v ∈ s.ex ∨ T ≤ (s.expansions : ℕ∞) then { s with active := false } else
      { hist := s.hist ++ [.expand v (((G v).sort (· ≤ ·)).map (fun j => (j, X j)))]
        ev := s.ev ∪ G v
        ex := insert v s.ex
        entries := s.entries
        expansions := s.expansions + 1
        active := true
        firstSuccess := succUpdate k X q s.firstSuccess (s.ev ∪ G v) }

/-- The state after `t` operations. -/
noncomputable def explRun {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) (A : LocalExplorer n d Ω) (ω : Ω) (T E : ℕ∞) (t : ℕ) : ExplState n d :=
  (explStep G X q k A ω T E)^[t] ExplState.init

/-- The algorithm with budget `(T, E)` succeeds: some operation within the budget evaluates a point
of `Top_k(q)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.59). -/
def explSucceeds {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ)
    (A : LocalExplorer n d Ω) (ω : Ω) (T E : ℕ∞) : Prop :=
  ∃ t, (explRun G X q k A ω T E t).firstSuccess.isSome

/-- The cost `V`: the number of distinct query–data evaluations through the first operation that
evaluates a point of `Top_k(q)`, across all operations (shared cache), and `∞` if no target is
ever evaluated (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.3, p.6, §5.2, p.59, and Theorem 5.9, p.78). -/
noncomputable def explCost {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) (A : LocalExplorer n d Ω) (ω : Ω) (T E : ℕ∞) : ℕ∞ :=
  ⨅ t, match (explRun G X q k A ω T E t).firstSuccess with
    | some c => (c : ℕ∞)
    | none => ⊤

/-- The operation chosen at step `t` of the unbudgeted run (`stop` once the run has ended). -/
noncomputable def explAction {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) (A : LocalExplorer n d Ω) (ω : Ω) (t : ℕ) : ExplAction n :=
  if (explRun G X q k A ω ⊤ ⊤ t).active = true then A.policy ω (explRun G X q k A ω ⊤ ⊤ t).hist
  else .stop

/-- A measurable local exploration algorithm on the graph map `Gf` (`G_ρ` or `N_Δ` of the sample)
for the query `q` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.9, p.78): the entry labels are measurable in the internal
randomness, and the operation chosen at every step is a measurable function of the sample and the
internal randomness.

**Formalization Note** Measurability is required of the induced operations rather than of the
policy on histories; a policy measurable in its history induces measurable operations. -/
def IsMeasurableExplorer {n d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Gf : (Fin n → Sph d) → NavGraph n) (q : Sph d) (k : ℕ) (A : LocalExplorer n d Ω) : Prop :=
  (∀ (j : ℕ) (i : Fin n), MeasurableSet {ω | A.entryLabel ω j = i}) ∧
    ∀ (t : ℕ) (a : ExplAction n),
      MeasurableSet {p : (Fin n → Sph d) × Ω | explAction (Gf p.1) p.1 q k A p.2 t = a}

end Supplement

end GraphNNSphere


