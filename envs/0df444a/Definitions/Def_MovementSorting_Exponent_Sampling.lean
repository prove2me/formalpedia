-- Prove2me | Definitions.Def_MovementSorting_Exponent_Sampling
-- name    : MovementSorting_Exponent_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:30.897518+00:00
-- url     : https://prove2.me/theorems/500b877a-5e65-459a-a982-7455e4f7c625
-- title:
--   The sampling algorithm template (Algorithm 1): state, required configurations, coins
-- statement:
--   Algorithm 1 as a template. The state between rounds is the list, in rank order, of resolved keys and segments, computed from the comparisons observed so far. Round 1 chooses $\lceil n/b_0\rceil$ splitters uniformly without replacement; its required configurations are all $(u,v)$ with $u \ne v$ and $v$ a splitter, and the splitters then cut the other positions into segments. A refinement round draws its samples independently: a sample is a partition of $[m]^d$ into boxes and a rate $p$, each box selected independently with probability $p$, and the keys of selected boxes lying in segments are the pivots. Its required configurations are all $(u,v)$ with $u \ne v$ and $v$ a pivot in the segment of $u$, and each segment is then split by its pivots into resolved keys and the nonempty maximal pivot-free sets of consecutive ranks. The cleanup requires one fixed orientation of every cell inside a segment, and the output sorts each segment and lists resolved keys and segments in rank order (Line 10).
--
--   A run with its coins fixed (`Template`) carries a route procedure for every round: a function from the current configuration and the state to a route. `Template.RoutesValid` requires every such route to start at the current configuration and to visit every required configuration of its round. `Plan` records the number of rounds, the number of splitters and the samples of each refinement round; `Plan.coins` is the coin distribution, `Plan.alg` the deterministic algorithm fixed by a coin outcome and `Plan.expMove` its expected movement. `Qbox` is $Q_{I,J} = \sum_G |G\cap I||G\cap J|$ over the segments, `occupied` the product boxes with $Q_{I,J} > 0$, and `productCount W box` the number of product boxes containing a configuration of $W$.
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Algorithm 1 and Section 5.3, pp. 25–27

import Definitions.Def_MovementSorting_Exponent_Model

set_option autoImplicit false

open scoped ENNReal

namespace MovementSorting.Exponent

/-! # The sampling algorithm template (Wang 2026, Algorithm 1 and §5.3, pp. 25–27)

Between rounds the algorithm knows a *state*: the resolved keys and the segments, in rank order.
The state is computed from the outcomes observed so far. Round 1 picks the splitters; each
refinement round turns the keys of its samples' selected boxes that lie in segments into pivots;
the cleanup compares one fixed orientation of every cell inside a segment. Algorithm 1 is a
template whose route procedures are parameters (p. 25): here a route procedure is any function
from the current configuration and the state to a route, and `Template.RoutesValid` requires it to
start at the current configuration and visit every required configuration. -/

/-- A piece of the state: `(true, {v})` a resolved key, `(false, G)` a segment `G`. -/
abbrev Piece (d m : ℕ) := Bool × Finset (Pos d m)

/-- The state: the pieces in rank order. -/
abbrev State (d m : ℕ) := List (Piece d m)

/-- The comparisons observed so far: each visited configuration with its outcome. -/
abbrev Table (d m : ℕ) := List (Config d m × Bool)

/-- `x` is known to rank below `y` from an observed outcome at `(x, y)` or at `(y, x)`. -/
def obsLess {d m : ℕ} (T : Table d m) (x y : Pos d m) : Bool :=
  decide (x ≠ y) &&
    T.any (fun e => (decide (e.1 = (x, y)) && e.2) || (decide (e.1 = (y, x)) && !e.2))

/-- The number of keys of `P` known to rank below `u`. -/
def countBelow {d m : ℕ} (T : Table d m) (P : Finset (Pos d m)) (u : Pos d m) : ℕ :=
  (P.filter (fun v => obsLess T v u = true)).card

/-- Splitting a segment `G` by its pivots `P ⊆ G`: the pivots become resolved keys, and the
nonempty maximal pivot-free sets of consecutive ranks become segments, all in rank order. -/
def splitSeg {d m : ℕ} (T : Table d m) (G P : Finset (Pos d m)) : State d m :=
  ((List.range (P.card + 1)).flatMap (fun k =>
    [((false : Bool), (G \ P).filter (fun u => countBelow T P u = k)),
     ((true : Bool), P.filter (fun v => countBelow T P v = k))])).filter
    (fun pc => decide pc.2.Nonempty)

/-- The state after a round whose pivot candidates are `cand`: each segment is split by the
candidates it contains; resolved keys stay. -/
def refineState {d m : ℕ} (T : Table d m) (cand : Finset (Pos d m)) (st : State d m) :
    State d m :=
  st.flatMap (fun pc => if pc.1 then [pc] else splitSeg T pc.2 (pc.2 ∩ cand))

/-- The segments of a state. -/
def segments {d m : ℕ} (st : State d m) : List (Finset (Pos d m)) :=
  (st.filter (fun pc => !pc.1)).map Prod.snd

/-- Required configurations of the splitter or a refinement round: all `(u, v)` with `u ≠ v` and
`v` a pivot (candidate) in the segment of `u`. -/
def refineReq {d m : ℕ} (cand : Finset (Pos d m)) (st : State d m) : Finset (Config d m) :=
  Finset.univ.filter (fun z => z.1 ≠ z.2 ∧ ∃ G ∈ segments st, z.1 ∈ G ∧ z.2 ∈ G ∧ z.2 ∈ cand)

/-- A fixed injective index of positions, used to fix one orientation of each cell. -/
def posIndex {d m : ℕ} (x : Pos d m) : ℕ := ∑ i, (x i : ℕ) * m ^ (i : ℕ)

/-- Required configurations of the cleanup: one fixed orientation `(u, v)`
(`posIndex u < posIndex v`) of every cell whose two positions lie in one segment. -/
def cleanupReq {d m : ℕ} (st : State d m) : Finset (Config d m) :=
  Finset.univ.filter (fun z => posIndex z.1 < posIndex z.2 ∧ ∃ G ∈ segments st, z.1 ∈ G ∧ z.2 ∈ G)

/-- The keys of a piece in the order given by the observed comparisons. -/
noncomputable def sortPiece {d m : ℕ} (T : Table d m) (G : Finset (Pos d m)) : List (Pos d m) :=
  (List.range G.card).flatMap (fun k => (G.filter (fun u => countBelow T G u = k)).toList)

/-- Line 10: sort each segment and output the resolved keys and segments in rank order. -/
noncomputable def outputOf {d m : ℕ} (T : Table d m) (st : State d m) : List (Pos d m) :=
  st.flatMap (fun pc => sortPiece T pc.2)

/-- A route procedure: from the current configuration (`none` = the start) and the state, a
route. -/
abbrev RouteProc (d m : ℕ) := Option (Config d m) → State d m → List (Config d m)

/-- One run of Algorithm 1 with its coins fixed: the splitters, the pivot candidates `cand t` of
refinement round `t + 1` (`1 ≤ t ≤ r - 2`, the union of the selected boxes of that round's
samples), and the route procedure of every round (0-based `t`). -/
structure Template (d m : ℕ) where
  splitters : Finset (Pos d m)
  cand : ℕ → Finset (Pos d m)
  proc : ℕ → RouteProc d m

/-- What the algorithm knows before a round: the state, the observed comparisons, and the current
configuration. -/
structure Snap (d m : ℕ) where
  st : State d m
  tbl : Table d m
  cur : Option (Config d m)

namespace Template

variable {d m : ℕ}

/-- The pivot candidates of round `t + 1` (0-based `t`): the splitters for `t = 0`. -/
def candAt (T : Template d m) (t : ℕ) : Finset (Pos d m) := if t = 0 then T.splitters else T.cand t

/-- The required configurations of round `t + 1` of an `r`-round run. -/
def reqAt (T : Template d m) (r t : ℕ) (st : State d m) : Finset (Config d m) :=
  if t + 1 = r then cleanupReq st else refineReq (T.candAt t) st

/-- The knowledge before round `t + 1`, computed from the outcome lists `h` of earlier rounds. -/
def snap (T : Template d m) (h : List (List Bool)) : ℕ → Snap d m
  | 0 => ⟨[((false : Bool), Finset.univ)], [], none⟩
  | t + 1 =>
    let s := T.snap h t
    let ρ := T.proc t s.cur s.st
    let tbl := s.tbl ++ ρ.zip (h.getD t [])
    ⟨refineState tbl (T.candAt t) s.st, tbl, ρ.getLast?⟩

/-- The deterministic `r`-round algorithm of the run: rounds `0` (splitter), `1, …, r-2`
(refinement), `r - 1` (cleanup), then Line 10. -/
noncomputable def toAlg (T : Template d m) (r : ℕ) : DetAlg d m r where
  route t h := T.proc t (T.snap h t).cur (T.snap h t).st
  output h := outputOf (T.snap h r).tbl (T.snap h (r - 1)).st

/-- Every route procedure returns a route from the current configuration that visits every
required configuration of its round, whatever the state. -/
def RoutesValid (T : Template d m) (r : ℕ) : Prop :=
  ∀ t < r, ∀ (cur : Option (Config d m)) (st : State d m),
    IsRoute (T.proc t cur st) ∧ StartsAt cur (T.proc t cur st) ∧
    ∀ z ∈ T.reqAt r t st, z ∈ T.proc t cur st

end Template

/-- A sample: a partition of `[m]^d` into boxes, given by the index of the box of each position,
and a rate `p`. -/
structure Sample (d m : ℕ) where
  box : Pos d m → (Fin d → ℕ)
  rate : ℝ

/-- The boxes of a partition. -/
def boxes {d m : ℕ} (box : Pos d m → (Fin d → ℕ)) : Finset (Fin d → ℕ) := Finset.univ.image box

/-- A rate as a probability (rates of the instances lie in `(0, 1]`; `min 1` only makes the
definition total). -/
noncomputable def clampProb (p : ℝ) : ℝ≥0∞ := ENNReal.ofReal (min 1 p)

/-- A coin with `Pr[true] = p`. -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then clampProb p else 1 - clampProb p) (by
    have h : clampProb p ≤ 1 := ENNReal.ofReal_le_one.mpr (min_le_left _ _)
    simp [Fintype.sum_bool, add_tsub_cancel_of_le h])

/-- Select each element of a list independently with probability `p`. -/
noncomputable def bernoulliOn {α : Type} [DecidableEq α] (p : ℝ) : List α → PMF (Finset α)
  | [] => PMF.pure ∅
  | a :: l => (bernoulliOn p l).bind (fun S => (coin p).map (fun b => if b then insert a S else S))

/-- Drawing a sample: each box selected independently with probability `rate`. -/
noncomputable def drawSample {d m : ℕ} (s : Sample d m) : PMF (Finset (Fin d → ℕ)) :=
  bernoulliOn s.rate (boxes s.box).toList

/-- The positions in the selected boxes of a sample. -/
def selectedPositions {d m : ℕ} (s : Sample d m) (sel : Finset (Fin d → ℕ)) : Finset (Pos d m) :=
  Finset.univ.filter (fun x => s.box x ∈ sel)

/-- Independent draws, one per list entry. -/
noncomputable def drawAll {α β : Type} (f : α → PMF β) : List α → PMF (List β)
  | [] => PMF.pure []
  | a :: l => (f a).bind (fun b => (drawAll f l).map (fun bs => b :: bs))

/-- `s` positions chosen uniformly at random without replacement. -/
noncomputable def uniformSubset (d m s : ℕ) : PMF (Finset (Pos d m)) :=
  if h : s ≤ Fintype.card (Pos d m) then
    PMF.uniformOfFinset (Finset.univ.powersetCard s)
      (Finset.powersetCard_nonempty.mpr (by simpa [Finset.card_univ] using h))
  else PMF.pure Finset.univ

/-- The coin outcomes of a run: the splitters, and for each refinement round `t = 1, …, r - 2`
(entry `t - 1`) the selected boxes of each of its samples. -/
abbrev Coins (d m : ℕ) := Finset (Pos d m) × List (List (Finset (Fin d → ℕ)))

/-- The sampling plan of an instance of Algorithm 1: the number of rounds, the number of
splitters, and the samples of refinement round `t` (`1 ≤ t ≤ r - 2`). -/
structure Plan (d m : ℕ) where
  rounds : ℕ
  splitterCount : ℕ
  samples : ℕ → List (Sample d m)

namespace Plan

variable {d m : ℕ}

/-- The coin distribution: uniform splitters, then the samples of every refinement round, all
independent. -/
noncomputable def coins (P : Plan d m) : PMF (Coins d m) :=
  (uniformSubset d m P.splitterCount).bind (fun S =>
    (drawAll (fun t => drawAll drawSample (P.samples t))
      ((List.range (P.rounds - 2)).map (· + 1))).map (fun sels => (S, sels)))

/-- The selected boxes of sample `k` of refinement round `t` under the coins `ω`. -/
def selOf (ω : Coins d m) (t k : ℕ) : Finset (Fin d → ℕ) := (ω.2.getD (t - 1) []).getD k ∅

/-- The pivot candidates of refinement round `t`: the union over its samples of the selected
positions. -/
def candOf (P : Plan d m) (ω : Coins d m) (t : ℕ) : Finset (Pos d m) :=
  ((P.samples t).zip (ω.2.getD (t - 1) [])).foldr
    (fun sk acc => selectedPositions sk.1 sk.2 ∪ acc) ∅

/-- The run of Algorithm 1 under the coins `ω` with route procedures `procs ω t`. -/
def template (P : Plan d m) (procs : Coins d m → ℕ → RouteProc d m) (ω : Coins d m) :
    Template d m :=
  ⟨ω.1, P.candOf ω, procs ω⟩

/-- The deterministic algorithm fixed by the coins `ω`. -/
noncomputable def alg (P : Plan d m) (procs : Coins d m → ℕ → RouteProc d m) (ω : Coins d m) :
    DetAlg d m P.rounds :=
  (P.template procs ω).toAlg P.rounds

/-- `E[Move]` over the coins, on input `π`. -/
noncomputable def expMove (P : Plan d m) (procs : Coins d m → ℕ → RouteProc d m)
    (π : Input d m) : ℝ≥0∞ :=
  ∑' ω, P.coins ω * ((P.alg procs ω).move π : ℝ≥0∞)

end Plan

/-- `Q_{I,J} = Σ_G |G ∩ I| |G ∩ J|` over the segments `G` of a state, for boxes `I, J` of a
partition. -/
def Qbox {d m : ℕ} (st : State d m) (box : Pos d m → (Fin d → ℕ)) (I J : Fin d → ℕ) : ℕ :=
  ((segments st).map (fun G =>
    (G.filter (fun x => box x = I)).card * (G.filter (fun x => box x = J)).card)).sum

/-- The occupied product boxes `I × J` (`Q_{I,J} > 0`). -/
def occupied {d m : ℕ} (st : State d m) (box : Pos d m → (Fin d → ℕ)) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ)) :=
  (boxes box ×ˢ boxes box).filter (fun IJ => 0 < Qbox st box IJ.1 IJ.2)

/-- `N(W)`: the number of product boxes `I × J` of a partition containing a configuration of `W`. -/
def productCount {d m : ℕ} (W : Finset (Config d m)) (box : Pos d m → (Fin d → ℕ)) : ℕ :=
  (W.image (fun z => (box z.1, box z.2))).card

end MovementSorting.Exponent


