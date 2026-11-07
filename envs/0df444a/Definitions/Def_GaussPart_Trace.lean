-- Prove2me | Definitions.Def_GaussPart_Trace
-- name    : GaussPart_Trace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:46.727212+00:00
-- url     : https://prove2.me/theorems/baecda0c-ea16-4880-8374-3a5381c0b173
-- title:
--   Traces of Algorithm 1 (GaussianSpacePartition)
-- statement:
--   A **trace** records a run of Algorithm 1 round by round. The partition $\mathcal U_1=\{\mathbb R^d\}$ (one active cell); in round $t$ each cell of $\mathcal U_t$ carries a tag (active, $\mathcal G$, $\mathcal B$, $\mathcal T$, $\mathcal E$), a mass estimate $\hat q_R$, and one action: carry (a terminal cell), low mass ($\hat q_R\le\xi/2$, into $\mathcal B$), certified (finder output None, into $\mathcal G$), rejected (finder Reject, into $\mathcal E$; only if $V_R^\perp\ne\{0\}$), failed (finder direction $v$, a unit vector of $V_R^\perp$, with empirical upper-tail function $\hat F$ satisfying $|\hat F(s)-\bar\Phi(s)|<2g$ for all $s\in[-T,T]$, into $\mathcal E$), or split (direction $v$, a threshold $s\in[-T,T]$ with $|\hat F(s)-\bar\Phi(s)|\ge 2g$, and breakpoints refining the binary split at $s$). Here $\bar\Phi(s)=\Pr_{z\sim N(0,1)}[z\ge s]$. A **refinement** is a strictly increasing list of breakpoints containing $s$, with consecutive gaps at most $\delta_0$, first at most $-T$, last at least $T$, and at most $m$ pieces; the children are the two tails (tagged $\mathcal T$) and the half-open middle pieces (active). $\mathcal U_{t+1}$ is the list of children and carried cells; $A_t$ is the list of cells split in round $t$. The parameters $(L,T,\delta_0,g,\xi,m)$ are the trace's knobs.
--
--   **Formalization Note** The mass estimates, finder outputs and empirical tails are free data; the probabilistic events are hypotheses of the lemmas, as in the wording of Lemma 3.7. A trace is more general than the page in two respects that the analysis does not use: any validated threshold instead of a maximizing one, and any refinement instead of the exact grid of Definition 3.4 (which is one).
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Algorithm 1, p.19 (PDF p.21); Definition 3.4, p.16

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_hellingerSq

open scoped RealInnerProductSpace

namespace GaussPart

/-- The numeric parameters a run of Algorithm 1 uses: the depth `L`, tail cutoff `T`, grid width
`δ₀`, split-validation parameter `g`, mass cutoff `ξ` and refinement size bound `m`. -/
structure Knobs where
  L : ℕ
  T : ℝ
  δ₀ : ℝ
  g : ℝ
  ξ : ℝ
  m : ℕ

/-- The status of a cell of the partition: still active, or in `G`, `B`, `T`, `E` (Algorithm 1). -/
inductive Tag where
  | active | good | bad | tail | err
  deriving DecidableEq

/-- What one round of Algorithm 1 (p.19, PDF p.21) does with one cell of its partition.
* `carry`: a terminal cell is kept unchanged (line 9).
* `lowMass`: mass estimate at most `ξ/2`; into `B` (line 8).
* `certified`: finder output None; into `G` (line 12).
* `rejected`: finder output Reject; into `E` (line 13).
* `failed v F̂`: the finder returned `v`, and no threshold in `[−T, T]` has empirical gap at least
  `2g`; into `E` (line 18).
* `split v F̂ s bp`: the finder returned `v`, the threshold `s` has gap at least `2g`, and the cell is
  refined along `v` at the breakpoints `bp` (lines 20–21).
Here `F̂ : ℝ → ℝ` is the empirical upper tail of `v · x` from the fresh samples of `Q | R`. -/
inductive Action (d : ℕ) where
  | carry
  | lowMass
  | certified
  | rejected
  | failed (v : Vec d) (tailFn : ℝ → ℝ)
  | split (v : Vec d) (tailFn : ℝ → ℝ) (s : ℝ) (bp : List ℝ)

/-- One cell of the partition at one round, its tag, its mass estimate `q̂_R` and what the round
does with it. -/
structure Entry (d : ℕ) where
  cell : Cell d
  tag : Tag
  est : ℝ
  action : Action d

/-- The middle and upper-tail children for breakpoints `a < b < …`, after the lower tail: the piece
`[a, b)` is the constraints `(−v) · x ≤ −a`, `v · x < b` and stays active; the piece `[a, ∞)` is the
constraint `(−v) · x ≤ −a` and is a tail. -/
def upperChildren {d : ℕ} (R : Cell d) (v : Vec d) : ℝ → List ℝ → List (Cell d × Tag)
  | a, [] => [(R ++ [⟨-v, -a, false⟩], Tag.tail)]
  | a, b :: l => (R ++ [⟨-v, -a, false⟩, ⟨v, b, true⟩], Tag.active) :: upperChildren R v b l

/-- The children of `R` refined along `v` at the breakpoints `a₀ < … < a_n`: the tail
`(−∞, a₀)`, the half-open pieces `[a_i, a_{i+1})`, and the tail `[a_n, ∞)`. -/
def refineChildren {d : ℕ} (R : Cell d) (v : Vec d) : List ℝ → List (Cell d × Tag)
  | [] => []
  | a :: l => (R ++ [⟨v, a, true⟩], Tag.tail) :: upperChildren R v a l

/-- The cells an entry contributes to the next partition. -/
def Entry.next {d : ℕ} (e : Entry d) : List (Cell d × Tag) :=
  match e.action with
  | .carry => [(e.cell, e.tag)]
  | .lowMass => [(e.cell, Tag.bad)]
  | .certified => [(e.cell, Tag.good)]
  | .rejected => [(e.cell, Tag.err)]
  | .failed _ _ => [(e.cell, Tag.err)]
  | .split v _ _ bp => refineChildren e.cell v bp

/-- The breakpoints `bp` give a **refinement** of the binary split at `s` (Definition 3.4, p.16,
PDF p.18, of arXiv:2611.05264, sha256 7e0ca6d4…): strictly increasing, containing `s`, with gaps at most `δ₀`,
first at most `−T`, last at least `T`, and at most `m` pieces in total (`bp.length + 1`).

**Formalization Note.** The grid of Definition 3.4 is one such list. The freedom is only in the choice
of grid; the proofs use exactly these properties. -/
structure IsRefinement (K : Knobs) (s : ℝ) (bp : List ℝ) : Prop where
  sorted : bp.Pairwise (· < ·)
  mem : s ∈ bp
  gaps : ∀ i (h : i + 1 < bp.length), bp[i + 1] - bp[i] ≤ K.δ₀
  first : ∃ a, bp.head? = some a ∧ a ≤ -K.T
  last : ∃ a, bp.getLast? = some a ∧ K.T ≤ a
  count : bp.length + 1 ≤ K.m

/-- The rules of Algorithm 1 for one entry. Every non-terminal cell has a mass estimate, compared
with `ξ/2`; a finder direction is a unit vector of `V_R^⊥`; a failed validation has all gaps in
`[−T, T]` below `2g`; a split has a threshold in `[−T, T]` with gap at least `2g`. A cell with
`V_R^⊥ = {0}` is never rejected (line 11). -/
def Entry.Valid {d : ℕ} (K : Knobs) (e : Entry d) : Prop :=
  match e.action with
  | .carry => e.tag ≠ Tag.active
  | .lowMass => e.tag = Tag.active ∧ e.est ≤ K.ξ / 2
  | .certified => e.tag = Tag.active ∧ K.ξ / 2 < e.est
  | .rejected => e.tag = Tag.active ∧ K.ξ / 2 < e.est ∧ (constraintSpace e.cell)ᗮ ≠ ⊥
  | .failed v F =>
      e.tag = Tag.active ∧ K.ξ / 2 < e.est ∧ v ∈ (constraintSpace e.cell)ᗮ ∧ ‖v‖ = 1 ∧
        ∀ s ∈ Set.Icc (-K.T) K.T, |F s - gaussianTail s| < 2 * K.g
  | .split v F s bp =>
      e.tag = Tag.active ∧ K.ξ / 2 < e.est ∧ v ∈ (constraintSpace e.cell)ᗮ ∧ ‖v‖ = 1 ∧
        s ∈ Set.Icc (-K.T) K.T ∧ 2 * K.g ≤ |F s - gaussianTail s| ∧ IsRefinement K s bp

/-- **A trace of Algorithm 1** (GaussianSpacePartition, arXiv:2611.05264, sha256 7e0ca6d4…, p.19,
PDF p.21): `tr t` lists the entries of round `t`, for `t = 1, …, L`.

**Formalization Note.** A trace is the record of a run with the empirical estimates, finder outputs
and empirical tails as free data; the probabilistic events are hypotheses of each lemma, as in the
wording of Lemma 3.7. It covers more than the page: any validated threshold rather than a maximizer,
and any refinement rather than the exact grid. It specializes to Algorithm 1. -/
abbrev Trace (d : ℕ) := ℕ → List (Entry d)

namespace Trace

variable {d : ℕ}

/-- The partition `U_t` with tags: `U_1 = {ℝᵈ}`, and `U_{t+1}` is what round `t` produces. -/
def U (tr : Trace d) : ℕ → List (Cell d × Tag)
  | 0 => []
  | 1 => [([], Tag.active)]
  | t + 2 => (tr (t + 1)).flatMap Entry.next

/-- `tr` is a run of Algorithm 1 through iteration `L`: the parameters are positive, round `t`
processes exactly the cells of `U_t`, and every entry follows the rules. -/
def IsValid (K : Knobs) (tr : Trace d) : Prop :=
  1 ≤ K.L ∧ 0 < K.T ∧ 0 < K.δ₀ ∧ 0 < K.g ∧ 0 < K.ξ ∧ 2 ≤ K.m ∧
  ∀ t, 1 ≤ t → t ≤ K.L →
    (tr t).map (fun e => (e.cell, e.tag)) = tr.U t ∧ ∀ e ∈ tr t, e.Valid K

/-- The cells of `U_t` with a given tag. -/
def tagged (tr : Trace d) (t : ℕ) (τ : Tag) : List (Cell d) :=
  ((tr.U t).filter fun c => c.2 = τ).map Prod.fst

/-- `A_t`, the cells split in round `t` (Lemma 3.7, p.21). -/
def splitCells (tr : Trace d) (t : ℕ) : List (Cell d) :=
  (tr t).filterMap fun e => match e.action with
    | .split _ _ _ _ => some e.cell
    | _ => none

end Trace

end GaussPart


