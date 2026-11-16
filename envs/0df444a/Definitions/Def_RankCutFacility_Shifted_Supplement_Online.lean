-- Prove2me | Definitions.Def_RankCutFacility_Shifted_Supplement_Online
-- name    : RankCutFacility_Shifted_Supplement_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:20:43.066423+00:00
-- url     : https://prove2.me/theorems/5df361c2-c6c1-4459-9ed7-105e91f24c58
-- title:
--   Arbitrary online facility-location algorithms and the lower-bound instance of Section 6
-- statement:
--   An instance consists of points $P$ with a distance $d$, candidates $Y$ with locations in $P$ and opening costs $f_y$. A **deterministic online algorithm** maps every revealed request prefix (current request last) to the finite set of candidates it opens in that round; it may open several at once, and the same map is used whatever the number of requests, so it is horizon-free unless the instance fixes the horizon. With $O_t$ the set opened through round $t$ and $d(x,\emptyset)=+\infty$, its cost is
--
--   $$\mathrm{ALG}=\sum_{y\in O_n}f_y+\sum_{t=1}^n d(v_t,O_t)\in[0,\infty].$$
--
--   A **randomized online algorithm** is a probability distribution over deterministic ones. Expectations average over the uniformly random order of the labeled demand copies and the algorithm's randomness. The offline optimum minimizes opening plus connection cost over nonempty facility sets.
--
--   The **lower-bound instance** of Section 6.1: for $N\ge2$ let $m=2N(N-1)$, $X=\{x_1,\dots,x_m\}$ and $Y=\{y_I: I\subseteq[m],|I|=N\}$, with $d(x_i,x_j)=2/3$ $(i\ne j)$, $d(y_I,y_{I'})=2/3$ $(I\ne I')$, $d(x_i,y_I)=1/3$ if $i\in I$ and $1$ otherwise. The candidates are $Y$ with unit costs; in the full-space variant of Section 6.4 every point is a candidate, with $f_{y_I}=1$ and $f_{x_i}=1+N/3$. A round with demand $x_i$ is **covered** if after its openings some open $y_I$ has $i\in I$; $C$ counts covered rounds and $K$ distinct opened facilities. The i.i.d. experiment draws $N$ demand locations independently and uniformly from $X$.
--
--   **Formalization Note** The distance is a plain function; that it is a metric is Lemma 6.2, a separate theorem.
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Section 2 model (printed p. 6, PDF p. 8), Section 6.1–6.2 (printed p. 19, PDF p. 21), Section 6.4 (printed p. 21, PDF p. 23), Appendix D (printed p. 36, PDF p. 38)

import Definitions.Def_RankCutFacility_Shifted_Model

noncomputable section
open scoped BigOperators ENNReal

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-! ### Arbitrary online facility-location algorithms on a fixed instance

An instance is a point type `P` with a distance function `d`, a candidate type `Y` with its
location map `site : Y → P`, and opening costs `f : Y → ℝ`. -/

/-- A deterministic online algorithm: the revealed request prefix (current request last) ↦ the
candidates it opens in that round. It may open several candidates in one round. -/
abbrev OnlineAlg (Y P : Type*) := List P → Finset Y

variable {Y P : Type*}

/-- `O_t`: everything opened in rounds `1, …, t` on the request list `vs`. -/
def openedBy [DecidableEq Y] (A : OnlineAlg Y P) (vs : List P) (t : ℕ) : Finset Y :=
  (Finset.range t).biUnion (fun s => A (vs.take (s + 1)))

/-- `d(x, O)` in `[0, ∞]`, with `d(x, ∅) = +∞`. -/
def openDist (d : P → P → ℝ) (site : Y → P) (O : Finset Y) (x : P) : ℝ≥0∞ :=
  ⨅ y ∈ O, ENNReal.ofReal (d x (site y))

/-- `ALG = Σ_{y ∈ O_n} f_y + Σ_t d(v_t, O_t)` (infinite if some `O_t` is empty). -/
def onlineCost [DecidableEq Y] (d : P → P → ℝ) (site : Y → P) (f : Y → ℝ)
    (A : OnlineAlg Y P) (vs : List P) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ y ∈ openedBy A vs vs.length, f y) +
    ∑ t : Fin vs.length, openDist d site (openedBy A vs ((t : ℕ) + 1)) vs[t]

/-- The arrival sequence of the labeled copies `u` in the order `π`. -/
def orderedStream {n : ℕ} (u : Fin n → P) (π : Arrival n) : List P := List.ofFn (fun i => u (π i))

/-- Random-order expected cost of a deterministic algorithm. -/
def detExpected [DecidableEq Y] (d : P → P → ℝ) (site : Y → P) (f : Y → ℝ)
    (A : OnlineAlg Y P) {n : ℕ} (u : Fin n → P) : ℝ≥0∞ :=
  (∑ π : Arrival n, onlineCost d site f A (orderedStream u π)) / (Fintype.card (Arrival n) : ℝ≥0∞)

/-- Random-order expected cost of a randomized algorithm, a distribution `ρ` over deterministic
ones, independent of the arrival order. -/
def randExpected [DecidableEq Y] (d : P → P → ℝ) (site : Y → P) (f : Y → ℝ)
    (ρ : PMF (OnlineAlg Y P)) {n : ℕ} (u : Fin n → P) : ℝ≥0∞ :=
  ∑' A, ρ A * detExpected d site f A u

/-- The true offline optimum over nonempty facility sets. -/
def offlineOpt [Fintype Y] (d : P → P → ℝ) (site : Y → P) (f : Y → ℝ) {n : ℕ}
    (u : Fin n → P) : ℝ :=
  sInf {v | ∃ O : Finset Y, O.Nonempty ∧
    v = ∑ y ∈ O, f y + ∑ i, sInf ((fun y => d (u i) (site y)) '' (O : Set Y))}

/-! ### The lower-bound instance of Section 6.1 and its full-space variant (Section 6.4) -/

/-- `m = 2N(N-1)` demand locations `x_1, …, x_m`. -/
def lbM (N : ℕ) : ℕ := 2 * N * (N - 1)

/-- Facilities `y_I`, one for every `N`-element index set `I ⊆ [m]`. -/
abbrev LBFac (N : ℕ) := {I : Finset (Fin (lbM N)) // I.card = N}

/-- The point set `X ∪ Y`. -/
abbrev LBPoint (N : ℕ) := Fin (lbM N) ⊕ LBFac N

/-- `d(x_i,x_j) = 2/3` (`i ≠ j`), `d(y_I,y_I') = 2/3` (`I ≠ I'`), `d(x_i,y_I) = 1/3` if `i ∈ I`
and `1` otherwise, `d(z,z) = 0`, symmetric. -/
def lbDist (N : ℕ) : LBPoint N → LBPoint N → ℝ
  | .inl i, .inl j => if i = j then 0 else 2 / 3
  | .inr I, .inr J => if I = J then 0 else 2 / 3
  | .inl i, .inr I => if i ∈ I.1 then 1 / 3 else 1
  | .inr I, .inl i => if i ∈ I.1 then 1 / 3 else 1

/-- Candidate set `Y` of the prescribed-candidate instance. -/
def lbSite (N : ℕ) : LBFac N → LBPoint N := Sum.inr

/-- Every candidate `y_I` has opening cost one. -/
def lbUnitFee (N : ℕ) : LBFac N → ℝ := fun _ => 1

/-- Full-space costs: `f_{y_I} = 1`, `f_{x_i} = 1 + N/3`. -/
def lbFullFee (N : ℕ) : LBPoint N → ℝ
  | .inl _ => 1 + (N : ℝ) / 3
  | .inr _ => 1

/-- Demand locations `x_{w_1}, …, x_{w_N}` in this order. -/
def lbDemand {N : ℕ} (w : Fin N → Fin (lbM N)) : List (LBPoint N) :=
  List.ofFn (fun i => Sum.inl (w i))

/-- `C`: rounds whose demand `x_i` is covered, after that round's openings, by an open `y_I`
with `i ∈ I`. -/
def coveredRounds {N : ℕ} (A : OnlineAlg (LBFac N) (LBPoint N)) (w : Fin N → Fin (lbM N)) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun t : Fin N => ∃ I ∈ openedBy A (lbDemand w) ((t : ℕ) + 1), w t ∈ I.1)).card

/-- `K`: number of distinct facilities opened. -/
def openedCount {N : ℕ} (A : OnlineAlg (LBFac N) (LBPoint N)) (w : Fin N → Fin (lbM N)) : ℕ := by
  classical
  exact (openedBy A (lbDemand w) N).card

/-- Expectation in the i.i.d. experiment: `N` independent uniform draws from `X`, independent of
the algorithm's randomness `ρ`. -/
def iidExpected {N : ℕ} (ρ : PMF (OnlineAlg (LBFac N) (LBPoint N)))
    (F : OnlineAlg (LBFac N) (LBPoint N) → (Fin N → Fin (lbM N)) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' A, ρ A * ((∑ w : Fin N → Fin (lbM N), F A w) /
    (Fintype.card (Fin N → Fin (lbM N)) : ℝ≥0∞))

end RankCutFacility.Shifted.Supplement


