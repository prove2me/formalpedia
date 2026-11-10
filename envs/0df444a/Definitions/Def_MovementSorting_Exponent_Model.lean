-- Prove2me | Definitions.Def_MovementSorting_Exponent_Model
-- name    : MovementSorting_Exponent_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:00:43.454747+00:00
-- url     : https://prove2.me/theorems/c3ca48c7-3846-4c2a-82ca-0f950d7fbc16
-- title:
--   The movement model, M^{(d)}_r and M^{(d)}_∞
-- statement:
--   The movement model of Definition 2.1. Positions are the points of $[m]^d$ (`Pos d m = Fin d → Fin m`, coordinates **0-based**), $n = m^d$ (`nR d m` as a real), and an input is a bijection $\pi$ from positions to the 0-based ranks `Fin (m^d)`. A configuration is a pair of positions (a point of the comparison grid $[m]^{2d}$). A route is a nonempty list of configurations with consecutive $\ell_1$ distance exactly 1; its movement is its length minus one. The outcome at $(x,y)$ is whether $\pi x < \pi y$.
--
--   A deterministic $r$-round algorithm (`DetAlg d m r`) chooses the route of round $t+1$ as a function of the outcome lists of rounds $1,\dots,t$ only, and its output as a function of all $r$ outcome lists. It is well formed when, on every input, every round runs a route that starts at the current configuration (the all-zero start for round 1, else the last configuration of the previous route), and correct when on every input its output is the list of positions in increasing order of rank. `Move` is the sum of the movements of the $r$ routes.
--
--   A randomized algorithm is a probability mass function on valid (well-formed and correct) deterministic $r$-round algorithms, so it is correct for every coin outcome. $M^{(d)}_r(n)$ (`M d r m`) is, in $\mathbb{R}_{\ge 0}\cup\{\infty\}$, the infimum over randomized $r$-round algorithms of the maximum over inputs of the expected movement, and $M^{(d)}_\infty(n)$ (`Minf d m`) is the infimum over $r \ge 1$. The uniform input is the uniform distribution on the $n!$ bijections, and `prob d m E` is the probability of an event under it.
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Definition 2.1, p. 7; uniform input p. 9

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace MovementSorting.Exponent

/-! # The movement model (Wang 2026, Definition 2.1, p. 7)

Keys sit one at each position of the grid `[m]^d`; coordinates are **0-based** (`Fin m`), so the
paper's start position `(1,…,1)` is the all-zero position here. `n = m^d`, and ranks are
**0-based** (`Fin (m^d)`), so the paper's rank `k` is `k - 1` here. -/

/-- A position of the grid `[m]^d` (0-based coordinates). -/
abbrev Pos (d m : ℕ) := Fin d → Fin m

/-- A configuration of the two heads: a point `(x, y)` of the comparison grid `[m]^{2d}`. -/
abbrev Config (d m : ℕ) := Pos d m × Pos d m

/-- An input: a bijection `π : [m]^d → [n]`, `n = m^d`; `π x` is the (0-based) rank of the key
at `x`. -/
abbrev Input (d m : ℕ) := Pos d m ≃ Fin (m ^ d)

/-- `n = m^d` as a real number. -/
noncomputable def nR (d m : ℕ) : ℝ := ((m ^ d : ℕ) : ℝ)

/-- `ℓ1` distance of two positions. -/
def posL1 {d m : ℕ} (x y : Pos d m) : ℕ := ∑ i, Nat.dist (x i).val (y i).val

/-- `ℓ1` distance of two configurations in `[m]^{2d}`. -/
def cfgL1 {d m : ℕ} (z w : Config d m) : ℕ := posL1 z.1 w.1 + posL1 z.2 w.2

/-- The start configuration: both heads at the all-zero position (the paper's `(1,…,1)`). -/
def IsStart {d m : ℕ} (z : Config d m) : Prop := ∀ i, (z.1 i).val = 0 ∧ (z.2 i).val = 0

/-- A route `z_0, …, z_L`: a nonempty list of configurations with consecutive `ℓ1` distance
exactly `1`. -/
def IsRoute {d m : ℕ} (ρ : List (Config d m)) : Prop :=
  ρ ≠ [] ∧ ρ.IsChain (fun z w => cfgL1 z w = 1)

/-- The movement `L` of a route `z_0, …, z_L`. -/
def movement {d m : ℕ} (ρ : List (Config d m)) : ℕ := ρ.length - 1

/-- A route starts at the current configuration; `none` means the heads are still at the start. -/
def StartsAt {d m : ℕ} : Option (Config d m) → List (Config d m) → Prop
  | none, ρ => ∃ z, ρ.head? = some z ∧ IsStart z
  | some z, ρ => ρ.head? = some z

/-- The outcome at a configuration `(x, y)`: whether `rk(x) < rk(y)`. -/
def outcome {d m : ℕ} (π : Input d m) (z : Config d m) : Bool := decide (π z.1 < π z.2)

/-- The outcomes at all configurations of a route, in order. -/
def outcomes {d m : ℕ} (π : Input d m) (ρ : List (Config d m)) : List Bool := ρ.map (outcome π)

/-- A deterministic `r`-round algorithm. `route t h` is the route committed at the start of round
`t + 1` (0-based `t < r`) as a function of the outcome lists `h` of the earlier rounds only;
`output` maps the outcome lists of all `r` rounds to a list of positions. -/
structure DetAlg (d m r : ℕ) where
  route : ℕ → List (List Bool) → List (Config d m)
  output : List (List Bool) → List (Pos d m)

namespace DetAlg

variable {d m r : ℕ}

/-- The outcome lists of the first `t` rounds on input `π`. -/
def history (A : DetAlg d m r) (π : Input d m) : ℕ → List (List Bool)
  | 0 => []
  | t + 1 => A.history π t ++ [outcomes π (A.route t (A.history π t))]

/-- The route run in round `t + 1` (0-based `t`) on input `π`. -/
def runRoute (A : DetAlg d m r) (π : Input d m) (t : ℕ) : List (Config d m) :=
  A.route t (A.history π t)

/-- The list output on input `π`. -/
def result (A : DetAlg d m r) (π : Input d m) : List (Pos d m) := A.output (A.history π r)

/-- On every input, every round runs a route that starts at the current configuration: the
start for round 1, and the last configuration of the previous route afterwards. -/
def WellFormed (A : DetAlg d m r) : Prop :=
  ∀ π : Input d m, ∀ t < r, IsRoute (A.runRoute π t) ∧
    StartsAt (if t = 0 then none else (A.runRoute π (t - 1)).getLast?) (A.runRoute π t)

/-- The positions listed in increasing order of rank. -/
def sortedPositions (π : Input d m) : List (Pos d m) := List.ofFn (fun i : Fin (m ^ d) => π.symm i)

/-- Correct on every input: the output is the list of positions in increasing order of rank. -/
def Correct (A : DetAlg d m r) : Prop := ∀ π : Input d m, A.result π = sortedPositions π

/-- `Move(A, π)`: the total movement over the `r` rounds. -/
def move (A : DetAlg d m r) (π : Input d m) : ℕ := ∑ t ∈ Finset.range r, movement (A.runRoute π t)

end DetAlg

/-- A (deterministic) `r`-round algorithm of the model: well formed and correct on every input. -/
def IsValidAlg {d m r : ℕ} (A : DetAlg d m r) : Prop := A.WellFormed ∧ A.Correct

/-- The valid deterministic `r`-round algorithms. -/
abbrev ValidAlg (d m r : ℕ) := {A : DetAlg d m r // IsValidAlg A}

/-- A randomized `r`-round algorithm: a probability distribution over its coin outcomes, each of
which fixes a valid deterministic algorithm (so it is correct for every outcome of its coins). -/
abbrev RandAlg (d m r : ℕ) := PMF (ValidAlg d m r)

/-- `E[Move(ALG, π)]`, in `ℝ≥0∞`. -/
noncomputable def expMove {d m r : ℕ} (μ : RandAlg d m r) (π : Input d m) : ℝ≥0∞ :=
  ∑' A, μ A * (A.1.move π : ℝ≥0∞)

/-- `M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)]` for `n = m^d`, over randomized `r`-round
algorithms, in `ℝ≥0∞`. -/
noncomputable def M (d r m : ℕ) : ℝ≥0∞ := ⨅ μ : RandAlg d m r, ⨆ π : Input d m, expMove μ π

/-- `M^{(d)}_∞(n) = inf_r M^{(d)}_r(n)` over the finite round numbers `r ≥ 1`. -/
noncomputable def Minf (d m : ℕ) : ℝ≥0∞ := ⨅ r : ℕ, ⨅ (_ : 1 ≤ r), M d r m

instance instNonemptyInput (d m : ℕ) : Nonempty (Input d m) :=
  ⟨Fintype.equivFinOfCardEq (by simp)⟩

/-- The uniform input: `π` uniform among the `n!` bijections. -/
noncomputable def uniformInput (d m : ℕ) : PMF (Input d m) := PMF.uniformOfFintype (Input d m)

/-- Probability of an event over the uniform input. -/
noncomputable def prob (d m : ℕ) (E : Input d m → Prop) : ℝ≥0∞ :=
  (uniformInput d m).toOuterMeasure {π | E π}

end MovementSorting.Exponent


