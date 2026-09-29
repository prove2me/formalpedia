-- Prove2me | Definitions.Def_BSSMachine
-- name    : BSSMachine
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T14:54:02.073719+00:00
-- url     : https://prove2.me/theorems/ba9f90c8-5688-403e-b940-3b589f62fff2
-- title:
--   Machines over an ordered ring (BSS model, §2)
-- statement:
--   The BSS machine model over an ordered ring, from §2 of the paper (pp. 10–13).
--
--   `Rinf R` is $R^\infty$, the countable direct sum of $R$ with itself, realized as finitely
--   supported sequences indexed by $\mathbb{N}$. A `PolyMapInf R` is a polynomial map
--   $R^\infty \to R^\infty$ of some dimension $k$: its first $k$ coordinates are polynomials in the
--   first $k$ coordinates of the argument and every later coordinate is left unchanged. A machine
--   has finitely many nodes, each an output node, a computation node (a polynomial map on the
--   $R^\infty$ part plus an increment-or-reset operation on each of the two index registers), a
--   branch node (a polynomial in the first $k$ coordinates, with the negative branch taken when its
--   value is $< 0$), or a fifth node (copy the entry at the index in register $i$ into the position
--   named by register $j$). The state space is
--   $\mathbb{Z}^{+} \times \mathbb{Z}^{+} \times R^\infty$.
--
--   On input $y$ the machine starts at its entry node with both registers at the first index, the
--   length of $y$ in coordinate $0$ and $y$ in coordinates $1, 2, \dots$. The output node is a fixed
--   point of the step map, so a halted computation stays halted. `haltingTime` is the least step
--   count at which the output node is reached, `output` is the $R^\infty$ part of the state there
--   (the natural projection of the normal form of §3), and `outputVal` its coordinate $0$, the
--   answer slot used by decision machines. A set is R.E. over $R$ when it is some machine's halting
--   set, and decidable when it and its complement both are.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §2, pp. 10-13; §3, p. 15

import Mathlib

/-!
# Machines over an ordered ring (Blum–Shub–Smale, §2)

Formalization of the machine model of

  L. Blum, M. Shub, S. Smale, *On a theory of computation and complexity over the
  real numbers: NP-completeness, recursive functions and universal machines*,
  Bull. Amer. Math. Soc. **21** (1989), no. 1, 1–46, §2 (pp. 10–13).

The machine is presented in the normal form of §3 (p. 15): a single input node,
which is folded into the initial configuration, and a single kind of output node,
whose associated output map is the natural projection onto the `R^∞` part of the
state.
-/

namespace BSS

/-- `R^∞`, the countable direct sum of `R` with itself: sequences `x₀, x₁, …` of
elements of `R` with `xₖ = 0` for all sufficiently large `k`. -/
abbrev Rinf (R : Type) [CommRing R] := ℕ →₀ R

/-- The two operations a computation node may perform on an index register:
increment it, or reset it to the first index (BSS §2, p. 12: `i'(i,j) = i+1` or `1`). -/
inductive ShiftOp : Type
  | inc : ShiftOp
  | reset : ShiftOp
  deriving DecidableEq

/-- The action of a shift operation on an index register. Registers are `0`-based,
so `reset` returns to index `0`. -/
def ShiftOp.apply : ShiftOp → ℕ → ℕ
  | ShiftOp.inc, i => i + 1
  | ShiftOp.reset, _ => 0

/-- A polynomial map `R^∞ → R^∞` of dimension `dim` (BSS §2, p. 10): the first
`dim` coordinates of the value are polynomials in the first `dim` coordinates of
the argument, and all further coordinates are left unchanged. -/
structure PolyMapInf (R : Type) [CommRing R] : Type where
  /-- The number of active variables and coordinates of the map. -/
  dim : ℕ
  /-- The polynomial computing each active coordinate. -/
  coord : Fin dim → MvPolynomial (Fin dim) R

/-- The map `R^∞ → R^∞` determined by a `PolyMapInf`. -/
noncomputable def PolyMapInf.eval {R : Type} [CommRing R]
    (g : PolyMapInf R) (x : Rinf R) : Rinf R :=
  Finsupp.onFinset (α := ℕ) (M := R) (x.support ∪ Finset.range g.dim)
    (fun i : ℕ => if h : i < g.dim then
        MvPolynomial.eval (fun j : Fin g.dim => x (j : ℕ)) (g.coord ⟨i, h⟩)
      else x i)
    (by
      intro a ha
      by_cases h : a < g.dim
      · exact Finset.mem_union_right _ (Finset.mem_range.mpr h)
      · simp only [dif_neg h] at ha
        exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr ha))

/-- The value of a branch node's test polynomial at a state (BSS §2, p. 11:
`hₙ : S → R` depends on the first `k` coordinates only). -/
noncomputable def branchValue {R : Type} [CommRing R] {k : ℕ}
    (h : MvPolynomial (Fin k) R) (x : Rinf R) : R :=
  MvPolynomial.eval (fun j : Fin k => x (j : ℕ)) h

/-- The nodes of a machine with `N` nodes (BSS §2, pp. 11–12). The input node of
the paper is folded into the initial configuration, so it does not appear here. -/
inductive Node (R : Type) [CommRing R] (N : ℕ) : Type
  /-- An output node: no outgoing edge; the computation halts here. -/
  | output : Node R N
  /-- A computation node: applies a polynomial map to the `R^∞` part of the state
  and a shift operation to each of the two index registers. -/
  | computation (g : PolyMapInf R) (iOp jOp : ShiftOp) (next : Fin N) : Node R N
  /-- A branch node: goes to `negNext` when the test polynomial is negative at the
  state, and to `posNext` otherwise. -/
  | branch (k : ℕ) (h : MvPolynomial (Fin k) R) (negNext posNext : Fin N) : Node R N
  /-- A fifth node: copies the entry at the index held in the first register into
  the position held in the second register (BSS §2, p. 12). -/
  | fifth (next : Fin N) : Node R N

/-- The output nodes. -/
def Node.IsOutput {R : Type} [CommRing R] {N : ℕ} : Node R N → Prop
  | Node.output => True
  | Node.computation _ _ _ _ => False
  | Node.branch _ _ _ _ => False
  | Node.fifth _ => False

/-- A machine over `R`: finitely many nodes, together with the node at which the
computation starts (the successor of the paper's input node). -/
structure Machine (R : Type) [CommRing R] : Type where
  /-- The number of nodes. -/
  numNodes : ℕ
  /-- The node carried by each label. -/
  nodes : Fin numNodes → Node R numNodes
  /-- The node the computation enters after the input map is applied. -/
  entry : Fin numNodes

/-- The state space `S = ℤ⁺ + ℤ⁺ + R^∞` of a machine (BSS §2, p. 12): two index
registers together with a point of `R^∞`. -/
abbrev State (R : Type) [CommRing R] := ℕ × ℕ × Rinf R

/-- The length of `x ∈ R^∞`: the largest index carrying a nonzero entry, plus one.
The length of `0` is `1` (BSS §2, p. 12; §5, p. 23). -/
noncomputable def lengthInf {R : Type} [CommRing R] (x : Rinf R) : ℕ :=
  if h : x.support.Nonempty then x.support.max' h + 1 else 1

/-- Shift `y ∈ R^∞` up by one coordinate and insert `v` in coordinate `0`. -/
noncomputable def consInf {R : Type} [CommRing R] (v : R) (y : Rinf R) : Rinf R :=
  Finsupp.onFinset (α := ℕ) (M := R) (insert 0 (y.support.image (fun k : ℕ => k + 1)))
    (fun i : ℕ => if i = 0 then v else y (i - 1))
    (by
      intro a ha
      by_cases h : a = 0
      · subst h
        exact Finset.mem_insert_self 0 _
      · simp only [if_neg h] at ha
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a - 1, ?_, ?_⟩)
        · exact Finsupp.mem_support_iff.mpr ha
        · omega)

/-- The state a machine over `R` starts from on input `y ∈ R^∞`: both index
registers hold the first index, coordinate `0` of the working space holds the
length of `y`, and `y` itself is placed in coordinates `1, 2, …`
(BSS §2, p. 12: the input map records the length of the input and leaves working
space). -/
noncomputable def inputState {R : Type} [CommRing R] (y : Rinf R) : State R :=
  (0, 0, consInf ((lengthInf y : ℕ) : R) y)

/-- A configuration of `M`: the current node together with the current state. -/
abbrev Machine.Config {R : Type} [CommRing R] (M : Machine R) : Type :=
  Fin M.numNodes × State R

/-- One step of the computation of `M`. An output node is a fixed point. -/
noncomputable def Machine.step {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (c : M.Config) : M.Config :=
  match M.nodes c.1 with
  | Node.output => c
  | Node.computation g iOp jOp next =>
      (next, iOp.apply c.2.1, jOp.apply c.2.2.1, g.eval c.2.2.2)
  | Node.branch _ h negNext posNext =>
      (if branchValue h c.2.2.2 < 0 then negNext else posNext, c.2)
  | Node.fifth next =>
      (next, c.2.1, c.2.2.1, c.2.2.2.update c.2.2.1 (c.2.2.2 c.2.1))

/-- The configuration of `M` after `T` steps on input `y`. -/
noncomputable def Machine.run {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) (T : ℕ) : M.Config :=
  M.step^[T] (M.entry, inputState y)

/-- `M` has reached an output node on input `y` within exactly `T` steps. -/
def Machine.HaltsBy {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) (T : ℕ) : Prop :=
  (M.nodes (M.run y T).1).IsOutput

/-- The halting set `Ω_M` of `M` (BSS §2, p. 12). -/
def Machine.Halts {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) : Prop :=
  ∃ T : ℕ, M.HaltsBy y T

/-- The halting time `T_M(y)`: the least `T` with `nT = N` (BSS §4, p. 19).
It is `0` when `M` does not halt on `y`. -/
noncomputable def Machine.haltingTime {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) : ℕ :=
  sInf {T : ℕ | M.HaltsBy y T}

/-- The value `φ_M(y)` output by `M` on input `y`: the `R^∞` part of the halting
state, the output map being the natural projection (BSS §3, p. 15, normal form). -/
noncomputable def Machine.output {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) : Rinf R :=
  (M.run y (M.haltingTime y)).2.2.2

/-- The first coordinate of the output, used for the answers `1` (yes) and `0` (no)
of a decision machine (BSS §5, p. 25). -/
noncomputable def Machine.outputVal {R : Type} [CommRing R] [LinearOrder R]
    (M : Machine R) (y : Rinf R) : R :=
  M.output y 0

/-- A set is R.E. over `R` when it is the halting set of a machine over `R`
(BSS §2, p. 13). -/
def IsREOver (R : Type) [CommRing R] [LinearOrder R] (S : Set (Rinf R)) : Prop :=
  ∃ M : Machine R, {y : Rinf R | M.Halts y} = S

/-- A set is decidable over `R` when it and its complement are both R.E. over `R`
(BSS §2, p. 13). -/
def IsDecidableOver (R : Type) [CommRing R] [LinearOrder R] (S : Set (Rinf R)) : Prop :=
  IsREOver R S ∧ IsREOver R Sᶜ

end BSS


