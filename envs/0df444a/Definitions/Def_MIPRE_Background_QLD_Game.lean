-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Game
-- name    : MIPRE_Background_QLD_Game
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:09.5978+00:00
-- url     : https://prove2.me/theorems/565a96f4-6e45-4a2a-b545-1517bc83d403
-- title:
--   Definitions of Game: The Pauli basis test Blueprint `def:qld-game`, the paper's game `game^pauli_{(q,m,d)}` (`ldt.tex`, `sec:qld-game` for…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Game` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Pauli basis test. Blueprint `def:qld-game`, the paper's game `game^pauli_{(q,m,d)}` (`ldt.tex`, `sec:qld-game` for the question distribution and `fig:decider_pauli` for the decision procedure). This is the game `thm:qld` is about and `lem:qld-win` unpacks. The test certifies that the players share `|EPR_q⟩^{⊗ M}`, `M = 2^m`. A player asked `(Pauli, W)` measures `{τ^W_h}_{h ∈ F_q^M}` and reports `h`; every other question probes limited information about `h` through its low-degree encoding `g_h : F_q^m → F_q` (`MIPRE.LowDegree.ldEnc`), and the subtests check that those probes are consistent…
--
--   **Definitions** (26): `MIPRE.QLD.Answer` (Answers, in the ``Answer Format'' column of `fig:decider_pauli`'s table.); `MIPRE.QLD.Bas` (The two Pauli bases the test probes.); `MIPRE.QLD.Content` (The ambient content of a sample: two points, a seed, a raw diagonal direction, and the two qubit basis elements, all uniform and…); `MIPRE.QLD.Content.omega` (The tuple `ω` a content carries.); `MIPRE.QLD.Content.pt` (The point of a content on the `W` side.); `MIPRE.QLD.Content.question` (The question a player of type `t` receives, the paper's typed CL functions read off the ambient sample.); `MIPRE.QLD.Omega` (The tuple `ω = (u_X, u_Z, r_X, r_Z)` every Magic Square and commutation-check question carries.); `MIPRE.QLD.Omega.pt` (The point of `ω` on the `W` side.); `MIPRE.QLD.Omega.r` (The qubit basis element of `ω` on the `W` side.); `MIPRE.QLD.Question` (Questions: a type together with the content that type prescribes, in the ``Question Content'' column of `fig:decider_pauli`'s table.); `MIPRE.QLD.Question.fmtOk` (Whether an answer has the format its question's type prescribes, which is the table at the top of `fig:decider_pauli`.); `MIPRE.QLD.Question.ty` (The type of a question.); `MIPRE.QLD.Sample` (A run of the verifier's random choices: an ordered edge of the type graph and the ambient content, drawn independently and uniformly.); `MIPRE.QLD.Ty` (The twenty-six question types of `eq:pauli-type`.); `MIPRE.QLD.TyEdge` (The ordered type pairs the graph distribution puts mass on.); and -3 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `question_ty`, `accepts_eq_false_left`, `accepts_eq_false_right`, `adj_self`, `qldGame_D`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Game` (`MIPRE/Background/QLD/Game.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Game.lean; blueprint def:qld-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Game.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game

/-!
# The Pauli basis test

Blueprint `def:qld-game`, the paper's game `game^pauli_{(q,m,d)}` (`ldt.tex`, `sec:qld-game`
for the question distribution and `fig:decider_pauli` for the decision procedure). This is the
game `thm:qld` is about and `lem:qld-win` unpacks.

The test certifies that the players share `|EPR_q⟩^{⊗ M}`, `M = 2^m`. A player asked
`(Pauli, W)` measures `{τ^W_h}_{h ∈ F_q^M}` and reports `h`; every other question probes
limited information about `h` through its low-degree encoding `g_h : F_q^m → F_q`
(`MIPRE.LowDegree.ldEnc`), and the subtests check that those probes are consistent with each
other and across the two bases.

## The three groups of question types

`type^pauli = ({Point, ALine, DLine, Pauli, Pair} × {X, Z}) ∪ type^MS ∪ {Pair}` --- twenty-six
types, `Ty` below, in three groups with three different jobs.

* **`(Point, W)`, `(ALine, W)`, `(DLine, W)`, `(Pauli, W)`** run the *classical* low-degree test
  of `def:lidt-cl` separately in each basis, plus the tie from a point probe to the full
  outcome. The line and point content is read off the sample exactly as the seeded CL game
  reads it (`MIPRE.LIDT.CL.chi`, `rep`, `zeroBelow`), which is what makes the distribution a
  typed CL distribution and lets the soundness proof feed `thm:lidt-cl-soundness`.
* **`Pair`, `(Pair, W)`** are the commutation check. The two two-outcome measurements
  `tr(g_{h_X}(u_X) r_X)` and `tr(g_{h_Z}(u_Z) r_Z)` either commute or anticommute, according to
  `γ(ω) = 0` or not (`MIPRE.LowDegree.acGamma`, blueprint `fact:omega-anticomm-prob`); when
  they commute the verifier asks for both at once and compares.
* **`Constraint_i`, `Variable_j`** are the Magic Square, run *when they anticommute* --- which
  is exactly when they cannot be measured together. `thm:ms-from-ac` is the completeness
  direction, and `lem:ms-direct-anticomm` (`MIPRE/Background/QLD/Anticomm.lean`) is the
  soundness direction this game consumes. The indices here are the layout's own
  (`MIPRE.LCS.MagicSquare.layout`), `0`-indexed against the paper's `1`-indexed
  `Constraint_1..6` and `Variable_1..9`, so the paper's distinguished pair
  `(Point, X)`--`Variable_1` and `(Point, Z)`--`Variable_5` is `var 0` with `X` and `var 4`
  with `Z` here.

## The distribution

`adj` is the type graph `fig:type-graph-pauli`: thirty non-loop edges (eighteen Magic Square
incidences, six line/point and point/Pauli edges, two point/variable edges, four through the
commutation check) and a self-loop at every one of the twenty-six vertices. The verifier draws
an ordered pair of adjacent types --- the graph distribution of `def:graph-distribution`, each
non-loop edge contributing two ordered pairs and each self-loop one, so uniform over the
`2 * 30 + 26 = 86` ordered pairs --- then `(u_X, u_Z, s, v, r_X, r_Z)` uniformly, and hands
each player the content its type prescribes. Sampling the pair and the content independently
and uniformly is what makes `Sample` a product and `μ_sum_one` one division.

## The decision procedure

`fig:decider_pauli` is a format check and then seven rules. `Question.fmtOk` is the check --- the
table at the top of the figure --- and `subtests` the rules, with `accepts` their conjunction.

The separation is not cosmetic, and the warning is on the record: the seeded CL game shipped
without its format check, which made the test vacuous and `thm:lidt-cl-soundness` false about
it (`reports/clgame-format-check-missing.md`). The same class of error is available here with
twenty-six types instead of three, so every rule below has a witness that it can fail:
`rejects_*` for the format check and for each of the seven rules.

Two structural facts about the rules are worth stating mechanically rather than trusting.
`subtests_covers_adj` says the catch-all --- `fig:ld-decider`'s "in all cases where no action
is indicated, accept", which this figure inherits --- is reached only at *non-adjacent* type
pairs, so it never accepts anything the distribution actually asks. And `lowDeg_eq_cl` says the
low-degree rule is the seeded CL decider at `ldc = 1` and not a paraphrase of it, which is what
the figure prescribes ("accept if `D^ld_{(q,m,d,1)}` accepts").
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE.LIDT MIPRE.LCS.MagicSquare
open MvPolynomial (eval)

/-! ## Bases -/

/-- The two Pauli bases the test probes. -/
inductive Bas
  | X
  | Z
  deriving DecidableEq

instance : Fintype Bas where
  elems := {Bas.X, Bas.Z}
  complete t := by cases t <;> simp

/-! ## Question types -/

/-- The twenty-six question types of `eq:pauli-type`. -/
inductive Ty
  /-- `(Point, W)`. -/
  | point (W : Bas)
  /-- `(ALine, W)`. -/
  | aline (W : Bas)
  /-- `(DLine, W)`. -/
  | dline (W : Bas)
  /-- `(Pauli, W)`. -/
  | pauli (W : Bas)
  /-- `(Pair, W)`, one half of the commutation check. -/
  | pairB (W : Bas)
  /-- `Pair`, both halves of the commutation check at once. -/
  | pair
  /-- `Constraint_i` of the Magic Square. -/
  | con (i : Fin layout.r)
  /-- `Variable_j` of the Magic Square. -/
  | var (j : Fin layout.s)
  deriving DecidableEq, Fintype

/-- The type graph `fig:type-graph-pauli`, one orientation per non-loop edge. -/
def adjRaw : Ty → Ty → Bool
  | .aline W, .point W' => decide (W = W')
  | .dline W, .point W' => decide (W = W')
  | .point W, .pauli W' => decide (W = W')
  | .point W, .pairB W' => decide (W = W')
  | .pairB _, .pair => true
  | .point .X, .var j => decide (j = v 0)
  | .point .Z, .var j => decide (j = v 4)
  | .con i, .var j => decide (j ∈ layout.V i)
  | _, _ => false

/-- `{t, u} ∈ E(G^pauli)`: the graph of `fig:type-graph-pauli`, with the self-loop at every
vertex that the figure's caption adds. -/
def adj (t u : Ty) : Bool := decide (t = u) || adjRaw t u || adjRaw u t

@[simp] theorem adj_self (t : Ty) : adj t t = true := by simp [adj]

/-! ## Questions -/

/-- The tuple `ω = (u_X, u_Z, r_X, r_Z)` every Magic Square and commutation-check question
carries. -/
structure Omega (F : Type*) (m : ℕ) where
  /-- The `X`-side point. -/
  uX : Point F m
  /-- The `Z`-side point. -/
  uZ : Point F m
  /-- The `X`-side qubit basis element. -/
  rX : F
  /-- The `Z`-side qubit basis element. -/
  rZ : F
  deriving DecidableEq, Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

/-- The point of `ω` on the `W` side. -/
def Omega.pt (ω : Omega F m) : Bas → Point F m
  | .X => ω.uX
  | .Z => ω.uZ

/-- The qubit basis element of `ω` on the `W` side. -/
def Omega.r (ω : Omega F m) : Bas → F
  | .X => ω.rX
  | .Z => ω.rZ

/-- Questions: a type together with the content that type prescribes, in the ``Question
Content'' column of `fig:decider_pauli`'s table. A `(Pauli, W)` question carries no content
(the paper's `x_w = 0`). -/
inductive Question (F : Type*) (m : ℕ)
  /-- `((Point, W), y)`. -/
  | point (W : Bas) (y : Point F m)
  /-- `((ALine, W), (u₀, s))`. -/
  | aline (W : Bas) (u₀ : Point F m) (s : F)
  /-- `((DLine, W), (u₀, s, v))`. -/
  | dline (W : Bas) (u₀ : Point F m) (s : F) (v : Point F m)
  /-- `((Pauli, W), 0)`. -/
  | pauli (W : Bas)
  /-- `((Pair, W), ω)`. -/
  | pairB (W : Bas) (ω : Omega F m)
  /-- `(Pair, ω)`. -/
  | pair (ω : Omega F m)
  /-- `(Constraint_i, ω)`. -/
  | con (i : Fin layout.r) (ω : Omega F m)
  /-- `(Variable_j, ω)`. -/
  | var (j : Fin layout.s) (ω : Omega F m)
  deriving DecidableEq, Fintype

/-- Answers, in the ``Answer Format'' column of `fig:decider_pauli`'s table. -/
inductive Answer (F : Type*) (m d : ℕ)
  /-- A point answer, an element of `F_q`. -/
  | val (a : F)
  /-- An axis-parallel line answer, of degree at most `d`. -/
  | apoly (f : LinePoly F d)
  /-- A diagonal line answer, of degree at most `m·d`. -/
  | dpoly (f : LinePoly F (m * d))
  /-- A `(Pauli, W)` answer, an element of `F_q^M` with `M = 2^m`. -/
  | pauliAns (h : (Fin m → Bool) → F)
  /-- A single bit: the answer to `(Pair, W)` and to `Variable_j`. -/
  | bit (b : ZMod 2)
  /-- `(β_X, β_Z) ∈ F_2^2`, the answer to `Pair`. -/
  | bitPair (β : Bas → ZMod 2)
  /-- `(α_{v_1}, α_{v_2}, α_{v_3}) ∈ F_2^3`, the answer to `Constraint_i`, indexed by the
  position of the variable in the constraint's support (`MIPRE.LCS.MagicSquare.cell`). -/
  | bitTriple (α : Fin 3 → ZMod 2)
  deriving DecidableEq, Fintype

/-- The type of a question. -/
def Question.ty : Question F m → Ty
  | .point W _ => .point W
  | .aline W _ _ => .aline W
  | .dline W _ _ _ => .dline W
  | .pauli W => .pauli W
  | .pairB W _ => .pairB W
  | .pair _ => .pair
  | .con i _ => .con i
  | .var j _ => .var j

/-! ## The sample space -/

/-- The ambient content of a sample: two points, a seed, a raw diagonal direction, and the two
qubit basis elements, all uniform and independent. -/
structure Content (F : Type*) (m : ℕ) where
  /-- The `X`-side point. -/
  uX : Point F m
  /-- The `Z`-side point. -/
  uZ : Point F m
  /-- The seed, which selects the axis-parallel direction through `χ`. -/
  s : F
  /-- The raw diagonal direction. -/
  v : Point F m
  /-- The `X`-side qubit basis element. -/
  rX : F
  /-- The `Z`-side qubit basis element. -/
  rZ : F
  deriving DecidableEq, Fintype

/-- The ordered type pairs the graph distribution puts mass on. -/
abbrev TyEdge : Type := {p : Ty × Ty // adj p.1 p.2 = true}

/-- A run of the verifier's random choices: an ordered edge of the type graph and the ambient
content, drawn independently and uniformly. -/
abbrev Sample (F : Type*) (m : ℕ) := TyEdge × Content F m

/-- The tuple `ω` a content carries. -/
def Content.omega (c : Content F m) : Omega F m := ⟨c.uX, c.uZ, c.rX, c.rZ⟩

/-- The point of a content on the `W` side. -/
def Content.pt (c : Content F m) : Bas → Point F m
  | .X => c.uX
  | .Z => c.uZ

/-- The question a player of type `t` receives, the paper's typed CL functions read off the
ambient sample. The line types read it exactly as `MIPRE.LIDT.CL.Sample.question` does, on the
point of the relevant basis. -/
def Content.question [NeZero m] (hm : m ∣ Fintype.card F) (c : Content F m) :
    Ty → Question F m
  | .point W => .point W (c.pt W)
  | .aline W => .aline W (MIPRE.LIDT.CL.rep (Pi.single (MIPRE.LIDT.CL.chi hm c.s) 1) (c.pt W))
      c.s
  | .dline W =>
      let v' := MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v
      .dline W (MIPRE.LIDT.CL.rep v' (c.pt W)) c.s v'
  | .pauli W => .pauli W
  | .pairB W => .pairB W c.omega
  | .pair => .pair c.omega
  | .con i => .con i c.omega
  | .var j => .var j c.omega

omit [DecidableEq F] in
@[simp] theorem Content.question_ty [NeZero m] (hm : m ∣ Fintype.card F) (c : Content F m)
    (t : Ty) : (c.question hm t).ty = t := by
  cases t <;> rfl

/-! ## The format check -/

/-- Whether an answer has the format its question's type prescribes, which is the table at the
top of `fig:decider_pauli`. The decider's first step is this check and it **rejects** if it
fails: "first checks that ... `a_A` and `a_B` also have the correct length, as can be inferred
from the table above. If not, it rejects." -/
def Question.fmtOk : Question F m → Answer F m d → Bool
  | .point _ _, .val _ => true
  | .aline _ _ _, .apoly _ => true
  | .dline _ _ _ _, .dpoly _ => true
  | .pauli _, .pauliAns _ => true
  | .pairB _ _, .bit _ => true
  | .pair _, .bitPair _ => true
  | .con _ _, .bitTriple _ => true
  | .var _ _, .bit _ => true
  | _, _ => false

/-! ## The rules -/

section Rules

variable [Algebra (ZMod 2) F]

/-- `γ(ω)`, whose vanishing says that the two two-outcome measurements of `ω` commute
(`MIPRE.LowDegree.acGamma`, blueprint `fact:omega-anticomm-prob`). -/
def gam (ω : Omega F m) : ZMod 2 := MIPRE.LowDegree.acGamma (ZMod 2) ω.uX ω.uZ ω.rX ω.rZ

/-- `tr_{q → 2}(a · r)`, the two-outcome probe of `fig:decider_pauli`. -/
def prb (a r : F) : ZMod 2 := Algebra.trace (ZMod 2) F (a * r)

/-- The seeded CL decider's line-against-point check at `ldc = 1`: the point lies on the line
and the polynomial evaluated at its parameter is the point answer. -/
def lowDeg {n : ℕ} (u₀ w y : Point F m) (f : LinePoly F n) (a : F) : Bool :=
  MIPRE.LIDT.CL.lineVsPoint (ldc := 1) u₀ w y (fun _ => f) (fun _ => a)

/-- The seven rules of `fig:decider_pauli`, on distinct types and correctly formatted answers.
Each rule is stated in both orientations, as the figure's "for `w ∈ {A, B}`" prescribes; the
catch-all is the figure's inherited "in all cases where no action is indicated, accept", and
`subtests_covers_adj` checks it is reached only off the type graph. -/
def pairTest [NeZero m] (hm : m ∣ Fintype.card F) :
    Question F m → Question F m → Answer F m d → Answer F m d → Bool
  -- 2a. low-degree, axis-parallel lines
  | .point W y, .aline W' u₀ s, .val a, .apoly f =>
      if W = W' then lowDeg u₀ (Pi.single (MIPRE.LIDT.CL.chi hm s) 1) y f a else true
  | .aline W' u₀ s, .point W y, .apoly f, .val a =>
      if W = W' then lowDeg u₀ (Pi.single (MIPRE.LIDT.CL.chi hm s) 1) y f a else true
  -- 2b. low-degree, diagonal lines
  | .point W y, .dline W' u₀ _ w, .val a, .dpoly f =>
      if W = W' then lowDeg u₀ w y f a else true
  | .dline W' u₀ _ w, .point W y, .dpoly f, .val a =>
      if W = W' then lowDeg u₀ w y f a else true
  -- 3. the point probe against the full Pauli outcome
  | .point W y, .pauli W', .val a, .pauliAns h =>
      if W = W' then decide (eval y (MIPRE.LowDegree.ldEnc h) = a) else true
  | .pauli W', .point W y, .pauliAns h, .val a =>
      if W = W' then decide (eval y (MIPRE.LowDegree.ldEnc h) = a) else true
  -- 4. commutation check
  | .pairB W _, .pair ω, .bit b, .bitPair β =>
      decide (gam ω ≠ 0) || decide (b = β W)
  | .pair ω, .pairB W _, .bitPair β, .bit b =>
      decide (gam ω ≠ 0) || decide (b = β W)
  -- 5. commutation consistency
  | .point W y, .pairB W' ω, .val a, .bit b =>
      if W = W' then decide (gam ω ≠ 0) || decide (prb a (ω.r W) = b) else true
  | .pairB W' ω, .point W y, .bit b, .val a =>
      if W = W' then decide (gam ω ≠ 0) || decide (prb a (ω.r W) = b) else true
  -- 6. magic square
  | .con i _, .var j ω, .bitTriple α, .bit b =>
      decide (gam ω = 0) ||
        (decide (j ∈ layout.V i) && decide (∑ k, α k = game.b i) && decide (α (cellIdx i j) = b))
  | .var j ω, .con i _, .bit b, .bitTriple α =>
      decide (gam ω = 0) ||
        (decide (j ∈ layout.V i) && decide (∑ k, α k = game.b i) && decide (α (cellIdx i j) = b))
  -- 7. magic square consistency
  | .point W y, .var j ω, .val a, .bit b =>
      decide (gam ω = 0) ||
        (decide (W = .X) && decide (j = v 0) && decide (prb a ω.rX = b)) ||
        (decide (W = .Z) && decide (j = v 4) && decide (prb a ω.rZ = b))
  | .var j ω, .point W y, .bit b, .val a =>
      decide (gam ω = 0) ||
        (decide (W = .X) && decide (j = v 0) && decide (prb a ω.rX = b)) ||
        (decide (W = .Z) && decide (j = v 4) && decide (prb a ω.rZ = b))
  -- the catch-all
  | _, _, _, _ => true

/-- The rules of `fig:decider_pauli`: equal types compare the answers, distinct types run
`pairTest`. -/
def subtests [NeZero m] (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d) : Bool :=
  if x.ty = y.ty then decide (a = b) else pairTest hm x y a b

/-- **The decision procedure of `fig:decider_pauli`**: the format check, then the rules. -/
def accepts [NeZero m] (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d) : Bool :=
  x.fmtOk a && y.fmtOk b && subtests hm x y a b

/-! ### The rules cover the type graph

The vacuity failure mode is a rule that is *missing*, so that an edge of the type graph falls
through to the catch-all and the test checks nothing on it. `handled` lists the type pairs
`pairTest` has a branch for, and `handled_of_adj` checks by `decide` that every non-loop edge
of `fig:type-graph-pauli` is among them. Together with the rejection witnesses below --- one
per branch, each exhibiting formatted answers that branch rejects --- that is what says no
question pair the distribution asks is accepted regardless of the answers.

The converse fails, and harmlessly: `pairTest` rejects some non-adjacent pairs too, for
instance `(Point, X)` against `Variable_j` for `j ≠ 0`, which the distribution never asks. -/

/-- The type pairs `pairTest` has a rule for, in both orientations. -/
def handled : Ty → Ty → Bool
  | .point W, .aline W' => decide (W = W')
  | .aline W, .point W' => decide (W = W')
  | .point W, .dline W' => decide (W = W')
  | .dline W, .point W' => decide (W = W')
  | .point W, .pauli W' => decide (W = W')
  | .pauli W, .point W' => decide (W = W')
  | .pairB _, .pair => true
  | .pair, .pairB _ => true
  | .point W, .pairB W' => decide (W = W')
  | .pairB W, .point W' => decide (W = W')
  | .con _, .var _ => true
  | .var _, .con _ => true
  | .point _, .var _ => true
  | .var _, .point _ => true
  | _, _ => false

/-! ### The low-degree rule is the seeded CL decider

`fig:decider_pauli` says "accept if `D^ld_{(q,m,d,1)}` accepts", so the rule must *be* the
seeded CL decider of `def:lidt-cl` at `ldc = 1` and not a paraphrase of it. Both halves hold by
`rfl`: `MIPRE.LIDT.CL.accepts`'s own format check is discharged by the formats these two
questions carry, and what is left is its `lineVsPoint`. -/

/-! ## Non-vacuity

Each of the eight rules is pinned by an explicit pair of answers it rejects, which is what says
the rule reads its answers at all. The four rules gated on `γ` need the gate as a hypothesis:
each of them checks nothing on the other value of `γ`, by design, and that is the point of the
gate. `MIPRE/LCS/MagicSquare/Game.lean` does the same for the Magic Square game itself. -/

section Witnesses

variable [NeZero m] {hm : m ∣ Fintype.card F}

@[simp] theorem accepts_eq_false_left {x y : Question F m} {a b : Answer F m d}
    (h : x.fmtOk a = false) : accepts hm x y a b = false := by simp [accepts, h]

@[simp] theorem accepts_eq_false_right {x y : Question F m} {a b : Answer F m d}
    (h : y.fmtOk b = false) : accepts hm x y a b = false := by simp [accepts, h]

end Witnesses

end Rules

/-! ## The game -/

section GameDef

variable [Algebra (ZMod 2) F] [NeZero m]

/-- **The Pauli basis test** as a game (blueprint `def:qld-game`). -/
def qldGame (hm : m ∣ Fintype.card F) :
    MIPRE.Game (Question F m) (Question F m) (Answer F m d) (Answer F m d) where
  μ x y := ∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (x, y) then 1 else 0
  μ_nonneg _ _ := Finset.sum_nonneg fun _ _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  μ_sum_one := by
    rw [← Fintype.sum_prod_type', Finset.sum_comm]
    simp only [← Finset.mul_sum, Prod.mk.eta, Fintype.sum_ite_eq, mul_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine mul_inv_cancel₀ ?_
    have : 0 < Fintype.card (Sample F m) :=
      Fintype.card_pos_iff.mpr ⟨⟨⟨(.pair, .pair), by simp⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩⟩
    simpa using this.ne'
  D := accepts hm

@[simp] theorem qldGame_D (hm : m ∣ Fintype.card F) (x y : Question F m)
    (a b : Answer F m d) : (qldGame hm).D x y a b = accepts hm x y a b := rfl

end GameDef

end MIPRE.QLD

end


