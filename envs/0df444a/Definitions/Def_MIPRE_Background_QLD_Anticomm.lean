-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Anticomm
-- name    : MIPRE_Background_QLD_Anticomm
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:49.240731+00:00
-- url     : https://prove2.me/theorems/216584f9-d42e-4f65-bb6b-e2956baf1044
-- title:
--   Definitions of Anticomm: Direct Magic Square anticommutation Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Anticomm` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Direct Magic Square anticommutation. Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with probability `ε` has `‖{B₁, B₅}|ψ⟩‖² ≤ 186624 ε` for the *original* `±1`-observables of the two players --- no isometry, no projectivity, no extracted EPR pairs. This is the only thing the Pauli basis test consumes from the Magic Square, and it is much weaker than the full rigidity theorem `thm:ms-rigidity`, which this repository does not prove.
--
--   **Definitions** (16): `MIPRE.QLD.MS.Dilated` (**The dilated Alice measurement.** For each constraint, a projective measurement on `dA × PV` whose compression by the *fixed* ancilla…); `MIPRE.QLD.MS.PV` (The repaired outcome set of a constraint.); `MIPRE.QLD.MS.anti` (`{B₀, B₄}`, the anticommutator the Pauli basis test consumes.); `MIPRE.QLD.MS.bobs` (Bob's `±1`-observable at variable `j`: the difference of the two bit outcomes.); `MIPRE.QLD.MS.con` (Constraint `c`: the three rows then the three columns.); `MIPRE.QLD.MS.corr` (The signed Born mass at an incidence: Alice's repaired outcome bit against Bob's answer bit, agreement counting `+1` and disagreement `-1`.); `MIPRE.QLD.MS.csgn` (The sign weighting of constraint `c` at its `j`-th cell.); `MIPRE.QLD.MS.dd` (`‖(X - Y) ⊗ Id |ψ'⟩‖`, the quantity every step of the word argument estimates.); `MIPRE.QLD.MS.dst` (The state, with Alice's ancilla adjoined in its initial state.); `MIPRE.QLD.MS.emb` (The fixed ancilla embedding of Alice's space.); `MIPRE.QLD.MS.pvBit` (The bit that outcome `k` assigns to cell `j` of constraint `c`.); `MIPRE.QLD.MS.refl` (Alice's reflection for constraint `c` at its `j`-th cell.); `MIPRE.QLD.MS.rep` (Alice's answer to a constraint, **repaired** to a parity-valid outcome: an assignment satisfying the constraint keeps its bits at the first…); `MIPRE.QLD.MS.repPOVM` (Alice's repaired constraint POVM, with the four parity-valid outcomes.); `MIPRE.QLD.MS.rsgn` (`(-1)^x` for a bit, as a real.); and -15 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Anticomm` (`MIPRE/Background/QLD/Anticomm.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Anticomm.lean; blueprint lem:ms-direct-anticomm

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
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
import Definitions.Def_MIPRE_Foundations_Swap
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_sum_bornProb

/-!
# Direct Magic Square anticommutation

Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with probability
`ε` has `‖{B₁, B₅}|ψ⟩‖² ≤ 186624 ε` for the *original* `±1`-observables of the two players ---
no isometry, no projectivity, no extracted EPR pairs. This is the only thing the Pauli basis
test consumes from the Magic Square, and it is much weaker than the full rigidity theorem
`thm:ms-rigidity`, which this repository does not prove.

## The shape of the argument

Alice's constraint answers are **repaired** to parity-valid ones and pushed forward to a POVM
with four outcomes (`repPOVM`), then **dilated** to a projective measurement on one shared
ancilla (`MIPRE.exists_projective_dilation`). Signed sums of that measurement are reflections
that commute within a constraint and multiply to its sign *exactly*
(`MIPRE.pvmObs_mul_mul`) --- that is what the dilation buys, and it is why the repair has to
happen first.

The rest is norm bookkeeping on the dilated state, in the operator-bound calculus of
`MIPRE/Foundations/OpBound.lean`: each of Alice's reflections is within `γ` of the
corresponding Bob observable, `γ² ≤ 144 ε`; a Bob word of length `t` can be replaced by the
reversed word of Alice reflections at cost `t γ`; a within-constraint relation costs `3 γ`; and
the six-step path through the six constraints turns `d a e b` into `- d e a b` at cost `24 γ`.
-/

noncomputable section

namespace MIPRE.QLD.MS

open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder

/-! ## Alice's repaired outcomes

A parity-valid answer to a constraint is determined by its bits at the first two cells, so the
repaired outcome set is `ZMod 2 × ZMod 2` and the bit at the third cell is read off the
constraint's right-hand side. -/

/-- The repaired outcome set of a constraint. -/
abbrev PV : Type := ZMod 2 × ZMod 2

/-- The bit that outcome `k` assigns to cell `j` of constraint `c`. -/
def pvBit (c : Fin layout.r) (k : PV) (j : Fin 3) : ZMod 2 :=
  if j = 0 then k.1 else if j = 1 then k.2 else game.b c + k.1 + k.2

/-- The sign weighting of constraint `c` at its `j`-th cell. -/
def csgn (c : Fin layout.r) (j : Fin 3) : PV → ℂ := fun k => sgn (pvBit c k j)

/-! ## The repaired and dilated Alice measurement -/

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- Alice's answer to a constraint, **repaired** to a parity-valid outcome: an assignment
satisfying the constraint keeps its bits at the first two cells, and everything else --- an
assignment violating the parity, or an answer of the wrong shape --- is sent to `(0, 0)`. This
preserves every originally winning pair, which is all the argument needs. -/
def rep (c : Fin layout.r) : layout.Answer → PV
  | .inl a => if (∑ k ∈ layout.V c, a k) = game.b c then (a (cell c 0), a (cell c 1)) else (0, 0)
  | .inr _ => (0, 0)

/-- Alice's repaired constraint POVM, with the four parity-valid outcomes. -/
def repPOVM (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) (k : PV) :
    Matrix dA dA ℂ :=
  ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k}, ((MA (Sum.inl c)).mats d).val

/-- The fixed ancilla embedding of Alice's space. -/
def emb (dA : Type) [DecidableEq dA] : Matrix (dA × PV) dA ℂ := ancillaEmbed dA ((0, 0) : PV)

/-- **The dilated Alice measurement.** For each constraint, a projective measurement on
`dA × PV` whose compression by the *fixed* ancilla embedding is the repaired POVM. The
embedding not depending on the constraint is what lets all six act on one state, and it is why
`MIPRE.exists_projective_dilation` has to extend the dilating isometry to a unitary. -/
structure Dilated (MA : layout.Question → POVM layout.Answer dA) where
  /-- The projective measurement at each constraint. -/
  P : Fin layout.r → PV → Matrix (dA × PV) (dA × PV) ℂ
  /-- Each is a projective measurement. -/
  isPVM : ∀ c, IsPVM (P c)
  /-- Each compresses to the repaired POVM, along the same embedding. -/
  compress : ∀ c k, (emb dA)ᴴ * (P c k * emb dA) = repPOVM MA c k

/-! ## Alice's reflections -/

variable {MA : layout.Question → POVM layout.Answer dA}

/-- Alice's reflection for constraint `c` at its `j`-th cell. -/
def refl (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    Matrix (dA × PV) (dA × PV) ℂ :=
  pvmObs (D.P c) (csgn c j)

/-! ## Numerals for the magic square -/

/-- Variable `k`, in row-major order. -/
def var (k : ℕ) (h : k < layout.s := by decide) : Fin layout.s := ⟨k, h⟩

/-- Constraint `c`: the three rows then the three columns. -/
def con (c : ℕ) (h : c < layout.r := by decide) : Fin layout.r := ⟨c, h⟩

/-! ## The dilated state -/

/-- The state, with Alice's ancilla adjoined in its initial state. -/
def dst (ψ : dA × dB → ℂ) : (dA × PV) × dB → ℂ :=
  ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ

/-! ## Bob's observables and Alice's reflections, on the product space -/

/-- Bob's `±1`-observable at variable `j`: the difference of the two bit outcomes. Answers of
the wrong shape contribute zero, which is exactly the paper's convention. -/
def bobs (MB : layout.Question → POVM layout.Answer dB) (j : Fin layout.s) :
    Matrix dB dB ℂ :=
  ((MB (Sum.inr j)).mats (Sum.inr 0)).val - ((MB (Sum.inr j)).mats (Sum.inr 1)).val

variable {MB : layout.Question → POVM layout.Answer dB}

variable {MA : layout.Question → POVM layout.Answer dA}

/-! ## The distance between two of Bob's operators on the state -/

/-- `‖(X - Y) ⊗ Id |ψ'⟩‖`, the quantity every step of the word argument estimates. -/
def dd (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : ℝ :=
  snorm (dst ψ) (bOp X - bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)

/-! ## Replacing Bob's letters by Alice's reflections

A Bob word of length `t` agrees on the state with the *reversed* word of Alice reflections to
within `t γ`: replace the letters one at a time from the right, each replacement costing `γ`,
and cross the tensor factors so the Alice letters accumulate in the opposite order. Only lengths
one, two and three occur in the argument, so the three cases are spelled out rather than
induced. -/

section Words

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

end Words

/-! ## Rewriting inside a word -/

section Rewrites

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

end Rewrites

/-! ## The six-step path

`d a e b` becomes `- d e a b` by applying the six constraints in turn --- column one, column
two, row three, column three, row two, row one --- at a total cost of `24 γ`. The sign appears
exactly once, at column three, which is the constraint of product `-1`. -/

section Path

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

end Path

/-! ## Removing the two outer letters

The path bounds `‖d (a e + e a) b |ψ'⟩‖`. Removing `d` costs the non-projectivity of `b_3`,
which is `‖(Id - b_3²) W |ψ'⟩‖ ≤ (2 + t) γ` for a word of length `t`; removing `b` costs `2 γ`,
because Alice's reflection for variable `1` is unitary and commutes with the anticommutator. -/

section Final

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

/-- `{B₀, B₄}`, the anticommutator the Pauli basis test consumes. -/
def anti (MB : layout.Question → POVM layout.Answer dB) : Matrix dB dB ℂ :=
  bobs MB (var 0) * bobs MB (var 4) + bobs MB (var 4) * bobs MB (var 0)

end Final

/-! ## From the game's value to the closeness hypothesis

The correlation `⟨ψ'| C_{c,j} ⊗ B_j |ψ'⟩` is agreement minus disagreement between Alice's
repaired outcome bit and Bob's answer bit, and every *winning* answer pair agrees --- that is
what the repair preserves. So the correlation is at least `1 - 2 ℓ_{c,j}`, and since
`δ²_{c,j} = 2 - 2⟨ψ'| C B |ψ'⟩ - (1 - ⟨ψ'| B² |ψ'⟩) ≤ 2 - 2⟨ψ'| C B |ψ'⟩`, the reflection is
within `2√ℓ` of the observable. -/

section Correlation

/-- `(-1)^x` for a bit, as a real. -/
def rsgn (x : ZMod 2) : ℝ := if x.val = 1 then -1 else 1

variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}

/-- The signed Born mass at an incidence: Alice's repaired outcome bit against Bob's answer
bit, agreement counting `+1` and disagreement `-1`. -/
def corr (ψ : dA × dB → ℂ) (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB) (c : Fin layout.r) (j : Fin 3) : ℝ :=
  ∑ d : layout.Answer, ∑ w : ZMod 2,
    rsgn (pvBit c (rep c d) j) * rsgn w
      * bornProb ψ (((MA (Sum.inl c)).mats d).val)
          (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val)

end Correlation

/-! ## The correlation is the quadratic form -/

section Assemble

variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}

/-! ## The closeness hypothesis, from the game's value -/

end Assemble

/-! ## The lemma, for the player who receives the variables -/

/-! ## The other player, by the symmetry of the game

Exchanging the players is an automorphism of the Magic Square game
(`MIPRE.LCS.Layout.questionDist_symm`, `MIPRE.LCS.Game.accepts_symm`), so Alice's half of the
lemma is Bob's half applied to the swapped strategy. -/

section Swap

end Swap

end MIPRE.QLD.MS

end


