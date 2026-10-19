-- Prove2me | Definitions.Def_MIPRE_Foundations_CrossConsistency_B
-- name    : MIPRE_Foundations_CrossConsistency_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:01.309529+00:00
-- url     : https://prove2.me/theorems/26fb2ebf-9364-46ec-879d-2731b8ab1200
-- title:
--   Definitions of CrossConsistency (addendum): Cross-party consistency, and what winning a subtest buys The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`:…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CrossConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Cross-party consistency, and what winning a subtest buys. The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the *other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same side, which is what the orthonormalization step needs; this file is the cross-party form, and the one lemma that produces it.
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_CrossConsistency` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (3): `MIPRE.obs2` (The `±1`-observable of a POVM with outcomes in `F_2`.); `MIPRE.xPovmDist` (**The cross-party distance** of two families of POVMs, one on each side, relative to a question distribution: the appendix's `M^x_a ⊗ Id…); `MIPRE.xStateDist` (**The cross-party distance** of two families of operators, one on each side.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CrossConsistency` (`MIPRE/Foundations/CrossConsistency.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 10 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CrossConsistency.lean; blueprint def:cross-distance

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_CrossConsistency does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail
import Theorems.Thm_MIPRE_sum_bornProb_mapA
import Theorems.Thm_MIPRE_sum_bornProb_mapB
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul

/-!
# Cross-party consistency, and what winning a subtest buys

The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the
*other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same
side, which is what the orthonormalization step needs; this file is the cross-party form, and
the one lemma that produces it.

## The engine

`xSqNorm ψ A B = ‖(A ⊗ Id - Id ⊗ B)|ψ⟩‖²`, and `xPovmDist` averages its sum over outcomes
against a question distribution. `xSqNorm_sum_le_two_mul` is the only analytic content:

```
∑_c ‖(A_c ⊗ Id - Id ⊗ B_c)|ψ⟩‖² ≤ 2 (1 - ∑_c ⟨ψ| A_c ⊗ B_c |ψ⟩)
```

for any two POVMs indexed by the same outcome set. Expand each square; the two diagonal sums are
at most one because a POVM element `A` has `A† A = A² ≤ A` and the elements sum to the identity,
and the cross term is exactly the agreement probability. **No projectivity is used** --- which
matters, because the strategies this is applied to are arbitrary POVM strategies and the
projectivity only arrives later, through `cor:ortho-from-consistency`.

Paired with `condFail_agree`, which says the right-hand side *is* twice the conditional failure
of a subtest whose decider accepts iff two post-processings of the answers agree, this turns
each item of `lem:qld-win` into an instance: name the two post-processings, check the decider,
and the bound is `2 ε / μ`.

## The weights

`sum_mul_condFail_le` is the other half: the conditional failures of *any* set of question
pairs, weighted by their probabilities, add up to at most `ε`. `condFail_le_div` in
`MIPRE/Foundations/POVMValue.lean` is its one-pair case. The useful corollary is
`sum_condFail_le_of_le`: an auxiliary distribution `ν` on an index set that injects into the
question pairs, with `c · ν i ≤ μ` at each, gives `∑_i ν i · condFail ≤ ε / c`. That is the
blueprint's "each item is the value of the corresponding subtest, divided by the probability
that the subtest is selected", with `c` the selection probability and `ν` the conditional
question distribution.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The cross-party squared deviation -/

/-- **The cross-party distance** of two families of POVMs, one on each side, relative to a
question distribution: the appendix's `M^x_a ⊗ Id ≃_δ Id ⊗ N^x_a`. -/
def xPovmDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM C dA) (N : X → POVM C dB) : ℝ :=
  ∑ x, μ x * ∑ c, xSqNorm ψ (((M x).mats c).val) (((N x).mats c).val)

/-! ## The cross-party distance of generalized observables

`stateDist_obsOf_le` is the same-side statement (blueprint `lem:qld-povm-to-obs`); the appendix
needs it across the two parties as well, to pass from a two-outcome coarse-graining of a point
measurement to the `±1`-observable it defines. -/

/-- **The cross-party distance** of two families of operators, one on each side. -/
def xStateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (A : X → Matrix dA dA ℂ)
    (B : X → Matrix dB dB ℂ) : ℝ :=
  ∑ x, μ x * xSqNorm ψ (A x) (B x)

/-! ## A POVM element is a contraction on the state

`A† A = A² ≤ A` for `0 ≤ A ≤ 1`, so the diagonal terms of the expansion below sum to at most
one. This is the only place positivity of the POVM is used. -/

/-! ## The engine -/

/-! ## The conditional failure of an agreement subtest

The decider of a real test does not *equal* an agreement predicate: it first checks the answer
formats and rejects if they fail, so an ill-formatted pair with agreeing post-processings is
still rejected. What holds, and all that is needed, is the implication **accept implies agree**.
The coarse-grainings are then free to send ill-formatted answers anywhere --- `0` is the usual
choice --- since the test rejects them either way. -/

variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

/-! ## The weights of the subtests -/

variable {ε : ℝ}

/-! ## Products, and the order reversal

`lem:qld-obs-commutation` needs one algebraic rule on top of the estimate above: if each of two of
Alice's operators is cross-close to one of Bob's, then their *product* is cross-close to the
product of Bob's **in the reverse order**. The reversal is not an accident of bookkeeping; it is
where it comes from. Split

```
AB ⊗ Id - Id ⊗ B'A' = (A ⊗ Id)(B ⊗ Id - Id ⊗ B') + (Id ⊗ B')(A ⊗ Id - Id ⊗ A')
```

--- the second step is legitimate because `A ⊗ Id` and `Id ⊗ B'` commute, and it is that commuting
step that puts `B'` on the *left* of `A'`. Each summand then loses its front factor to a bound on
its operator norm.

This is stated on the unsquared deviation, because the triangle inequality is what the argument
uses; `xSqNorm_mul_le` squares it at the cost of the usual factor two.
-/

section Reversal

variable {ψ : dA × dB → ℂ}

/-! ### A sum inside a deviation

Pushing a sum inside a deviation costs the number of terms; the appendix's chains need it when a
marginal of a joint measurement replaces the measurement itself. -/

/-! ### Transferring an anticommutation across the two factors

This is the shape the anticommuting case of `lem:qld-obs-commutation` needs, and it is where the
sign comes from. Suppose `A ⊗ Id ~ Id ⊗ A'` and `B ⊗ Id ~ Id ⊗ B'`. Then

```
AB + BA ⊗ Id = [AB ⊗ Id - Id ⊗ B'A'] + [Id ⊗ (A'B' + B'A')] + [BA ⊗ Id - Id ⊗ A'B']
```

is an identity --- Bob's two products cancel --- and its three summands are, in order: an order
reversal, Bob's own anticommutator, and the other order reversal. So if Bob's two operators
anticommute on the state then Alice's two *anti*commute on it as well: the product picked up a
reversal on the way across and a second one on the way back, and the two reversals do not cancel
because the anticommutator in the middle is a sum, not a difference. -/

/-! ### Two-outcome observables

A two-outcome POVM's `±1`-observable is the difference of its two elements, which is what
`obsOf sgn` computes; stating it as a difference is what makes the contraction bound of
`POVM.sub_mul_self_le_one` available, and every consumer of the order reversal needs that. -/

/-- The `±1`-observable of a POVM with outcomes in `F_2`. -/
def obs2 {d : Type*} [Fintype d] [DecidableEq d] (P : POVM (ZMod 2) d) : Matrix d d ℂ :=
  ((P.mats 0).val) - ((P.mats 1).val)

/-! ### The swap, for mixed operators

`norm_stateVecB` says Bob's norm is Alice's norm of the swapped state, but only for an operator
sitting on one factor. The chain below needs it for a *difference* of one operator on each factor,
and the clean statement is at the level of vectors: a Kronecker product applied to the swapped
state is the swap of the exchanged product applied to the state. Everything else follows by
linearity. -/

/-! ### The commutator form of the transfer

The same split as `norm_stateVec_anticomm_le`, with the middle term a commutator rather than an
anticommutator: Bob's two products cancel either way. -/

end Reversal

end MIPRE

end


