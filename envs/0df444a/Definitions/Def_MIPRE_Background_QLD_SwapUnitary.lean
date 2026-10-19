-- Prove2me | Definitions.Def_MIPRE_Background_QLD_SwapUnitary
-- name    : MIPRE_Background_QLD_SwapUnitary
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:59.01216+00:00
-- url     : https://prove2.me/theorems/b89e6185-e39f-4c23-a053-bef67faef871
-- title:
--   Definitions of SwapUnitary: The swap unitary, and why two twirls force an EPR pair Blueprint `lem:qld-swap`, the part of it that is **exact**,…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.SwapUnitary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap unitary, and why two twirls force an EPR pair. Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate that turns the exact part into the closeness statement. The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary* `V = sum_{(g_X, g_Z)} S_{g_X,g_Z} (x) tau^X(cd g_Z) tau^Z(cd g_X)` and shows that conjugation by it carries each exact Pauli observable `wTilde` of `MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla, `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities,…
--
--   **Definitions** (5): `MIPRE.QLD.eprProj` (The rank-one projector onto the maximally entangled state of the two ancilla halves.); `MIPRE.QLD.sTensor` (`sum_p S_p (x) T_p`: an ancilla-side family `T` read along the outcomes of `S`.); `MIPRE.QLD.swapU` (**The swap unitary** of the appendix's isometry construction.); `MIPRE.QLD.twirl` (**The Weyl twirl** `E_u tau^W(u) (x) tau^W(u)` on two copies of the ancilla.); `MIPRE.QLD.uOf` (The ancilla-side factor of the swap unitary at one outcome: `tau^X(cd g_Z) tau^Z(cd g_X)`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.SwapUnitary` (`MIPRE/Background/QLD/SwapUnitary.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapUnitary.lean; blueprint lem:qld-swap

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapUnitary.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-!
# The swap unitary, and why two twirls force an EPR pair

Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate
that turns the exact part into the closeness statement.

The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary*

`V = sum_{(g_X, g_Z)} S_{g_X,g_Z}  (x)  tau^X(cd g_Z) tau^Z(cd g_X)`

and shows that conjugation by it carries each exact Pauli observable `wTilde` of
`MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla,
`V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities, and both are here
(`swapU_mul_conjTranspose`, `swapU_conj`).

## The algebra of `sTensor`

Every operator in sight has the shape `sum_p S_p (x) T_p` for a family `T` on the ancilla. Because
`S` is projective, these compose factorwise (`sTensor_mul`), so the whole calculation is arithmetic
in `T` and the projectivity of `S` is used once, in that one lemma. Unitarity of `V` and the
conjugation identity are then two lines each.

## The two twirls

The estimate rests on an identity about the Weyl system alone, with no measurement in it:

`twirl_mul_twirl`:  `(E_u tau^X(u) (x) tau^X(u)) * (E_v tau^Z(v) (x) tau^Z(v)) = |EPR_q><EPR_q|` .

The paper reaches it through an iterated tensor product over the `M` qudits. In this
repository `(C^q)^{(x) M}` is *one* matrix algebra indexed by `F_q^M`
(`MIPRE/Foundations/Weyl.lean` explains why), so the identity is a single entry computation: the
`v`-average kills every off-diagonal pair of column indices by the cancellation lemma, and the
`u`-average then leaves exactly the diagonal pair of row indices.

## The repaired arithmetic

`re_inner_ge_of_two_close` is the last step, and it is where the pinned paper carried an error that
the verification campaign repaired: the earlier text bounded `||(H_W - Id) v||` by `delta_S` where
the display above it gives `delta_S` for the *square*, and compared a squared triangle inequality
with `2 sqrt(delta_S)` where the bound on the square is `4 delta_S`. The conclusion
`O(sqrt(delta_S))` is unchanged; only the constants move, and the chain below is the corrected one:
from `Re<theta, H_W theta> >= 1 - delta/2` for both `W` one gets
`Re<H_X theta, H_Z theta> >= 1 - 2 sqrt(delta) - 2 delta`.

The case split in its proof is not in the paper and is not a repair --- it is what a statement
with no implicit "for small enough `delta`" needs: for `delta > 1` the first chain's
`1 - sqrt(delta)` is negative and squaring it reverses, so that range is handled by the trivial
bound `Re<x,y> >= -2 delta`, which is already stronger there.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

set_option linter.unusedSectionVars false

/-! ## Operators block-diagonal along a pair measurement -/

/-- `sum_p S_p (x) T_p`: an ancilla-side family `T` read along the outcomes of `S`. The swap
unitary, the exact Pauli observables and the identity are all of this shape. -/
def sTensor (S : G × G → Matrix dA dA ℂ) (T : G × G → Matrix (n → F) (n → F) ℂ) :
    Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  ∑ p, S p ⊗ₖ T p

/-! ## The swap unitary -/

/-- The ancilla-side factor of the swap unitary at one outcome: `tau^X(cd g_Z) tau^Z(cd g_X)`.
Note the crossing --- the argument of the `X`-type operator is the `Z`-side polynomial. -/
def uOf (cd : G → (n → F)) (p : G × G) : Matrix (n → F) (n → F) ℂ :=
  wX (cd p.2) * wZ (cd p.1)

/-- **The swap unitary** of the appendix's isometry construction. -/
def swapU (S : G × G → Matrix dA dA ℂ) (cd : G → (n → F)) :
    Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  sTensor S (uOf cd)

variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}

/-! ### Conjugating a Weyl operator by the ancilla factor

Two instances of the twisted commutation relation, in the only form the conjugation needs. -/

/-! ### The conjugation identity -/

/-! ## The two twirls, and the maximally entangled state -/

/-- The rank-one projector onto the maximally entangled state of the two ancilla halves. The
generalized Paulis in characteristic two are real, so no conjugation appears. -/
def eprProj : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ :=
  Matrix.vecMulVec (epr (F := F) (n := n)) (epr (F := F) (n := n))

/-- **The Weyl twirl** `E_u tau^W(u) (x) tau^W(u)` on two copies of the ancilla. -/
def twirl (w : (n → F) → Matrix (n → F) (n → F) ℂ) :
    Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ u : n → F, w u ⊗ₖ w u

/-! ## From two near-invariances to the overlap

The last step of `lem:qld-swap`, in the state-independent form: two vectors each close to a unit
vector have a large inner product with one another. Both lemmas are elementary, and both are
stated for a bound rather than for the quantity itself, so that no "for small enough" is hidden. -/

section TwoClose

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end TwoClose

end MIPRE.QLD

end


