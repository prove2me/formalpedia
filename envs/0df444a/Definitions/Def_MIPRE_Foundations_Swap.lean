-- Prove2me | Definitions.Def_MIPRE_Foundations_Swap
-- name    : MIPRE_Foundations_Swap
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:37.945894+00:00
-- url     : https://prove2.me/theorems/01d92211-0dcb-4053-8dd7-ccc8d68b29a2
-- title:
--   Definitions of Swap: Exchanging the two players A game whose question distribution and decision predicate are both symmetric in the players…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Swap` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exchanging the two players. A game whose question distribution and decision predicate are both symmetric in the players is unchanged by exchanging them, and so is the value of a strategy once the state is swapped (`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved about Alice's measurements, with Bob's only as the other party --- into the statement about **Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion back through `norm_stateVecB`. The Pauli basis test is such a game: every rule of its decider is…
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `swapVec_swapVec`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Swap` (`MIPRE/Foundations/Swap.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 8 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Swap.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Swap.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue

/-!
# Exchanging the two players

A game whose question distribution and decision predicate are both symmetric in the players is
unchanged by exchanging them, and so is the value of a strategy once the state is swapped
(`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved
about Alice's measurements, with Bob's only as the other party --- into the statement about
**Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion
back through `norm_stateVecB`.

The Pauli basis test is such a game: every rule of its decider is written in both orientations
(`MIPRE.QLD.accepts_symm`) and its sampler draws an *ordered* edge of a symmetric type graph
(`MIPRE.QLD.qldGame_mu_symm`). Its combining stage needs both players' commutation bounds, which
is why this is here.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
@[simp] theorem swapVec_swapVec (ψ : dA × dB → ℂ) : swapVec (swapVec ψ) = ψ := rfl

end MIPRE

end


