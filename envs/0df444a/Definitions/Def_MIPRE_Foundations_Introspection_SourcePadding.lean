-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
-- name    : MIPRE_Foundations_Introspection_SourcePadding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:54:39.521174+00:00
-- url     : https://prove2.me/theorems/ec9ac5e5-7f74-43f7-befd-92025ce6a6b2
-- title:
--   Definitions of SourcePadding: Padding the original CL source game without changing its strategy Unused seed coordinates are ignored
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourcePadding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding the original CL source game without changing its strategy. Unused seed coordinates are ignored. On every sampled padded question pair, the pulled-back questions have one common original seed. This suffices to preserve perfect PCC play with exactly the original Hilbert-space dimension.
--
--   **Definitions** (4): `MIPRE.Introspection.SourcePadding.decider`; `MIPRE.Introspection.SourcePadding.depthFamily` (Consume unused coordinates by the zero part of the existing first factor.); `MIPRE.Introspection.SourcePadding.family`; `MIPRE.Introspection.SourcePadding.strategy` (The common source measurement rule just restricts question coordinates.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `positive_seed`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourcePadding` (`MIPRE/Foundations/Introspection/SourcePadding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 62 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourcePadding.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourcePadding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_directSum
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! # Padding the original CL source game without changing its strategy

Unused seed coordinates are ignored. On every sampled padded question pair,
the pulled-back questions have one common original seed. This suffices to
preserve perfect PCC play with exactly the original Hilbert-space dimension.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ)
  (D : (I → F) → (I → F) → A → A → Bool)

def family (w : Bool) : CL.CLFun F J ℓ := (L w).embed e
def decider (x y : J → F) : A → A → Bool := D (CL.pull e x) (CL.pull e y)

/-- Consume unused coordinates by the zero part of the existing first factor.
Unlike `fullFamily`, this construction preserves the original depth. -/
def depthFamily (w : Bool) : CL.CLFun F J ℓ :=
  (family e L w).directSum (CL.CLFun.zeroOn (univ.map e)ᶜ ℓ)

variable (R : SyncStrategy (Honest.sourceGame L D).doubled)

/-- The common source measurement rule just restricts question coordinates. -/
def strategy : SyncStrategy (Honest.sourceGame (family e L) (decider e D)).doubled where
  d := R.d
  d_pos := R.d_pos
  P :=
    { M := fun q a => R.P.M (q.1, CL.pull e q.2) a
      selfAdjoint := fun q a => R.P.selfAdjoint (q.1, CL.pull e q.2) a
      projective := fun q a => R.P.projective (q.1, CL.pull e q.2) a
      normalized := fun q => R.P.normalized (q.1, CL.pull e q.2) }

set_option backward.isDefEq.respectTransparency false in
theorem positive_seed (q r : Bool × (J → F))
    (h : 0 < (Honest.sourceGame (family e L) (decider e D)).doubled.μ q r) :
    ∃ x : J → F, q = (false,(family e L false).eval x) ∧
      r = (true,(family e L true).eval x) := by
  have ht : q.1 = false ∧ r.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  have hs : 0 < SampledGame.dist (family e L false).eval (family e L true).eval q.2 r.2 := by
    simpa only [Game.doubled_μ, if_pos ht, Honest.sourceGame, SampledGame.game] using h
  rw [SampledGame.dist_eq_card, div_pos_iff_of_pos_right
    (by exact_mod_cast (Fintype.card_pos (α := J → F)))] at hs
  simp only [Nat.cast_pos, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and] at hs
  obtain ⟨x,hx,hy⟩ := hs
  exact ⟨x,Prod.ext ht.1 hx.symm,Prod.ext ht.2 hy.symm⟩

end MIPRE.Introspection.SourcePadding
end


