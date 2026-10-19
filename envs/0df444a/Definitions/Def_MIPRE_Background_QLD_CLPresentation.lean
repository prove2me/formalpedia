-- Prove2me | Definitions.Def_MIPRE_Background_QLD_CLPresentation
-- name    : MIPRE_Background_QLD_CLPresentation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:22.259271+00:00
-- url     : https://prove2.me/theorems/18bcfb3a-25e7-4f26-bb26-dc8fa41f74e8
-- title:
--   Definitions of CLPresentation: The actual three-level Pauli question presentations The ambient coordinates are precisely the two points, the seed, the…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.CLPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The actual three-level Pauli question presentations. The ambient coordinates are precisely the two points, the seed, the raw direction, and the two scalars in `Content`. The presentation reads the seed, then the selected direction, then the point and scalar registers. Its full evaluation is the question map of the existing twenty-six-type Pauli game. These are concrete field-valued presentations; uniform binary execution is a separate layer.
--
--   **Definitions** (15): `MIPRE.QLD.PauliCL.Coord` (The `3m+3` field coordinates in the actual Pauli sample.); `MIPRE.QLD.PauliCL.contentEquiv`; `MIPRE.QLD.PauliCL.contentVector`; `MIPRE.QLD.PauliCL.coordEquiv`; `MIPRE.QLD.PauliCL.directionMap`; `MIPRE.QLD.PauliCL.directionSet`; `MIPRE.QLD.PauliCL.finalMap`; `MIPRE.QLD.PauliCL.finalSet`; `MIPRE.QLD.PauliCL.pointMap` (A point-register linear map, zero on all other content coordinates.); `MIPRE.QLD.PauliCL.presentation` (All twenty-six full question maps, with an explicit three-stage register partition.); `MIPRE.QLD.PauliCL.questionOfVector` (Decode the actual content carried by a question of the specified type.); `MIPRE.QLD.PauliCL.secondMap`; `MIPRE.QLD.PauliCL.seedMap`; `MIPRE.QLD.PauliCL.seedSet`; `MIPRE.QLD.PauliCL.vectorContent`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `directionMap_apply`, `pointMap_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.CLPresentation` (`MIPRE/Background/QLD/CLPresentation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 28 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLPresentation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLPresentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game

/-! # The actual three-level Pauli question presentations

The ambient coordinates are precisely the two points, the seed, the raw
direction, and the two scalars in `Content`. The presentation reads the seed,
then the selected direction, then the point and scalar registers. Its full
evaluation is the question map of the existing twenty-six-type Pauli game.
These are concrete field-valued presentations; uniform binary execution is
a separate layer.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

/-- The `3m+3` field coordinates in the actual Pauli sample. -/
inductive Coord (m : ℕ)
  | point (W : Bas) (i : Fin m)
  | seed
  | direction (i : Fin m)
  | scalar (W : Bas)
  deriving DecidableEq, Fintype

def coordEquiv (m : ℕ) : Coord m ≃ ((Bas × Fin m) ⊕ (Unit ⊕ (Fin m ⊕ Bas))) where
  toFun
    | .point W i => .inl (W, i)
    | .seed => .inr (.inl ())
    | .direction i => .inr (.inr (.inl i))
    | .scalar W => .inr (.inr (.inr W))
  invFun
    | .inl (W, i) => .point W i
    | .inr (.inl _) => .seed
    | .inr (.inr (.inl i)) => .direction i
    | .inr (.inr (.inr W)) => .scalar W
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with ⟨W, i⟩ | (u | (i | W)) <;> rfl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def contentVector (c : Content F m) : Coord m → F
  | .point .X i => c.uX i
  | .point .Z i => c.uZ i
  | .seed => c.s
  | .direction i => c.v i
  | .scalar .X => c.rX
  | .scalar .Z => c.rZ

def vectorContent (x : Coord m → F) : Content F m :=
  ⟨fun i => x (.point .X i), fun i => x (.point .Z i), x .seed,
    fun i => x (.direction i), x (.scalar .X), x (.scalar .Z)⟩

def contentEquiv : Content F m ≃ (Coord m → F) where
  toFun := contentVector
  invFun := vectorContent
  left_inv c := by cases c; rfl
  right_inv x := by
    funext i
    cases i with
    | point W i => cases W <;> rfl
    | scalar W => cases W <;> rfl
    | seed => rfl
    | direction i => rfl

def seedSet (m : ℕ) : Finset (Coord m) := {.seed}

def directionSet (m : ℕ) : Finset (Coord m) :=
  univ.filter fun c => match c with | .direction _ => True | _ => False

def finalSet (m : ℕ) : Finset (Coord m) := (seedSet m ∪ directionSet m)ᶜ

/-- A point-register linear map, zero on all other content coordinates. -/
def pointMap (W : Bas) (L : (Fin m → F) →ₗ[F] (Fin m → F)) :
    CL.RegLinear F (finalSet m) where
  toLinearMap :=
    { toFun := fun x c => match c with
        | .point W' i => if W' = W then L (fun j => x (.point W j)) i else 0
        | _ => 0
      map_add' x y := by
        funext c
        cases c with
        | point W' i =>
          by_cases h : W' = W
          · simp only [if_pos h, Pi.add_apply]
            exact congrFun (L.map_add (fun j => x (.point W j))
              (fun j => y (.point W j))) i
          · simp only [if_neg h, Pi.add_apply, add_zero]
        | seed => simp
        | direction i => simp
        | scalar W => simp
      map_smul' a x := by
        funext c
        cases c with
        | point W' i =>
          by_cases h : W' = W
          · simp only [if_pos h, Pi.smul_apply]
            exact congrFun (L.map_smul a (fun j => x (.point W j))) i
          · simp only [if_neg h, Pi.smul_apply, smul_zero]
        | seed => simp
        | direction i => simp
        | scalar W => simp }
  proj_comp_proj' x := by
    funext c
    cases c with
    | point W' i =>
      simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | seed => simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | direction i => simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | scalar W => simp [CL.proj_apply, finalSet, seedSet, directionSet]

def directionMap (i : Fin m) : CL.RegLinear F (directionSet m) where
  toLinearMap :=
    { toFun := fun x c => match c with
        | .direction j => if j < i then 0 else x (.direction j)
        | _ => 0
      map_add' x y := by
        funext c
        cases c with
        | direction j => by_cases h : j < i <;> simp [h]
        | point W j => simp
        | seed => simp
        | scalar W => simp
      map_smul' a x := by
        funext c
        cases c with
        | direction j => by_cases h : j < i <;> simp [h]
        | point W j => simp
        | seed => simp
        | scalar W => simp }
  proj_comp_proj' x := by
    funext c
    cases c <;> simp [CL.proj_apply, directionSet]

def seedMap : Ty → CL.RegLinear F (seedSet m)
  | .aline _ | .dline _ => CL.RegLinear.id _
  | _ => 0

@[simp] theorem pointMap_apply (W : Bas)
    (L : (Fin m → F) →ₗ[F] (Fin m → F)) (x : Coord m → F) (c : Coord m) :
    pointMap W L x c = (match c with
      | .point W' i => if W' = W then L (fun j => x (.point W j)) i else 0
      | _ => 0) := rfl

@[simp] theorem directionMap_apply (i : Fin m) (x : Coord m → F) (c : Coord m) :
    directionMap i x c = (match c with
      | .direction j => if j < i then 0 else x (.direction j)
      | _ => 0) := rfl

variable [NeZero m]

def secondMap (hm : m ∣ Fintype.card F) (t : Ty) (s : F) :
    CL.RegLinear F (directionSet m) :=
  match t with
  | .dline _ => directionMap (LIDT.CL.chi hm s)
  | _ => 0

def finalMap (hm : m ∣ Fintype.card F) (t : Ty) (s : F) (v : Fin m → F) :
    CL.RegLinear F (finalSet m) :=
  match t with
  | .point W => pointMap W LinearMap.id
  | .aline W => pointMap W
      (CL.canonLin (Submodule.span F {Pi.single (LIDT.CL.chi hm s) 1}))
  | .dline W => pointMap W (CL.canonLin (Submodule.span F {v}))
  | .pauli _ => 0
  | _ => CL.RegLinear.id _

/-- All twenty-six full question maps, with an explicit three-stage register
partition. Trivial stages are retained for the lower-level question types. -/
def presentation (hm : m ∣ Fintype.card F) (t : Ty) : CL.CLFun F (Coord m) 3 :=
  .cons (seedSet m) (seedMap t) fun y =>
    .cons (directionSet m) (secondMap hm t (y .seed)) fun z =>
      .cons (finalSet m) (finalMap hm t (y .seed) (fun i => z (.direction i)))
        fun _ => .zero

/-- Decode the actual content carried by a question of the specified type. -/
def questionOfVector (t : Ty) (x : Coord m → F) : Question F m :=
  let c := vectorContent x
  match t with
  | .point W => .point W (c.pt W)
  | .aline W => .aline W (c.pt W) c.s
  | .dline W => .dline W (c.pt W) c.s c.v
  | .pauli W => .pauli W
  | .pairB W => .pairB W c.omega
  | .pair => .pair c.omega
  | .con i => .con i c.omega
  | .var j => .var j c.omega

end MIPRE.QLD.PauliCL
end


