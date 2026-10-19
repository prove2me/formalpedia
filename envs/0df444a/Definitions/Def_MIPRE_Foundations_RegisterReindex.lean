-- Prove2me | Definitions.Def_MIPRE_Foundations_RegisterReindex
-- name    : MIPRE_Foundations_RegisterReindex
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:41.203057+00:00
-- url     : https://prove2.me/theorems/98c7256a-3158-400b-b3fe-9cee392232dc
-- title:
--   Definitions of RegisterReindex: Reindexing the registers of a bipartite strategy `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   **Definitions** (5): `MIPRE.POVM.reindex` (Reindex a POVM along an equivalence of its register.); `MIPRE.ProjectiveMeasurement.ofIsPVM` (A family of POVMs whose elements are projective, as a `ProjectiveMeasurement`.); `MIPRE.TensorProductStrategy.ofProjective` (A projective strategy on arbitrary finite registers `dA`, `dB`, packaged as a `TensorProductStrategy` on `Fin (card dA) × Fin (card dB)`…); `MIPRE.reindexStarAlgEquiv` (`Matrix.reindex e e` as a star-algebra equivalence of the two matrix algebras.); `MIPRE.reindexVec` (Reindex a bipartite state along equivalences of the two registers.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `reindex_mats`, `toPOVM_ofIsPVM`, `reindexStarAlgEquiv_apply`, `reindexVec_unit`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.RegisterReindex` (`MIPRE/Foundations/RegisterReindex.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/RegisterReindex.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Theorems.Thm_MIPRE_POVM_ext_prime
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val

/-!
# Reindexing the registers of a bipartite strategy

`TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be
`Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments ---
`MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its
strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their
states and measurements on *structured* registers: a strategy's own space tensored with ancillas
such as `(dA × Anc F m) × (F × F)`, where the block structure is what the proofs compute with. A
strategy in that form has a value (`povmValue`), but it is not a `TensorProductStrategy`, and
nothing in the repository turned one into the other. This file is that bridge.

Everything transports along an equivalence `e : d ≃ d'` of a register:

* `reindexStarAlgEquiv e` is `Matrix.reindex e e` as a star-algebra equivalence, so that
  `ProjectiveMeasurement.map` moves projective measurement families across it;
* `POVM.reindex e` moves POVMs, and commutes with the relabelling `POVM.map`
  (`POVM.map_reindex`) and with `ProjectiveMeasurement.toPOVM`
  (`ProjectiveMeasurement.toPOVM_map_reindex`);
* `reindexVec eA eB` moves a bipartite state, and the Born rule is invariant
  (`quadForm_reindex`, `bornProb_reindex`), hence so are `povmValue` (`povmValue_reindex`) and
  `inconsistency` (`inconsistency_reindex`).

`TensorProductStrategy.ofProjective` then packages a projective strategy on arbitrary finite
registers as a `TensorProductStrategy` on `Fin (card dA) × Fin (card dB)`, with
`TensorProductStrategy.value_ofProjective` identifying its value with the `povmValue` of the
original; `TensorProductStrategy.ofPVM` is the same for measurements given as POVM families with
`IsPVM` proofs, the form the rigidity arguments produce. A consumer applies a soundness theorem to
the packaged strategy and reads the conclusion back through `inconsistency_reindex` and the
`reindex` lemmas: `MIPRE.Background.LIDT.Adapter.Registers` does exactly that for the seeded
low individual degree test.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## The matrix algebra of a reindexed register -/

section StarAlgEquiv

variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

/-- `Matrix.reindex e e` as a star-algebra equivalence of the two matrix algebras. -/
def reindexStarAlgEquiv (e : d ≃ d') : Matrix d d ℂ ≃⋆ₐ[ℂ] Matrix d' d' ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) fun M => by
    simp [Matrix.star_eq_conjTranspose]

@[simp] theorem reindexStarAlgEquiv_apply (e : d ≃ d') (M : Matrix d d ℂ) :
    reindexStarAlgEquiv e M = Matrix.reindex e e M := rfl

end StarAlgEquiv

/-! ## Reindexing POVMs and projective measurement families -/

section POVM

variable {A : Type*} [Fintype A]
variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

/-- Reindex a POVM along an equivalence of its register. -/
def POVM.reindex (e : d ≃ d') (M : POVM A d) : POVM A d' where
  mats a := ⟨Matrix.reindex e e (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a := by
    have h : (Matrix.reindex e e (M.mats a).val).PosSemidef := by
      rw [Matrix.reindex_apply]
      exact (M.posSemidef a).submatrix _
    exact Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, Matrix.reindex e e (M.mats a).val = 1
    have h : ∑ a, Matrix.reindex e e (M.mats a).val
        = Matrix.reindex e e (∑ a, (M.mats a).val) :=
      (map_sum (Matrix.reindexLinearEquiv ℂ ℂ e e) _ _).symm
    rw [h, POVM.sum_val, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[simp] theorem POVM.reindex_mats (e : d ≃ d') (M : POVM A d) (a : A) :
    ((M.reindex e).mats a).val = Matrix.reindex e e (M.mats a).val := rfl

/-- A family of POVMs whose elements are projective, as a `ProjectiveMeasurement`. This is the
form the rigidity arguments produce their measurements in (`IsPVM` on the bare matrices), and
`TensorProductStrategy` consumes the bundled form. -/
def ProjectiveMeasurement.ofIsPVM {X : Type*} (M : X → POVM A d)
    (h : ∀ x, IsPVM fun a => ((M x).mats a).val) :
    ProjectiveMeasurement X A (Matrix d d ℂ) where
  M x a := ((M x).mats a).val
  selfAdjoint x a := by rw [Matrix.star_eq_conjTranspose]; exact (h x).isSelfAdjoint a
  projective x a := (h x).idem a
  normalized x := (h x).sum_eq_one

@[simp] theorem ProjectiveMeasurement.toPOVM_ofIsPVM {X : Type*} [Fintype X] (M : X → POVM A d)
    (h : ∀ x, IsPVM fun a => ((M x).mats a).val) (x : X) :
    (ProjectiveMeasurement.ofIsPVM M h).toPOVM x = M x :=
  POVM.ext_prime fun _ => rfl

end POVM

/-! ## Reindexing a bipartite state, and the invariance of the Born rule -/

section State

variable {dA dB dA' dB' : Type*}

/-- Reindex a bipartite state along equivalences of the two registers. -/
def reindexVec (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ) : dA' × dB' → ℂ :=
  ψ ∘ (Equiv.prodCongr eA eB).symm

variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']

/-- A reindexed unit vector is a unit vector. -/
theorem reindexVec_unit (eA : dA ≃ dA') (eB : dB ≃ dB') {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) : star (reindexVec eA eB ψ) ⬝ᵥ reindexVec eA eB ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (Equiv.prodCongr eA eB).symm fun p => star ψ p * ψ p

variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end State

/-! ## A projective strategy on arbitrary registers, as a `TensorProductStrategy` -/

section Strategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- A projective strategy on arbitrary finite registers `dA`, `dB`, packaged as a
`TensorProductStrategy` on `Fin (card dA) × Fin (card dB)` along `Fintype.equivFin`. -/
noncomputable def TensorProductStrategy.ofProjective (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (PA : ProjectiveMeasurement X A (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix dB dB ℂ)) : TensorProductStrategy G where
  dA := Fintype.card dA
  dB := Fintype.card dB
  ψ := reindexVec (Fintype.equivFin dA) (Fintype.equivFin dB) ψ
  ψ_unit := reindexVec_unit _ _ hψ
  PA := PA.map (reindexStarAlgEquiv (Fintype.equivFin dA))
  PB := PB.map (reindexStarAlgEquiv (Fintype.equivFin dB))

end Strategy

end MIPRE


