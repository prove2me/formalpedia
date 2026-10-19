-- Prove2me | Definitions.Def_MIPRE_Foundations_RegisterReindex_B
-- name    : MIPRE_Foundations_RegisterReindex_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:28.80458+00:00
-- url     : https://prove2.me/theorems/ebbf1e2a-2221-4a09-b0b1-649fcbb8336c
-- title:
--   Definitions of RegisterReindex (addendum): Reindexing the registers of a bipartite strategy `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.RegisterReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reindexing the registers of a bipartite strategy. `TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be `Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments --- `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their states and measurements on *structured* registers: a strategy's own space tensored with ancillas such as `(dA × Anc F m) × (F × F)`, where the block structure is what the…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_RegisterReindex` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (1): `MIPRE.TensorProductStrategy.ofPVM` (A strategy given by POVM families with projective elements, packaged as a `TensorProductStrategy`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.RegisterReindex` (`MIPRE/Foundations/RegisterReindex.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/RegisterReindex.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/RegisterReindex.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_RegisterReindex does not carry);
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
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex

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

end StarAlgEquiv

/-! ## Reindexing POVMs and projective measurement families -/

section POVM

variable {A : Type*} [Fintype A]
variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

end POVM

/-! ## Reindexing a bipartite state, and the invariance of the Born rule -/

section State

variable {dA dB dA' dB' : Type*}

variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']

variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end State

/-! ## A projective strategy on arbitrary registers, as a `TensorProductStrategy` -/

section Strategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- A strategy given by POVM families with projective elements, packaged as a
`TensorProductStrategy`. -/
noncomputable def TensorProductStrategy.ofPVM (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (hA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hB : ∀ y, IsPVM fun b => ((MB y).mats b).val) : TensorProductStrategy G :=
  TensorProductStrategy.ofProjective G ψ hψ (ProjectiveMeasurement.ofIsPVM MA hA)
    (ProjectiveMeasurement.ofIsPVM MB hB)

end Strategy

end MIPRE


