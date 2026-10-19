-- Prove2me | Definitions.Def_MIPRE_Foundations_VerifierIndexTransport
-- name    : MIPRE_Foundations_VerifierIndexTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:15.258133+00:00
-- url     : https://prove2.me/theorems/5f4e8d38-3366-44f4-8dad-a4416e66faa5
-- title:
--   Definitions of VerifierIndexTransport: Verifier transport at a single index Wrappers may change a sampler at exceptional indices
-- statement:
--   The definitions of the module `MIPRE.Foundations.VerifierIndexTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Verifier transport at a single index. Wrappers may change a sampler at exceptional indices. Equality of its dimension and CL presentations at the index in question suffices to preserve both quantum value and perfect PCC strategies; the programs need not agree elsewhere.
--
--   **Definitions** (2): `MIPRE.Verifier.SamplerAgreement` (Only the sampler data used at this index are compared.); `MIPRE.Verifier.dimensionEquiv` (Numbered vectors transported along an equality of their dimensions.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.VerifierIndexTransport` (`MIPRE/Foundations/VerifierIndexTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/VerifierIndexTransport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/VerifierIndexTransport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel
import Theorems.Thm_MIPRE_quantumValue_eq_of_equiv

/-! # Verifier transport at a single index

Wrappers may change a sampler at exceptional indices. Equality of its dimension
and CL presentations at the index in question suffices to preserve both quantum
value and perfect PCC strategies; the programs need not agree elsewhere.
-/

noncomputable section
namespace MIPRE.Verifier
open CL

/-- Numbered vectors transported along an equality of their dimensions. -/
def dimensionEquiv {s t : ℕ} (h : s = t) : (Fin s → 𝔽₂) ≃ (Fin t → 𝔽₂) :=
  h ▸ Equiv.refl _

variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}

/-- Only the sampler data used at this index are compared. -/
structure SamplerAgreement (V W : Verifier ℓ) (n : ℕ) : Prop where
  dimension : V.sampler.dim n = W.sampler.dim n
  presentation : ∀ w, HEq (V.sampler.cl n w) (W.sampler.cl n w)

end MIPRE.Verifier


