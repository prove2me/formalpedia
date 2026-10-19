-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
-- name    : MIPRE_Foundations_LowDegree_BinaryDegreeFactors
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:37.34098+00:00
-- url     : https://prove2.me/theorems/290dd223-52eb-4988-9513-5bcb99e5cfef
-- title:
--   Definitions of BinaryDegreeFactors: Prime-power degree decomposition This list is used only in the proof of the all-degrees constructor
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryDegreeFactors` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Prime-power degree decomposition. This list is used only in the proof of the all-degrees constructor. The executable constructor computes the same prime-power factors by bounded unary arithmetic. Indices outside the prime support contribute the neutral factor one.
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors` (Prime-power degree factors in ascending base order, including neutral factors.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryDegreeFactors` (`MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power degree decomposition

This list is used only in the proof of the all-degrees constructor. The
executable constructor computes the same prime-power factors by bounded unary
arithmetic. Indices outside the prime support contribute the neutral factor one.
-/

namespace MIPRE.LowDegree.BinaryDegreeFactors

/-- Prime-power degree factors in ascending base order, including neutral factors. -/
def degreeFactors (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n + 1) => (i : ℕ) ^ n.factorization (i : ℕ))

end MIPRE.LowDegree.BinaryDegreeFactors


