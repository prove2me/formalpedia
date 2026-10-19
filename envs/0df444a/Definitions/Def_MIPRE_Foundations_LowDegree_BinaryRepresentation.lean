-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
-- name    : MIPRE_Foundations_LowDegree_BinaryRepresentation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:57.269243+00:00
-- url     : https://prove2.me/theorems/9132ed41-97ff-48f5-a43d-ab4c573553a1
-- title:
--   Definitions of BinaryRepresentation: Binary coefficient representations The coefficient interpretation used by the public Shoup contract and by the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryRepresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary coefficient representations. The coefficient interpretation used by the public Shoup contract and by the independent polynomial algorithms. This module does not assume that an irreducible polynomial has already been constructed.
--
--   **Definitions** (1): `MIPRE.LowDegree.polyOfBits` (The polynomial over `𝔽₂` whose coefficient of `Tⁱ` is bit `i` of `l`, least significant first --- the repository's little-endian bit…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryRepresentation` (`MIPRE/Foundations/LowDegree/BinaryRepresentation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryRepresentation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryRepresentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# Binary coefficient representations

The coefficient interpretation used by the public Shoup contract and by the
independent polynomial algorithms. This module does not assume that an
irreducible polynomial has already been constructed.
-/

namespace MIPRE.LowDegree

open Cost

/-- The polynomial over `𝔽₂` whose coefficient of `Tⁱ` is bit `i` of `l`, least significant
first --- the repository's little-endian bit convention (`Cost.bitsVal`, `bitsOfNat`). -/
noncomputable def polyOfBits (l : List Bool) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range l.length, Polynomial.monomial i (if l.getD i false then 1 else 0)

namespace BinaryPolynomial

end BinaryPolynomial

end MIPRE.LowDegree


