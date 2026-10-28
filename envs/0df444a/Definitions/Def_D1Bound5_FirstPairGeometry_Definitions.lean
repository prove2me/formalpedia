-- Prove2me | Definitions.Def_D1Bound5_FirstPairGeometry_Definitions
-- name    : D1Bound5_FirstPairGeometry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:30:04.74618+00:00
-- url     : https://prove2.me/theorems/74212645-9019-44f3-9668-8a5beebf93e7
-- title:
--   First Pair Geometry
-- statement:
--   Definitions for first pair geometry in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `firstPairPhi`.
-- source:
--   D1Bound5/FirstPairGeometry.lean, lines 6-7, SHA-256 6897ed712974dd8aa38c4f747975287a62389b141930051223663f4f1d136bb9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.GCongr

section
namespace D1Bound5

noncomputable def firstPairPhi (b s : ℂ) : ℝ :=
  max ((‖b-s‖/‖s‖)^6) ((‖b‖/‖s‖)*(‖b-s‖/‖s‖)^5)





end D1Bound5
end


