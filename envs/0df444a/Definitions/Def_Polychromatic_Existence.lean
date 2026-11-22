-- Prove2me | Definitions.Def_Polychromatic_Existence
-- name    : Polychromatic_Existence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:34:57.662526+00:00
-- url     : https://prove2.me/theorems/eccfd646-0eba-47ad-8a2c-654baf397475
-- title:
--   Existence
-- statement:
--   Definitions and structural lemmas for Existence, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Existence.lean

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
def polychromColouringBound (k m : ℕ) : Prop :=
  Real.exp 1 * (m * (m - 1) + 1) * k * (1 - (k : ℝ)⁻¹) ^ m ≤ 1
open Real
noncomputable def mBound (k : ℕ) : ℕ :=
  ⌈k * (3 * log k + (2 * log (log k) + 5.2))⌉₊
open Asymptotics Filter Topology


