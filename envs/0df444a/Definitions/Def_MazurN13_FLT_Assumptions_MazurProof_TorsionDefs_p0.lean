-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TorsionDefs_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_TorsionDefs_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:43:58.592395+00:00
-- url     : https://prove2.me/theorems/f496db7b-56d8-4339-9848-678079267e0d
-- title:
--   FLT.Assumptions.MazurProof.TorsionDefs source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TorsionDefs

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TorsionDefs
Original leading source comments and nonproject imports are retained below. -/
import Mathlib

set_option autoImplicit false




/-!
# Torsion definitions for the Mazur bound proof

Extracted from Axioms.lean to break import cycles.
Both Axioms.lean and RealTorsionBound.lean import this file.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

end MazurProof


