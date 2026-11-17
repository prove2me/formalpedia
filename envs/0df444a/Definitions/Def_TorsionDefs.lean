-- Prove2me | Definitions.Def_TorsionDefs
-- name    : TorsionDefs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:17.627478+00:00
-- url     : https://prove2.me/theorems/6611bdb3-4c53-4496-94dc-1186dfc68555
-- title:
--   Common predicates and data for rational torsion structures
-- statement:
--   For an elliptic curve $E/ℚ$, the file defines its rational torsion set, the existence of an injective copy of $(ℤ/mℤ)^2$, the existence of a rational point of order $n$, and an injective torsion structure $ℤ/mℤ×ℤ/nℤ$. It also packages positive integers $m∣n$, the embedding data, a point of order $n$, and the torsion cardinality $mn$ into one structure. This is the shared logical interface for the Mazur classification statements.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
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


