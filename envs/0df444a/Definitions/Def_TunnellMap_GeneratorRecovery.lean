-- Prove2me | Definitions.Def_TunnellMap_GeneratorRecovery
-- name    : TunnellMap_GeneratorRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:47:00.125449+00:00
-- url     : https://prove2.me/theorems/4c106742-bd25-44dd-a8b1-89f7a36afff8
-- title:
--   Generator Recovery
-- statement:
--   Definitions and structural lemmas for Generator Recovery, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorRecovery.lean

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
set_option autoImplicit true
namespace TunnellMap
structure GeneratorWitness {n : ℤ} (s : BResidual n) (t : AResidual n)
    (R : PreferredMidpointRecord s t) where
  frame : OrthogonalFrame (tau (residualSourceLift s))
  A : ℤ
  q : ℤ
  r : Triple
  a : ℤ
  b : ℤ
  u : ℤ
  A_eq : A = qForm R.direction
  q_eq : q = R.multiplier
  r_eq : r = tau R.direction
  A_pos : 0 < A
  A_bound : 2 * A ≤ n - 1
  q_odd : Odd q
  q_range : q ^ 2 * A < n
  r_tau_parity : InTauLattice r
  affine_coordinates :
    r = linComb3 a b (q * A) frame.e₁ frame.e₂ frame.z
  affine_norm : dot r r = A
  root_certificate :
    u ^ 2 = frame.halfDiscriminant A q b ∧
      dot frame.e₁ frame.e₁ * a =
        -(dot frame.e₁ frame.e₂ * b + q * A * dot frame.z frame.e₁) + u
  short_window :
    let α := dot frame.e₁ frame.e₁
    let β := dot frame.e₁ frame.e₂
    let δ := dot frame.z frame.e₁
    let ε := dot frame.z frame.e₂
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    (n * b - q * A * K) ^ 2 ≤ α * M
end TunnellMap


