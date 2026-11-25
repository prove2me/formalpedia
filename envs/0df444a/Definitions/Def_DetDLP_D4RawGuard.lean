-- Prove2me | Definitions.Def_DetDLP_D4RawGuard
-- name    : DetDLP_D4RawGuard
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:34:49.881487+00:00
-- url     : https://prove2.me/theorems/936ca898-8e35-43b9-9a63-862be7bcb73d
-- title:
--   Raw losses and coefficients of guard-tree expansions
-- statement:
--   Each rank of a guard-tree expansion specifies one branch at each expanded node and one rank for each of its 64 children. Its raw loss is the sum of the level-zero losses over those expanded nodes. Its raw coefficient is the product of the canonical integer-jet representatives of the original branch weights. A leaf contributes zero loss and the unit coefficient.
-- source:
--   DetDLP, Appendix D.4 guard-tree expansion, raw coefficients and level-zero losses.

import Definitions.Def_DetDLP_D4GuardWeight
set_option autoImplicit false
namespace DetDLP.D4GuardTree.Expansion
open Polynomial AppendixD4 ResidualScalarOracle
variable {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l : ℕ}

/-- Sum of the level-zero loss at every expanded node; an early leaf costs no loss. -/
noncomputable def rawLossSum : {d k p : ℕ} → {z : B f l p} →
    (e : Expansion S f hf l d k p z) → e.Ranks → ℕ
  | _, _, _, _, .leaf _, _ => 0
  | _, _, _, _, .step (G := G) (d := d) _ _ _ _ _ _ next, r =>
    loss G.nE (D3Stopped.shift S d) (D3Stopped.width S d) 0 + ∑ j, rawLossSum (next r.1 j) (r.2 j)

/-- Product of canonical integer representatives of the original branch weights. -/
noncomputable def rawCoeff : {d k p : ℕ} → {z : B f l p} →
    (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _, _, _, _, .leaf _, _ => 1
  | _, _, _, _, .step s _ _ _ _ _ next, r =>
    repr hf (AdjoinRoot.of _ (s.weight r.1.1 r.1.2.1) : B f l _) * ∏ j, rawCoeff (next r.1 j) (r.2 j)
end DetDLP.D4GuardTree.Expansion


