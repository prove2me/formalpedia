-- Prove2me | Definitions.Def_proofs_PhosphorylationSharpness_Resolution
-- name    : proofs_PhosphorylationSharpness_Resolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:22:21.2232+00:00
-- url     : https://prove2.me/theorems/709cacf8-6c3e-4a13-80d2-b3762e51a00b
-- title:
--   Resolution
-- statement:
--   Definitions and structural lemmas for Resolution, from mmislan (mmislan/palomar-p080-phosphorylation-attainment; see pinned Apache-2.0 LICENSE)'s pinned Sharp lower bound on positive equilibria in sequential distributive phosphorylation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Resolution.lean

import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
set_option autoImplicit true
namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
def Attains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (z : Fin count → State n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective z ∧
      ∀ j, (z j).Positive ∧ Equilibrium k (z j) ∧
        totalE (z j)=ET ∧ totalF (z j)=FT ∧ totalS (z j)=ST
end
end PhosphorylationSharpness


