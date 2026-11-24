-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
-- name    : Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:23.82624+00:00
-- url     : https://prove2.me/theorems/d2355143-529f-40ed-a755-8c460a2a4f2d
-- title:
--   Lat Defs
-- statement:
--   Definitions and structural lemmas for Lat Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/LatDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Sph
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k]
def IntM {m p : Type} (Z : Matrix m p k) : Prop := ∀ i j, Z i j ∈ 𝒪[k]
def Below {n d : ℕ} (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) 𝒪[k], ∃ Z : Matrix (Fin n) (Fin d) k, IntM Z ∧
    Y = A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z
def latt {n d : ℕ} (t : k) (Y₀ : Matrix (Fin n) (Fin d) k) : Submodule 𝒪[k] (Fin d → k) :=
  Submodule.span 𝒪[k] (Set.range Y₀ ∪ Set.range fun j : Fin d => t • (Pi.single j 1 : Fin d → k))
end PositivityTheory.Sph
end


