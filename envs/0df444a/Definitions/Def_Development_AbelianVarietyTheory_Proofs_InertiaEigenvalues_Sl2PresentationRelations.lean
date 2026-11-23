-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:28.465975+00:00
-- url     : https://prove2.me/theorems/846798ef-4cfc-45d6-95e7-0f6f2fedcd2d
-- title:
--   Sl2 Presentation Relations
-- statement:
--   Definitions and structural lemmas for Sl2 Presentation Relations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.BruhatRep
variable {K : Type} [Field K]
def en (g : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) : K := (g : Matrix (Fin 2) (Fin 2) K) i j
variable {M : Type} [Monoid M]
open Classical in

def mx (m : Kˣ → M) (x : K) : M := if h : x = 0 then 1 else m (Units.mk0 x h)
open Classical in

def rho (n : K → M) (m : Kˣ → M) (t : M) (g : SpecialLinearGroup (Fin 2) K) : M :=
  if en g 1 0 = 0 then mx m (en g 0 0) * n (en g 0 1 / en g 0 0)
  else n (en g 0 0 / en g 1 0) * mx m (-1 / en g 1 0) * t * n (en g 1 1 / en g 1 0)
section rel
variable (n : K → M) (m : Kˣ → M) (t : M)
end rel
end GlobalTheory.BruhatRep
namespace GlobalTheory.BruhatRep
end GlobalTheory.BruhatRep


