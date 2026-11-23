-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
-- name    : Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:17.756999+00:00
-- url     : https://prove2.me/theorems/34f84954-4e73-45ba-bc31-2557fe531db9
-- title:
--   Lattice Height Zero Eq
-- statement:
--   Definitions and structural lemmas for Lattice Height Zero Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/LatticeReduction/LatticeHeightZeroEq.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
namespace PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
def Mj (k : Type) [Field k] (N j : ℕ) : Submodule k (Fin N → k) where
  carrier := {x | ∀ a : Fin N, (a : ℕ) < j → x a = 0}
  add_mem' := by
    intro x y hx hy a ha
    simp [hx a ha, hy a ha]
  zero_mem' := by
    intro a _
    rfl
  smul_mem' := by
    intro c x hx a ha
    simp [hx a ha]
def ej (N j m : ℕ) (h : m + j = N) (i : Fin m) : Fin N → k := Pi.single (⟨j + i, by omega⟩ : Fin N) 1
end PositivityTheory.Rg.Rs.JLatOf
end


