-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:21.616632+00:00
-- url     : https://prove2.me/theorems/cff40d5f-fc66-4f16-a357-f9cede6d21b2
-- title:
--   Fundamental Domain Pi Basis
-- statement:
--   Definitions and structural lemmas for Fundamental Domain Pi Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallC
variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]
def psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    (ι → mixedSpace K) ≃ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) where
  toFun y := fun w i => (y i).2 w
  invFun z := fun i => (fun w => isEmptyElim w, fun w => z w i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv z := rfl
def piBasis : Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (ι → mixedSpace K) :=
  Pi.basis fun _ => latticeBasis K
end Formalism.HermitianLattices.Ext.L3.BallC


