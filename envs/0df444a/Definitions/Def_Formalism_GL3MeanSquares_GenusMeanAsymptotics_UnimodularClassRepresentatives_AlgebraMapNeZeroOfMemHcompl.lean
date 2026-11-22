-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:18.065826+00:00
-- url     : https://prove2.me/theorems/2b5d98de-2fdf-4cb2-9fb4-33d2557477a3
-- title:
--   Algebra Map Ne Zero Of Mem Hcompl
-- statement:
--   Definitions and structural lemmas for Algebra Map Ne Zero Of Mem Hcompl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapNeZeroOfMemHcompl.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_one_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def locRing (p : Ideal (𝓞 K)) : Subring K where
  carrier := {a | a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p}
  mul_mem' := by
    intro a b ha hb
    change a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at ha
    change b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at hb
    change a * b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha hb ⊢
    obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have e : algebraMap (𝓞 K) K (s * t) * (a * b) =
        (algebraMap (𝓞 K) K s * a) * (algebraMap (𝓞 K) K t * b) := by
      rw [map_mul]; ring
    rw [e]
    exact Formalism.HermitianLatticesTheory.locDual_one_mul h1 h2
  one_mem' := by
    change (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, mul_one]; exact Submodule.one_le.mp le_rfl⟩
  add_mem' := fun ha hb => (Formalism.HermitianLatticesTheory.locR (K := K) p).add_mem ha hb
  zero_mem' := (Formalism.HermitianLatticesTheory.locR (K := K) p).zero_mem
  neg_mem' := fun ha => (Formalism.HermitianLatticesTheory.locR (K := K) p).neg_mem ha
end Formalism.HermitianLattices.Ext.L3.WA


