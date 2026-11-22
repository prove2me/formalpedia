-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:29.500189+00:00
-- url     : https://prove2.me/theorems/4f47732c-31d7-447b-a201-bfdb95c464fe
-- title:
--   Automorphic Forms Decomposition Holds
-- statement:
--   Definitions and structural lemmas for Automorphic Forms Decomposition Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AutomorphicFormsDecompositionHolds.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG.P
open Formalism.UG
section Rep
variable {G : Type} [Group G] (Γ K : Subgroup G)
theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (DoubleCoset.eq Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
def extend (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W) (g : G) : W :=
  ρ (Classical.choose (exists_rep Γ K s hs g)).1 (w (DoubleCoset.mk Γ K g))
end Rep
end Formalism.UG.P


