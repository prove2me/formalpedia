-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AuxiliaryNormPrimes
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AuxiliaryNormPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:23.253128+00:00
-- url     : https://prove2.me/theorems/24c24123-27d6-49a5-9b84-de8628433bae
-- title:
--   Auxiliary Norm Primes
-- statement:
--   Definitions and structural lemmas for Auxiliary Norm Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AuxiliaryNormPrimes.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyNu.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → ℝ :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ ‖z‖) (Multiset.filter (fun (z : L) ↦ (1 : ℝ) ≤ ‖z‖) R)).prod
noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyF.{u_1} :
    {L : Type u_1} → [inst : NormedField L] → Multiset L → Polynomial L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ Polynomial.X - (Polynomial.C : L → Polynomial L) z) R).prod
noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyP.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → Multiset L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦ Multiset.filter (fun (z : L) ↦ ‖z‖ < (1 : ℝ)) R


