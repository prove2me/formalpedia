-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNineteenKernelAnnihilationExplicitPublicNorm20261017
-- name    : MazurTransfer_Order13ActualPicardNineteenKernelAnnihilationExplicitPublicNorm20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:51:34.121486+00:00
-- url     : https://prove2.me/theorems/e71b549e-e81c-487a-9847-0a70f70b1ccb
-- title:
--   The original literal arithmetic Picard norm kernels are annihilated by nineteen
-- statement:
--   For the original actual arithmetic Picard endomorphisms, the reverse product piConjugate*pi equals nineteen, and any class killed by either pi or piConjugate is killed by nineteen. All three original full theorem types and unchanged proofs are retained. Named downstream consumer: original rational Picard nineteen descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardCyclotomicNorm converse product and two kernel annihilation proofs, using the accepted literal norm product and published original endomorphism constructors. Official Anthropic FLT arithmetic Pic0 interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The three original converse-product and kernel annihilation proofs are retained.
Design boundary: the original pi and piConjugate kernels are killed by nineteen.
Named downstream consumer: original rational Picard nineteen descent.
Official Anthropic FLT arithmetic Pic0 interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardCyclotomicNorm_pi_comp_piConjugate_nineteen
noncomputable section
namespace MazurTransfer.Order13ActualPicardCyclotomicNorm
open Order13ActualDiamondPicardEndomorphisms
theorem piConjugate_comp_pi_nineteen : piConjugate * pi = 19 :=
  piConjugate_comp_pi.trans (pi_comp_piConjugate.symm.trans pi_comp_piConjugate_nineteen)

theorem nineteen_nsmul_eq_zero_of_pi_eq_zero {c : ActualPicard} (hc : pi c = 0) :
    (19 : ℕ) • c = 0 := by
  have h := congrArg (fun f : AddMonoid.End ActualPicard => f c)
    piConjugate_comp_pi_nineteen
  change piConjugate (pi c) = (19 : ℕ) • c at h
  rw [hc, map_zero] at h
  exact h.symm

theorem nineteen_nsmul_eq_zero_of_piConjugate_eq_zero {c : ActualPicard}
    (hc : piConjugate c = 0) : (19 : ℕ) • c = 0 := by
  have h := congrArg (fun f : AddMonoid.End ActualPicard => f c)
    pi_comp_piConjugate_nineteen
  change pi (piConjugate c) = (19 : ℕ) • c at h
  rw [hc, map_zero] at h
  exact h.symm

end MazurTransfer.Order13ActualPicardCyclotomicNorm
#print axioms MazurTransfer.Order13ActualPicardCyclotomicNorm.nineteen_nsmul_eq_zero_of_pi_eq_zero
#print axioms MazurTransfer.Order13ActualPicardCyclotomicNorm.nineteen_nsmul_eq_zero_of_piConjugate_eq_zero


