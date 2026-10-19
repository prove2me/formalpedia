-- Prove2me | Definitions.Def_MazurTransfer_Order13LocalCoefficientResidueField
-- name    : MazurTransfer_Order13LocalCoefficientResidueField
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:20:44.22098+00:00
-- url     : https://prove2.me/theorems/3125e320-7065-4ecd-a73f-de95b0cdf4fa
-- title:
--   The actual residue-field isomorphism for Z localized at a prime
-- statement:
--   Let $q$ be prime and let $B_q=\mathbb Z_{(q)}$. The specified coefficient map $B_q\to\mathbf F_q$ is surjective and its kernel is the maximal ideal. It gives the original residue-field isomorphism $$\kappa(B_q)\simeq\mathbf F_q,$$ under which the canonical residue map agrees with the actual coefficient map on every element of $B_q$. This identifies the residue restriction used by the original torsion-kernel theorem with the actual finite-field specialization map.
-- source:
--   Original complete Order13LocalCoefficientResidueField.lean from MazurTheorem, Apache-2.0, Vas and contributors. All four original declarations and bodies are unchanged; the import alone becomes the public local coefficient-map Definition. Four complete original closed types and the single residue-field isomorphism value are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual rational Picard torsion detection, using the exact finite-field/residue-map factorization with the original pinned Anthropic FLT local torsion-kernel API.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual map Z_(q) to F_q is the local residue map
followed by an explicit residue-field isomorphism.
Named downstream consumer: applying the original local torsion-kernel
contract to the already constructed rational specialization maps.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps

noncomputable section
namespace MazurTransfer.Order13LocalCoefficientResidueField
open Order13LocalIntegralCoefficientMaps
variable (q : ℕ) [Fact q.Prime]

theorem localFiniteFieldMap_surjective : Function.Surjective (localFiniteFieldMap q) := by
  intro a
  obtain ⟨z,hz⟩ := ZMod.intCast_surjective a
  refine ⟨algebraMap ℤ (LocalRing q) z,?_⟩
  change IsLocalization.lift _ (algebraMap ℤ (LocalRing q) z) = a
  rw [IsLocalization.lift_eq]
  exact hz

theorem localFiniteFieldMap_ker : RingHom.ker (localFiniteFieldMap q) =
    IsLocalRing.maximalIdeal (LocalRing q) :=
  IsLocalRing.ker_eq_maximalIdeal (localFiniteFieldMap q) (localFiniteFieldMap_surjective q)

def residueFieldIso : IsLocalRing.ResidueField (LocalRing q) ≃+* ZMod q :=
  (Ideal.quotientEquivAlgOfEq ℤ (localFiniteFieldMap_ker q).symm).toRingEquiv.trans
    ((localFiniteFieldMap q).quotientKerEquivOfSurjective (localFiniteFieldMap_surjective q))

theorem residueFieldIso_residue (x : LocalRing q) :
    residueFieldIso q (IsLocalRing.residue (LocalRing q) x) = localFiniteFieldMap q x := by
  change (localFiniteFieldMap q).quotientKerEquivOfSurjective (localFiniteFieldMap_surjective q)
    ((Ideal.quotientEquivAlgOfEq ℤ (localFiniteFieldMap_ker q).symm)
      (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk,RingHom.quotientKerEquivOfSurjective_apply_mk]

end MazurTransfer.Order13LocalCoefficientResidueField
#print axioms MazurTransfer.Order13LocalCoefficientResidueField.localFiniteFieldMap_ker
#print axioms MazurTransfer.Order13LocalCoefficientResidueField.residueFieldIso_residue


