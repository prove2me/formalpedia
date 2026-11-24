-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:31.933319+00:00
-- url     : https://prove2.me/theorems/2671c09c-8721-46a5-af38-ca752f010db3
-- title:
--   Even Step
-- statement:
--   Definitions and structural lemmas for Even Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/EvenStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.BlockRatReal
def EvenStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf lam), ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
        (M0.1.map embLL * y).det ^ lam (Fin.last m) *
            eval (fun x => (M0.1.map embLL * y) x.1 x.2) (MvPolynomial.map embLL F) =
          y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)
def OddStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf fun i => -lam i.rev),
        ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
          (((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev).det ^ (-lam (Fin.last m).rev) *
              eval (fun x => ((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev x.1 x.2) (MvPolynomial.map embLL F) =
            y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)
end PI.BlockRatReal


