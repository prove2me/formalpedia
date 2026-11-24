-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:12.29317+00:00
-- url     : https://prove2.me/theorems/974df69e-09cd-4f38-a002-cd35a70029c0
-- title:
--   Jacobi Minor Identity
-- statement:
--   Definitions and structural lemmas for Jacobi Minor Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
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
namespace PI.OddDualWeyl.Jac
end PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl.Jac
def mkE {a b k : ℕ} (f : Fin a → Fin k) (g : Fin b → Fin k) (h : a + b = k)
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Fin a ⊕ Fin b ≃ Fin k :=
  Equiv.ofBijective (Sum.elim f g) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hf.sumElim hg hfg, by simp [h]⟩)
def eR (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x) (fun y => Fin.rev (Fin.castLE hs y)) (by omega)
    (Fin.castLE_injective _) (Fin.rev_injective.comp (Fin.castLE_injective _))
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)
def eL (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.rev (Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x)) (fun y => Fin.castLE hs y) (by omega)
    (Fin.rev_injective.comp (Fin.castLE_injective _)) (Fin.castLE_injective _)
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)
end PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl
end PI.OddDualWeyl


