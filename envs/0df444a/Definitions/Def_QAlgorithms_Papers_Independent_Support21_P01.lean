-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01
-- name    : QAlgorithms_Papers_Independent_Support21_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:26:36.352935+00:00
-- url     : https://prove2.me/theorems/9d2a41c7-fa24-49e0-8c9a-999e29f4d2d9
-- title:
--   Definitions for Cellularity and the Jones basic construction
-- statement:
--   The objects the formalized statements of *Cellularity and the Jones basic construction* (arXiv:0906.1496) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `balancingSubmodule`: Balancing relations for right M_A and left _A N, used on PDF pp.4,15. The right action is encoded by a left action of A's opposite ring.
--   - `BalancedTensor`: The actual R-module underlying M tensor_A N (PDF pp.4,15). Only the quotient and its simple tensors are constructed here; descended outer bimodule actions and functorial maps are separately deferred.
--   - `balancedTmul`: Canonical simple tensor in the noncommutative balanced quotient, PDF pp.4,15.
--   - `strictifiedCellBasis`: Remark 2.4(2), PDF p.5: the displayed half-error adjustment. Here half denotes the inverse of 2, and the source's f(lambda,t,s) is exactly i(c(lambda,t,s)) - c(lambda,s,t).
-- source:
--   Cellularity and the Jones basic construction, arXiv:0906.1496v2, https://arxiv.org/abs/0906.1496v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

/-!
Draft statements from Goodman and Graber, Cellularity and the Jones basic
construction, arXiv:0906.1496v2. The accepted Renew46.P16 import is used only
for CellIndex and IsWeakCellularBasis, checked against Definition 2.3 here.
All other planned nodes are accounted for in this unit's HARD.md and GAPS.json.
Compilation and independent moderation are pending under the batch handoff.
-/

noncomputable section

open scoped TensorProduct

namespace QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

section BalancedTensor

variable (R A M N : Type*) [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- Balancing relations for right M_A and left _A N, used on PDF pp.4,15.
The right action is encoded by a left action of A's opposite ring. -/
def balancingSubmodule : Submodule R (M ⊗[R] N) :=
  Submodule.span R {z | ∃ (m : M) (a : A) (n : N),
    z = TensorProduct.tmul R (MulOpposite.op a • m) n -
      TensorProduct.tmul R m (a • n)}

/-- The actual R-module underlying M tensor_A N (PDF pp.4,15).
Only the quotient and its simple tensors are constructed here; descended
outer bimodule actions and functorial maps are separately deferred. -/
abbrev BalancedTensor := (M ⊗[R] N) ⧸ balancingSubmodule R A M N

/-- Canonical simple tensor in the noncommutative balanced quotient,
PDF pp.4,15. -/
def balancedTmul (m : M) (n : N) : BalancedTensor R A M N :=
  (balancingSubmodule R A M N).mkQ (TensorProduct.tmul R m n)

/-- Sanity check: the quotient imposes precisely the generating balance equation. -/
example (m : M) (a : A) (n : N) :
    balancedTmul R A M N (MulOpposite.op a • m) n =
      balancedTmul R A M N m (a • n) := by
  apply (Submodule.Quotient.eq (balancingSubmodule R A M N)).mpr
  exact Submodule.subset_span ⟨m, a, n, rfl⟩

end BalancedTensor

/-- Remark 2.4(2), PDF p.5: the displayed half-error adjustment.
Here half denotes the inverse of 2, and the source's f(lambda,t,s) is
exactly i(c(lambda,t,s)) - c(lambda,s,t). -/
def strictifiedCellBasis
    {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (i : A →ₗ[R] A)
    (half : R) : CellIndex L T → A :=
  fun z => c z + half • (i (c ⟨z.1, (z.2.2, z.2.1)⟩) - c z)

/-- Sanity check: a basis already swapped exactly by i is unchanged. -/
example {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (i : A →ₗ[R] A)
    (half : R) (h : ∀ (l : L) (s t : T l),
      i (c ⟨l, (t, s)⟩) = c ⟨l, (s, t)⟩) :
    strictifiedCellBasis c i half = c := by
  funext z
  simp [strictifiedCellBasis, h]

end QAlgorithms.Papers.Independent.Support21.P01


