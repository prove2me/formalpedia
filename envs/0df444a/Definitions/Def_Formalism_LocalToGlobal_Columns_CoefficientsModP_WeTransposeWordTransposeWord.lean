-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
-- name    : Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.877915+00:00
-- url     : https://prove2.me/theorems/0d6ed77e-db39-4fce-9d16-05c4f495cac8
-- title:
--   We Transpose Word Transpose Word
-- statement:
--   Definitions and structural lemmas for We Transpose Word Transpose Word, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/WeTransposeWordTransposeWord.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQBilin
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
theorem we_fock_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := (fockQPos σ f g).1
theorem we_fock_add_left {σ : Type} (f f' g : MvPolynomial σ ℚ) : fockQ (f + f') g = fockQ f g + fockQ f' g :=
  (fockQBilin σ f f' g 0).1
theorem we_fock_smul_left {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ (c • f) g = c * fockQ f g :=
  (fockQBilin σ f 0 g c).2
theorem we_fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [we_fock_symm, we_fock_add_left, we_fock_symm g, we_fock_symm g']
theorem we_fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [we_fock_symm, we_fock_smul_left, we_fock_symm g]
section Double
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
def weForm : (dualWeyl ℚ r n ν) →ₗ⋆[ℚ] (dualWeyl ℚ r n ν) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℚ) (RingHom.id ℚ)
    (fun x y => fockQ x.1 y.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν))
    (by intro x x' y; simp only [Submodule.coe_add, we_fock_add_left, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul, mul_div_assoc])
    (by intro x y y'; simp only [Submodule.coe_add, we_fock_add_right, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_right, RingHom.id_apply, smul_eq_mul, mul_div_assoc])
def weCut (r n : ℕ) (ν : Fin n → ℕ) (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (dualWeyl ℚ r n ν) :=
  S.comap ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
end Double
end Formalism.L2.DIV


