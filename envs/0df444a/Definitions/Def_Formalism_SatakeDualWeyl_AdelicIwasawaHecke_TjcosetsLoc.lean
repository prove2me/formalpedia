-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:17.324326+00:00
-- url     : https://prove2.me/theorems/a55c8002-427b-41e6-8c7f-5ff7a8e89314
-- title:
--   Tjcosets Loc
-- statement:
--   Definitions and structural lemmas for Tjcosets Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
section Loc
variable {L : Type} [Field L]
theorem tjcosets_bc_injective (n : ℕ) (O : Subring L) :
    Function.Injective (bc (n := Fin n) O.subtype) := by
  intro g h hgh
  refine Units.ext (Matrix.ext fun a b => Subtype.ext ?_)
  have := congrArg (fun u : GL (Fin n) L => (u : Matrix (Fin n) (Fin n) L) a b) hgh
  exact this
def tjcosets_iso (n : ℕ) (O : Subring L) : GL (Fin n) O ≃* GLint (Fin n) O :=
  MonoidHom.ofInjective (tjcosets_bc_injective n O)
variable (O : Subring L) [IsLocalRing O]
def tjcosets_red (n : ℕ) : GLint (Fin n) O →* GL (Fin n) (IsLocalRing.ResidueField O) :=
  (bc (IsLocalRing.residue O)).comp (tjcosets_iso n O).symm.toMonoidHom
variable {O}
def tjcosets_dG (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) : GL (Fin n) L :=
  ⟨diagJ n ϖ j, diagJ n ϖ⁻¹ j, by
    unfold diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ], by
    unfold diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ]⟩
end Loc
end Formalism.UG.P


