-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:19.377502+00:00
-- url     : https://prove2.me/theorems/960b6c26-f67e-5102-a7cd-f9471fb535b5
-- title:
--   Integral Of Module
-- statement:
--   Definitions and structural lemmas for Integral Of Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/IntegralOfModule.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
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
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
namespace CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
section Loc
variable (s : SplitPlace L) (n)
def dg {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) : GL (Fin n) (s.v.adicCompletion L⁺) :=
  ⟨diagJ n ϖ k, Matrix.diagonal fun i => if (i : ℕ) < k then ϖ⁻¹ else 1,
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0],
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0]⟩
variable {n}
variable {s}
end Loc
section TypeSp
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}
end TypeSp
section Same
variable {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
end Same
section Int
variable {R : Type} [CommRing R] [Algebra R ℂ]
end Int
end CompanionTheory.L3H


