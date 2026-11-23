-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
-- name    : Formalism_PeriodIntegrals_LocDualGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:22.781359+00:00
-- url     : https://prove2.me/theorems/0e7463e0-8681-4134-87ec-12803cce7fec
-- title:
--   Loc Dual Gen
-- statement:
--   Definitions and structural lemmas for Loc Dual Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocDualGen.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocDualGen
def DualAtL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (δ : A.Fp) : Prop :=
  ∀ x : A.Ep, (∀ y ∈ A.O, A.psiE (-(x * y * algebraMap A.Fp A.Ep δ⁻¹)) = 1) ↔ x ∈ A.O
def UnramL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) : Prop :=
  ∀ ϖ : 𝒪[A.Fp], Irreducible ϖ → ∀ x ∈ A.O,
    x * x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)} →
      x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)}
def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    (IsReduced A.Ep → UnramL A → ∃ δ : A.Fp, δ ≠ 0 ∧ DualAtL A δ) ∧
    (∀ (δ : A.Fp) (u : 𝒪[A.Fp]), IsUnit u → DualAtL A δ → DualAtL A (δ * (u : A.Fp))) ∧
    (IsReduced A.Ep → UnramL A → Irreducible ((resChar p : ℕ) : 𝒪[A.Fp]) → DualAtL A 1)
end PI.LocDualGen


