-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
-- name    : Formalism_PeriodIntegrals_LocLatSat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:15:30.749165+00:00
-- url     : https://prove2.me/theorems/f088d16e-6098-4aba-b078-7f33f002f475
-- title:
--   Loc Lat Sat
-- statement:
--   Definitions and structural lemmas for Loc Lat Sat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocLatSat.lean

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
namespace PI.LocLatSat
def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)
def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))
def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (W : Submodule E (Fin n → E)), Λ.FG →
    (latL A (Λ ⊓ W.restrictScalars (𝓞 E)) : Set (Fin n → A.Ep)) =
      (latL A Λ : Set (Fin n → A.Ep)) ∩ Submodule.span A.Ep (bc A '' (W : Set (Fin n → E)))
end PI.LocLatSat


