-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:24.051656+00:00
-- url     : https://prove2.me/theorems/92aefc32-5d61-48c2-9108-98cf8f86cc3a
-- title:
--   Exists Tame Gen
-- statement:
--   Definitions and structural lemmas for Exists Tame Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
def rat (σ : G E Ω) : Ωˣ →* Ωˣ := (Units.map (σ : Ω →* Ω)) / MonoidHom.id _
variable [IsAlgClosure E Ω]
def Near {A' : Type} [Group A'] (φ : G E Ω →* A') (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → (∀ κ ∈ φ.ker, κ y = y) → A.valuation (σ y / y - 1) < 1
structure Test (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Type 1 where
  A' : Type
  [grp : Group A']
  [fin : Finite A']
  φ : G E Ω →* A'
  ho : IsOpen (φ.ker : Set (G E Ω))
attribute [instance] Test.grp Test.fin
def Test.prod {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (s t : Test E Ω) : Test E Ω where
  A' := s.A' × t.A'
  φ := s.φ.prod t.φ
  ho := by rw [MonoidHom.ker_prod]; exact s.ho.inter t.ho
end Formalism.BasicNotions.Examples₂.Tame


