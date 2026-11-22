-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_DataS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:13.326626+00:00
-- url     : https://prove2.me/theorems/748a4c73-f697-48be-a99c-5d2b00e47f33
-- title:
--   Data S
-- statement:
--   Definitions and structural lemmas for Data S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/DataS.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.S.Draft
open Formalism.BasicNotions
open NumberField
structure SData (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (Word Tau : Type) (hc : Word → Tau → HCParam R) : Type 1 where

  cdScale : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal
  cdScale_pos : ∀ n ε, 0 < cdScale n ε

  Del : ℚ
  Del_pos : 0 < Del

  cloud_gap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del

  letter : Word → Fin (R.k - 2) → Bool

  letter_inj : Function.Injective letter

  u_letter : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
    (hc w τ).u ⟨l + 1, by omega⟩ =
      (hc w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

  HH : Type
  [hhN : NormedAddCommGroup HH]
  [hhI : InnerProductSpace ℂ HH]
  [hhF : FiniteDimensional ℂ HH]

  Cu : Word → Type
  [cuN : ∀ u, NormedAddCommGroup (Cu u)]
  [cuI : ∀ u, InnerProductSpace ℂ (Cu u)]
  [cuF : ∀ u, FiniteDimensional ℂ (Cu u)]

  Pu : ∀ u, Cu u →L[ℂ] HH

  volN : Word → ℝ
  volH : Word → ℝ
  volN_pos : ∀ u, 0 < volN u
  volH_pos : ∀ u, 0 < volH u

  Term : Word → Word → Type
  aTerm : ∀ u u', Term u u' → (Cu u' →L[ℂ] Cu u)

  isId : ∀ {u u'}, Term u u' → Prop

  inS : ∀ {u u'}, Term u u' → Prop

  relevant : ∀ {u u'}, Term u u' → Prop

  FeqF : ∀ {u u'}, Term u u' → Prop

  Gterm : ∀ {u u'}, Term u u' → F

  atP : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Formalism.MainNotions.S.Loc.LocAt F E sig p

  PlF : Type
  BBne : ∀ {u u'}, Term u u' → PlF → Prop

  generic : ∀ {u u'}, Term u u' → Prop

  Pair : Word → Word → Type
  pfst : ∀ {u u'}, Pair u u' → Term u u'
  psnd : ∀ {u u'}, Pair u u' → Term u u'
  s0 : ∀ {u u'}, Pair u u' → ℕ
  scalarPair : ∀ {u u'}, Pair u u' → Prop

  pval : ∀ {u u'}, Pair u u' → ℂ

  ptOf : ∀ {u u'}, Term u u' → Formalism.MainNotions.S.Point E (R.rS + 1)

  cTerm : ∀ {u u'}, Term u u' → ℂ

  massPair : ∀ {u u'}, Pair u u' → ℝ

  meanCount : Word → Word → Formalism.MainNotions.S.Point E (R.rS + 1) → ℝ
attribute [instance] SData.hhN SData.hhI SData.hhF SData.cuN SData.cuI SData.cuF
end Formalism.MainNotions.S.Draft


