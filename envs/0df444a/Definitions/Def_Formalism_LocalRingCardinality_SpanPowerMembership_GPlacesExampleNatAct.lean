-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:26.333749+00:00
-- url     : https://prove2.me/theorems/9e0ef245-3b41-42b1-9fc4-02b376b85520
-- title:
--   GPlaces Example Nat Act
-- statement:
--   Definitions and structural lemmas for GPlaces Example Nat Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions NumberField IsDedekindDomain
section S
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)
def locAdj (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) : Formalism.MainNotions.S.Loc.LocAt F E sig p :=
  { loc p with split := if h : Formalism.MainNotions.S.Loc.resChar p ∈ G then some (spl p h) else none }
variable {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)
def toySData (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc where
  cdScale := fun _ _ => 1
  cdScale_pos := fun _ _ => one_pos
  Del := Del
  Del_pos := hDel
  cloud_gap := hgap
  letter := fun _ _ => false
  letter_inj := fun _ _ _ => Subsingleton.elim _ _
  u_letter := by
    intro w τ l h
    simp [hlet w τ l h]
  HH := EuclideanSpace ℂ (Fin 0)
  Cu := fun _ => EuclideanSpace ℂ (Fin 0)
  Pu := fun _ => 0
  volN := fun _ => 1
  volH := fun _ => 1
  volN_pos := fun _ => one_pos
  volH_pos := fun _ => one_pos
  Term := fun _ _ => Empty
  aTerm := fun _ _ t => t.elim
  isId := fun _ => False
  inS := fun _ => False
  relevant := fun _ => False
  FeqF := fun _ => False
  Gterm := fun t => t.elim
  atP := loc
  PlF := HeightOneSpectrum (𝓞 F)
  BBne := fun _ _ => False
  generic := fun _ => False
  Pair := fun _ _ => Empty
  pfst := fun t => t.elim
  psnd := fun t => t.elim
  s0 := fun _ => 0
  scalarPair := fun _ => False
  pval := fun _ => 0
  ptOf := fun t => t.elim
  cTerm := fun _ => 0
  massPair := fun _ => 0
  meanCount := fun _ _ _ => 0
variable {sig hc}
def toySData_Cu (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) (u : Word)
    {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (hM : M = ⊥) :
    (toySData sig hc Del hDel hgap hlet loc).Cu u ≃ₗ[ℂ] M := by
  subst hM
  haveI : Subsingleton (EuclideanSpace ℂ (Fin 0)) := ⟨fun a b => by ext i; exact i.elim0⟩
  exact LinearEquiv.ofSubsingleton (EuclideanSpace ℂ (Fin 0)) (⊥ : Submodule ℂ V)
def toySData_PlF (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).PlF ≃ HeightOneSpectrum (𝓞 F) := Equiv.refl _
end S
section G
open Formalism.MainNotions.G
def emptyPlaces (p : ℕ) : Places p ℤ_[3] ℚ_[3] where
  w := 0
  nV := 0
  n' := fun v => v.elim0
  W := fun v => v.elim0
  Qq := fun v => v.elim0
  ringW := fun v => v.elim0
  domW := fun v => v.elim0
  dvrW := fun v => v.elim0
  fieldQ := fun v => v.elim0
  algWQ := fun v => v.elim0
  ι := fun v => v.elim0
  σ := fun v => v.elim0
  j := fun v => v.elim0
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun v => v.elim0
  dom := fun v => v.elim0
instance (p : ℕ) : Unique (emptyPlaces p).Tup :=
  inferInstanceAs (Unique (∀ _ : Fin 0, _))
def toySignLevel (p : ℕ) : Level (emptyPlaces p) where
  Γ := ℤˣ
  act := fun v => v.elim0
  χ := Units.map (Int.castRingHom ℤ_[3]).toMonoidHom
def gAtPExample (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => toySignLevel p
  e := 0
instance (p : ℕ) : Unique (gAtPExample p).P.Tup := inferInstanceAs (Unique (emptyPlaces p).Tup)
end G
end Formalism.BasicNotions.Examples₂


