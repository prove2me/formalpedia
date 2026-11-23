-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_HtdOf
-- name    : ReciprocityTheory_DualLattices_HtdOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:30.128831+00:00
-- url     : https://prove2.me/theorems/513ccbf9-a950-45b5-8b92-b8e053122de9
-- title:
--   Htd Of
-- statement:
--   Definitions and structural lemmas for Htd Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HtdOf.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EvLatStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EvHopfStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EvActStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EvHtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EvBtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix
namespace ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
def Dat.hopf (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] [Algebra (Tw.O : Type) C]
    (hdom : IsDomain (Tw.O : Type)) (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) : HopfOrder (C := C) (Tw.O : Type) (Nb p g) where
  carrier := D.evImg C
  lat := (hLat C hdom hinj).1
  le_int := (hLat C hdom hinj).2.1
  one_mem := (hLat C hdom hinj).2.2.1
  mul_mem := (hLat C hdom hinj).2.2.2
  comul := (hHopf C hinj).1
  antipode := (hHopf C hinj).2
def htd_of (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) (hAct : EvActStatement D)
    (hHt : EvHtStatement D) (hBt : EvBtStatement D) (hH5 : EvenTwoEvaluationSign D) (hCot : EvCotStatement D) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp where
  ρ := D.H.ρ
  ρL := D.H.ρL
  P := D.H.P
  PL := D.H.PL
  E := D.H.E
  E_alternating := D.H.E_alternating
  isUnit_det_E := D.H.isUnit_det_E
  E_equivariant := D.H.E_equivariant
  projectors := D.H.projectors
  Ht := D.H.Ht
  Bt := D.H.Bt
  Ht_equivariant := D.H.Ht_equivariant
  form_eq_alt := D.H.form_eq_alt
  AA := D.hopf C hdom hinj hLat hHopf
  h3 := fun a f hf => hAct C a f hf
  h4 := fun k => ⟨hHt C k, hBt C k⟩
  h5 := fun hp2 s => hH5 C hdom hinj hp2 s
  φ := Classical.choose (hCot C hinj)
  cotangent_surjective := (Classical.choose_spec (hCot C hinj)).1
  cotangent_ker_eq := (Classical.choose_spec (hCot C hinj)).2.1
  cotangent_linear := (Classical.choose_spec (hCot C hinj)).2.2
end ReciprocityTheory.PGsh.Be2


