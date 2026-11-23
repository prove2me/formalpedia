-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
-- name    : Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:54.365749+00:00
-- url     : https://prove2.me/theorems/c452e1ad-2456-4bfb-8089-4676b040df34
-- title:
--   Model At
-- statement:
--   Definitions and structural lemmas for Model At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/RegularCharts/ModelAt.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Theorems.Thm_Formalism_L2_Pj_OverLa_bc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.Reg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable (Xo c) in

def FrBC : Prop :=
  ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z
variable (Xo c) in

structure EvLaws : Prop where
  wd : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
  test : AllTest Xo c
  wt : WtField Xo c
  bc : FrBC Xo c
variable (Xo c) in

structure PChart {O : Type} [CommRing O] (β : O →+* c.F) where
  Ω : Type
  [fld : Field Ω]
  [alg : Algebra c.F Ω]
  gens : Finset Ω
  frac : Subfield.closure (Set.range (algebraMap c.F Ω) ∪ (gens : Set Ω)) = ⊤
  es : Finset Ω
  es_ne : es.Nonempty
  es_mem : ∀ e ∈ es, e ≠ 0 ∧ e ∈ Subring.closure (Set.range ((algebraMap c.F Ω).comp β) ∪ (gens : Set Ω))
  sm : ∀ e ∈ es, Algebra.Smooth c.F (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)))
  yg : FrPt Xo c Ω
  y : ∀ e ∈ es, FrPt Xo c (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)))
  gen : ∀ e (he : e ∈ es), FrMap (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (y e he) yg
  int : ∀ e (he : e ∈ es) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (ψ : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)) →ₐ[c.F] T.Fr),
      (∀ a : O, io (β a) ∈ Set.range (algebraMap T.V T.Fr)) →
      (∀ g : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → ψ g ∈ Set.range (algebraMap T.V T.Fr)) →
      ∀ z : FrPt Xo c T.Fr, FrMap ψ (y e he) z → Integral T io z
attribute [instance] PChart.fld PChart.alg
variable {O : Type} [CommRing O] {β : O →+* c.F}
abbrev PChart.R (P : PChart Xo c β) (e : P.Ω) : Subalgebra c.F P.Ω :=
  Algebra.adjoin c.F (insert e⁻¹ (P.gens : Set P.Ω))
abbrev PChart.B (P : PChart Xo c β) : Subring P.Ω :=
  Subring.closure (Set.range ((algebraMap c.F P.Ω).comp β) ∪ (P.gens : Set P.Ω))
def PChart.Catches (P : PChart Xo c β) {L : Type} [Field L] [Algebra c.F L] (W : ValuationSubring L)
    (y : FrPt Xo c L) : Prop :=
  ∃ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
    (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) ∧ FrMap ψ (P.y e he) z ∧ FrBor t y z
def Covers {J : Type} (P : J → PChart Xo c β) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (β a) ∈ W) →
    ∀ y : FrPt Xo c L, ∃ j, (P j).Catches W y
def PChart.Fam (P : PChart Xo c β) {m : ℕ} (ws : Fin m → Rul Xo c) : Prop :=
  ∃ k, evR Xo c (ws k) P.yg ≠ 0 ∧ (∀ i, evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg ∈ P.B) ∧
    ∀ e ∈ P.es, (evR Xo c (ws k) P.yg)⁻¹ ∈ P.R e
variable (Xo c) in

def ModelAt (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L
end GlobalTheory.Reg


