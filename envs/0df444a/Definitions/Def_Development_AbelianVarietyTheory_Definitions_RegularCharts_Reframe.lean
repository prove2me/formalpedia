-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
-- name    : Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:15.088606+00:00
-- url     : https://prove2.me/theorems/c6a4b125-e2c8-4353-9e7c-81f4130f33ec
-- title:
--   Reframe
-- statement:
--   Definitions and structural lemmas for Reframe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/RegularCharts/Reframe.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Reg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def lowM {T S : Type} [CommRing S] {r : T → ℕ} (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    Matrix (Fin (r τ)) (Fin (r τ)) S :=
  fun j i => if h : i < j then x ⟨τ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0
def Reframe {S : Type} [CommRing S] [Algebra c.F S]
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ∧ ∀ τ i, IsCombAt y.x (y.u τ) (fun j => g τ j i) (y'.u τ i)
structure FChart (h : GenFrEx Xo c) where
  Z : Comp Xo c
  R : Subalgebra c.F (Om Z)
  sm : Algebra.Smooth c.F R
  frac : ∀ x : Om Z, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a
  y : FrPt Xo c R
  yg : FrPt Xo c (Om Z)
  t : Ix Dw → (Om Z)ˣ
  gen : FrMap R.val y yg
  bor : FrBor t (genFr h Z) yg
  mono : ∀ (L : Type) [Field L] [Algebra c.F L] (ψ ψ' : R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t' : Ix Dw → Lˣ),
    FrMap ψ y z → FrMap ψ' y z' → FrBor t' z z' → ψ = ψ'
  opn : ∀ (S L : Type) [CommRing S] [Algebra c.F S] [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c S)
    (wL : FrPt Xo c L), FrMap χ w wL →
    (∃ (ψ : R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ y z ∧ FrBor t' z wL) →
    ∃ g : S, χ g ≠ 0 ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (lam : S →ₐ[c.F] S'), IsUnit (lam g) →
      ∀ w' : FrPt Xo c S', FrMap lam w w' →
        ∃ (ψ : R →ₐ[c.F] S') (z : FrPt Xo c S') (t' : Ix Dw → S'ˣ), FrMap ψ y z ∧ FrBor t' z w'
def Atlas (h : GenFrEx Xo c) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y
end GlobalTheory.Reg


