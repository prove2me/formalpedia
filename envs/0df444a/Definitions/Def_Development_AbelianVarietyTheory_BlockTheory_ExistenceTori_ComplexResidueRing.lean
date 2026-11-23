-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ComplexResidueRing
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ComplexResidueRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:16.971807+00:00
-- url     : https://prove2.me/theorems/13aeba3f-f9d4-4678-ad2c-7fc66d0ccba7
-- title:
--   Complex Residue Ring
-- statement:
--   Definitions and structural lemmas for Complex Residue Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ComplexResidueRing.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {c c' : Coeff l}
def incl (h : c.F ≤ c'.F) : c.F →+* c'.F := (IntermediateField.inclusion h).toRingHom
def Res (_h : c.F ≤ c'.F) (S : Type) : Type := S
instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] : CommRing (Res h S) := inferInstanceAs (CommRing S)
instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F (Res h S) :=
  ((algebraMap c'.F S).comp (incl h)).toAlgebra
def unRes {h : c.F ≤ c'.F} {S : Type} [CommRing S] : Res h S ≃+* S := RingEquiv.refl S
variable {Xo : Moduli Dw l}
def ptDown (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FrPt Xo c (Res h S) where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen
def ptUp (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c (Res h S)) :
    FrPt Xo c' S where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen
def ptEquiv (h : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : FrPt Xo c' S ≃ FrPt Xo c (Res h S) where
  toFun := ptDown h
  invFun := ptUp h
  left_inv _ := rfl
  right_inv _ := rfl
def embRes (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) : c.F →+* ℂ := σ'.comp (incl h)
variable {r : ℕ}
def unfUp (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) (U : Unf Xo c (embRes h σ') r) : Unf Xo c' σ' r where
  Comp := U.Comp
  fin := U.fin
  X := U.X
  un k x := ptUp h (S := CAt σ') (U.un k x)
def unfFamUp (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : ∀ σ' : c'.F →+* ℂ, Unf Xo c' σ' r :=
  fun σ' => unfUp h σ' (U (embRes h σ'))
def ruleUp (h : c.F ≤ c'.F) : Rul Xo c →ₛₗ[incl h] Rul Xo c' where
  toFun f := fun p y => unRes (evR Xo c f (ptDown h y))
  map_add' f g := by
    funext p y
    exact evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (ptDown h y)
  map_smul' a f := by
    funext p y
    have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (ptDown h y)
    show _ = incl h a • (unRes (evR Xo c f (ptDown h y)) : p.R)
    exact e.trans (Algebra.smul_def (incl h a) (unRes (evR Xo c f (ptDown h y)) : p.R)).symm
def IsComb (h : c.F ≤ c'.F) {m : ℕ} (b : Fin m → c'.F) (f : Fin m → Rul Xo c) (f' : Rul Xo c') : Prop :=
  ∀ (p : TRing c'.F) (y : FrPt Xo c' p.R),
    f' p y = ∑ i, algebraMap c'.F p.R (b i) * unRes (evR Xo c (f i) (ptDown h y))
variable (Xo)
def CuspIsComb (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f' ∈ cusp Xo c' (unfFamUp h U) a n, ∃ (m : ℕ) (b : Fin m → c'.F) (f : Fin m → Rul Xo c),
    (∀ i, f i ∈ cusp Xo c U a n) ∧ IsComb h b f f'
def CombIsCusp (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (m : ℕ) (b : Fin m → c'.F) (f : Fin m → Rul Xo c) (f' : Rul Xo c'),
    (∀ i, f i ∈ cusp Xo c U a n) → IsComb h b f f' → f' ∈ cusp Xo c' (unfFamUp h U) a n
def CuspIndep (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (m : ℕ) (b : Fin m → c'.F) (f : Fin m → Rul Xo c),
    (∀ i, f i ∈ cusp Xo c U a n) → LinearIndependent c.F f → IsComb h b f 0 → b = 0
def CuspBaseChange (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  CuspIsComb Xo h U a n ∧ CombIsCusp Xo h U a n ∧ CuspIndep Xo h U a n
def ActionExtends (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {G : Type} [Group G] (ρ : G →* Module.End c.F (cusp Xo c U a n))
    (ρ' : G →* Module.End c'.F (cusp Xo c' (unfFamUp h U) a n)) : Prop :=
  ∀ (g : G) (m : ℕ) (b : Fin m → c'.F) (f : Fin m → cusp Xo c U a n) (f' : cusp Xo c' (unfFamUp h U) a n),
    IsComb h b (fun i => (f i : Rul Xo c)) (f' : Rul Xo c') →
      IsComb h b (fun i => (ρ g (f i) : Rul Xo c)) (ρ' g f' : Rul Xo c')
example (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {G : Type} [Group G] : ActionExtends Xo h U a n (G := G) 1 1 :=
  fun _ _ _ _ _ hf => hf
end GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing


