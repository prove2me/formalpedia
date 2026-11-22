-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:10.003414+00:00
-- url     : https://prove2.me/theorems/daa3900d-ad93-499b-949b-b20922e15b29
-- title:
--   Un Free
-- statement:
--   Definitions and structural lemmas for Un Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
structure Unf (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) : Type 1 where

  Comp : Type
  [fin : Fintype Comp]

  X : Comp → Data E r

  un : ∀ k, (X k).dom → FrPt Xo c (CAt σ)
attribute [instance] Unf.fin
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
def gxFst {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Xo.univ.t.G.left :=
  (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left
def gxSnd {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Sp S :=
  (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left
def toC {K : Type} [Field K] {σ : K →+* ℂ} (z : CAt σ) : ℂ := z
open Classical in

def rdU (U : Unf Xo c σ r) : Rul Xo c →ₛₗ[σ] FDSec U.X where
  toFun f := fun k x => if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0
  map_add' f g := by
    funext k x
    simp only [Pi.add_apply]
    split_ifs with h
    · have e := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
      exact e
    · simp
  map_smul' a f := by
    funext k x
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (U.un k ⟨x, h⟩)
      exact e
    · simp
def relab (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) : E →+* ℂ := σ.comp (embF c τ)
def GoodEmb (c : Coeff l) (σ : c.F →+* ℂ) : Prop :=
  (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0
open Classical in

def laU (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
    else -(a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ)
open Classical in

def perFr (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) : ℂ :=
  if h : τ ∈ X.Ψ then
    (if hi : X.p0 + i < r then ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ v)) ⟨X.p0 + i, hi⟩ else 0)
  else if h' : conjEmb τ ∈ X.Ψ then
    (if hj : X.p0 - 1 - i < r then
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, hj⟩) (Data.emb (conjEmb τ) v) else 0)
  else 0
def IsUnf (U : Unf Xo c σ r) : Prop :=
  r = Dw.p + Dw.q ∧ (∀ k, (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) ∧
    (∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y) ∧
    (∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom), (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) (U.un k' x')) ↔
      ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (U.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩) ∧
    (∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, (U.X k).IsSec (laU U a n k) (rdU U f k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ),
      (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
      ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          ((U.un k x).u τ i)) ∧
        ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)
end Formalism.L2.PjFree


