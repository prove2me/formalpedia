-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:44.14874+00:00
-- url     : https://prove2.me/theorems/02f83f35-dc00-4921-b484-d18e66aab021
-- title:
--   Chart Chg
-- statement:
--   Definitions and structural lemmas for Chart Chg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ChartChg.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
section Defs
variable {k : Type} [CommRing k] {d : ℕ}
def dLin (φ : Pt k 1 d) : Matrix (Fin d) (Fin d) k :=
  fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)
def transF (F : Fin d → PS k 2 d) (φ φi : Pt k 1 d) : Fin d → PS k 2 d :=
  fun i => ev (n := 2) ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))] (φi i)
def IsInvPair (φ φi : Pt k 1 d) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧ (∀ i, constantCoeff (φi i) = 0) ∧
    comp1 φ φi = pt k (n := 1) d 0 ∧ comp1 φi φ = pt k (n := 1) d 0
def colM {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => m (l, b)
end Defs
def LogSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ ℓ : Pt k 1 d,
    (∀ i, constantCoeff (ℓ i) = 0) ∧ dLin ℓ = 1 ∧
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)
def LogDerivSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ : Pt k 1 d),
    (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    ∀ (u : Fin d → k) (g : PS k 1 d),
      Dof G.F u (ev (n := 1) ![ℓ] g) = ev (n := 1) ![ℓ] (∑ j, C (u j) * pderiv k ((0 : Fin 1), j) g)
def ChainSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
    ∀ (g : PS k 1 d) (j : Fin d),
      pderiv k ((0 : Fin 1), j) (ev (n := 1) ![φ] g) =
        ∑ i, ev (n := 1) ![φ] (pderiv k ((0 : Fin 1), i) g) * pderiv k ((0 : Fin 1), j) (φ i)
def ConstSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
    ∀ g : PS k 1 d, constantCoeff (ev (n := 1) ![φ] g) = constantCoeff g
def TransPolySt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (F : Fin d → PS k 2 d), (∀ i, constantCoeff (F i) = 0) →
    (∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d)) →
    ∀ φ φi : Pt k 1 d, IsInvPair φ φi →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (g : PS k 1 d),
      DpolyOf (transF F φ φi) u P (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] (DpolyOf F (fun l => (dLin φ).mulVec (u l)) P g)
def GaugeTransSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B' : FB k d O)
    (φ φi : Pt k 1 d) (lam : PS k 2 d), IsInvPair φ φi →
    ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 → ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 →
    (∀ i, B'.G.F i = transF B.G.F φ φi i) →
    (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) →
    B'.ph1 = ev (n := 3) ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1),
        comp1 φ (pt k (n := 3) d 2)] B.ph1 *
      FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] lam +
        ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] lam -
        ev (n := 3) ![addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] lam) →
    B'.ph2 = ev (n := 3) ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1),
        comp1 φ (pt k (n := 3) d 2)] B.ph2 *
      FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] lam +
        ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] lam -
        ev (n := 3) ![pt k (n := 3) d 0, addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] lam) →
    B'.sy = ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] B.sy *
      FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] lam - lam) →
    (∀ a, B'.ad a = ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (B.ad a) *
      FB.expS k (ev (n := 2) ![comp1 (B'.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] lam -
        ev (n := 2) ![pt k (n := 2) d 0, comp1 (B'.A.act (star a)) (pt k (n := 2) d 1)] lam)) →
    ∀ h : PS k 2 d, B.IsCanonGauge k h →
      B'.IsCanonGauge k (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)
def NabTransSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B' : FB k d O)
    (φ φi : Pt k 1 d) (lam : PS k 2 d), IsInvPair φ φi →
    ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 → ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 →
    (∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (B.G.F i) = (X ((0 : Fin 1), i) : PS k 1 d)) →
    (∀ i, B'.G.F i = transF B.G.F φ φi i) →
    (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) →
    ∀ h : PS k 2 d, ev (n := 1) ![0, pt k (n := 1) d 0] h = 0 →
    ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k),
      B'.nabVal k (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0 m
          (ev (n := 1) ![φ] f * FB.expS k (-((m : k) •
            ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.actK k w0) (pt k (n := 1) d 0)] lam))) u P =
        B.nabVal k h w0 m f (fun l => (dLin φ).mulVec (u l)) P
def GaugeIndependenceColumns : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d),
    B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (w0 : O) (mm n : ℕ) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then
      dotProduct (u p.1) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u q.1))) +
        dotProduct (u q.1) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u p.1))) else 0) P = 0 →
    ∀ f : Fin n → PS k 1 d,
      ∑ mo ∈ P.support, P.coeff mo *
          ∏ b, B.nabVal k h w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        ∑ mo ∈ P.support, P.coeff mo *
          ∏ b, B.nabVal k h' w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1)
def HarmSecondSt : Prop :=
  ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop),
    (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) →
    ∀ (n : ℕ) (c : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → k),
    (∀ l l' : Σ τ : T, Fin (r τ), l'.1 ≠ cc l.1 → c l l' = 0) →
    ∀ P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k,
      (∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
          (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) P) = 0) →
      secondOrder k (fun p q : (Σ τ : T, Fin (r τ)) × Fin n => if p.2 = q.2 then c p.1 q.1 else 0) P = 0
end ReciprocityTheory.ChartRestriction.G.TB


