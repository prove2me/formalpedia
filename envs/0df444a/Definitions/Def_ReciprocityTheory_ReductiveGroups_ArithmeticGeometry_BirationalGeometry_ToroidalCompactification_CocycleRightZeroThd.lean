-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:49.18005+00:00
-- url     : https://prove2.me/theorems/4b4efa42-30a3-4f54-aa1e-43dce44bc195
-- title:
--   Cocycle Right Zero Thd
-- statement:
--   Definitions and structural lemmas for Cocycle Right Zero Thd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleRightZeroThd.lean

import Mathlib
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
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
abbrev PS (R : Type) [CommRing R] (n d : ℕ) : Type := MvPowerSeries (Fin n × Fin d) R
abbrev Pt (R : Type) [CommRing R] (n d : ℕ) : Type := Fin d → PS R n d
variable {R : Type} [CommRing R] {d : ℕ}
def pt (R : Type) [CommRing R] {n : ℕ} (d : ℕ) (j : Fin n) : Pt R n d := fun i => X (j, i)
def ev {m n : ℕ} (a : Fin m → Pt R n d) (f : PS R m d) : PS R n d :=
  MvPowerSeries.subst (fun p : Fin m × Fin d => a p.1 p.2) f
def comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) : Pt R n d := fun i => ev ![a] (φ i)
def addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) : Pt R n d := fun i => ev ![a, b] (F i)
def Dof (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) : PS R 1 d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (F j))) *
    pderiv R ((0 : Fin 1), j) f
def DmonOf (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f : PS R 1 d) : PS R 1 d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (Dof F (u l))^[m l] g) f
def DpolyOf (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R 1 d) : PS R 1 d :=
  ∑ m ∈ P.support, C (P.coeff m) * DmonOf F u m f
@[simp] lemma ev_one {m n : ℕ} (a : Fin m → Pt R n d) : ev a (1 : PS R m d) = 1 := by
  have H : ∃ p : MvPolynomial (Fin m × Fin d) R, (p : MvPowerSeries (Fin m × Fin d) R) = 1 :=
    ⟨1, MvPolynomial.coe_one⟩
  have hc : Classical.choose H = 1 := by
    have h := (Classical.choose_spec H).trans MvPolynomial.coe_one.symm
    first
    | exact MvPolynomial.coe_inj.mp h
    | exact MvPolynomial.coe_injective _ _ h
    | exact MvPolynomial.coe_injective _ h
  first
  | (simp [ev]; done)
  | (simp only [ev, MvPowerSeries.subst, MvPowerSeries.eval₂];
      rw [dif_pos H, hc];
      exact MvPolynomial.eval₂_one _ _)
  | (unfold ev MvPowerSeries.subst MvPowerSeries.eval₂;
      rw [dif_pos H, hc];
      exact MvPolynomial.eval₂_one _ _)
  | (simp only [ev, MvPowerSeries.subst, MvPowerSeries.eval₂, dif_pos H, hc, MvPolynomial.eval₂_one])
structure FGLaw (R : Type) [CommRing R] (d : ℕ) where
  F : Fin d → PS R 2 d
  const : ∀ i, constantCoeff (F i) = 0
  unit : ∀ i, ev (n := 1) ![0, pt R d 0] (F i) = (X ((0 : Fin 1), i) : PS R 1 d)
  comm : ∀ i, ev (n := 2) ![pt R d 1, pt R d 0] (F i) = F i
  assoc : ∀ i,
    ev (n := 3) ![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (F l), pt R d 2] (F i) =
      ev (n := 3) ![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (F l)] (F i)
namespace FGLaw
variable (G : FGLaw R d)
abbrev add {n : ℕ} (a b : Pt R n d) : Pt R n d := addOf G.F a b
def mapF {S : Type} [CommRing S] (φ : R →+* S) : Fin d → PS S 2 d :=
  fun i => MvPowerSeries.map φ (G.F i)
end FGLaw
structure OAct (O : Type) [CommRing O] (G : FGLaw R d) where
  act : O → Pt R 1 d
  const : ∀ a i, constantCoeff (act a i) = 0
  hom : ∀ a, comp1 (act a) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
    G.add (comp1 (act a) (pt R (n := 2) d 0)) (comp1 (act a) (pt R (n := 2) d 1))
  add_act : ∀ a b, act (a + b) = G.add (act a) (act b)
  mul_act : ∀ a b, act (a * b) = comp1 (act a) (act b)
  one_act : act 1 = pt R d 0
structure FB (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] where
  G : FGLaw R d
  A : OAct O G
  ph1 : PS R 3 d
  ph2 : PS R 3 d
  sy : PS R 2 d
  ad : O → PS R 2 d
  cocycleLeft_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph1 = 1
  cocycleRight_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph2 = 1
  cocycleRight_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph2 = 1
  cocycleRight_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph2 = 1
  symmetry_zero_fst : ev (n := 1) ![0, pt R d 0] sy = 1
  symmetry_zero_snd : ev (n := 1) ![pt R d 0, 0] sy = 1
  adjoint_zero_fst : ∀ a, ev (n := 1) ![0, pt R d 0] (ad a) = 1
  adjoint_zero_snd : ∀ a, ev (n := 1) ![pt R d 0, 0] (ad a) = 1

  cocycleLeft_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph1 =
      ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph1 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph1

  cocycleLeft_comm : ev (n := 3) ![pt R d 1, pt R d 0, pt R d 2] ph1 = ph1

  cocycleRight_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph2 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph2

  cocycleRight_comm : ev (n := 3) ![pt R d 0, pt R d 2, pt R d 1] ph2 = ph2

  interchange :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph1 * ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 * ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph1

  sy_inv : sy * ev (n := 2) ![pt R d 1, pt R d 0] sy = 1

  sy_law :
    ph2 * ev (n := 3) ![pt R d 0, pt R d 1] sy * ev (n := 3) ![pt R d 0, pt R d 2] sy =
      ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] sy * ev (n := 3) ![pt R d 1, pt R d 2, pt R d 0] ph1

  adjoint_compat_left : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), comp1 (A.act a) (pt R d 1), pt R d 2] ph1 *
        ev (n := 3) ![G.add (pt R d 0) (pt R d 1), pt R d 2] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 2] (ad a) * ev (n := 3) ![pt R d 1, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, pt R d 1, comp1 (A.act (star a)) (pt R d 2)] ph1

  adjoint_compat_right : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), pt R d 1, pt R d 2] ph2 *
        ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 1] (ad a) * ev (n := 3) ![pt R d 0, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1),
          comp1 (A.act (star a)) (pt R d 2)] ph2
  ad_one : ad 1 = 1

  ad_mul : ∀ a b : O, ad (a * b) =
    ev (n := 2) ![comp1 (A.act b) (pt R d 0), pt R d 1] (ad a) *
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] (ad b)

  ad_add : ∀ a b : O,
    ev (n := 2) ![comp1 (A.act a) (pt R d 0), comp1 (A.act b) (pt R d 0), pt R d 1] ph1 * ad (a + b) =
      ad a * ad b *
        ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1), comp1 (A.act (star b)) (pt R d 1)] ph2

  ad_sy : ∀ a : O,
    ad a * ev (n := 2) ![pt R d 1, pt R d 0] (ad (star a)) *
        ev (n := 2) ![comp1 (A.act a) (pt R d 0), pt R d 1] sy =
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] sy
namespace FB
variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
abbrev toK {n : ℕ} (f : PS R n d) : PS k n d := MvPowerSeries.map (algebraMap R k) f
def expS {n : ℕ} (f : PS k n d) : PS k n d := PowerSeries.subst f (PowerSeries.exp k)
def actK (a : O) : Pt k 1 d := fun i => MvPowerSeries.map (algebraMap R k) (B.A.act a i)
def FK : Fin d → PS k 2 d := B.G.mapF (algebraMap R k)
structure IsCanonGauge (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : toK k B.ph1 = expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : toK k B.ph2 = expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  sy : toK k B.sy = expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)
  ad : ∀ a : O, toK k (B.ad a) = expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)
def hL (h : PS k 2 d) (w0 : O) : PS k 1 d := ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] h
def nabVal (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial ι k) : k :=
  constantCoeff (DpolyOf (B.FK k) u P (f * expS k ((m : k) • B.hL k h w0)))
end FB
def FB.triv {O : Type} [CommRing O] [StarRing O] (G : FGLaw R d) (A : OAct O G) : FB R d O where
  G := G
  A := A
  ph1 := 1
  ph2 := 1
  sy := 1
  ad := fun _ => 1
  cocycleLeft_zero_fst := by simp
  cocycleLeft_zero_snd := by simp
  cocycleLeft_zero_thd := by simp
  cocycleRight_zero_fst := by simp
  cocycleRight_zero_snd := by simp
  cocycleRight_zero_thd := by simp
  symmetry_zero_fst := by simp
  symmetry_zero_snd := by simp
  adjoint_zero_fst := by simp
  adjoint_zero_snd := by simp
  cocycleLeft_assoc := by simp
  cocycleLeft_comm := by simp
  cocycleRight_assoc := by simp
  cocycleRight_comm := by simp
  interchange := by simp
  sy_inv := by simp
  sy_law := by simp
  adjoint_compat_left := by simp
  adjoint_compat_right := by simp
  ad_one := by simp
  ad_mul := by simp
  ad_add := by simp
  ad_sy := by simp
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ


