-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:33.180309+00:00
-- url     : https://prove2.me/theorems/f846b474-d681-4160-a7ee-bbaa1f1e268b
-- title:
--   Biext Change Second Factor
-- statement:
--   Definitions and structural lemmas for Biext Change Second Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextChangeSecondFactor.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
section Map
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
def mP {n : ℕ} (x : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map φ (x i)
def mV {m n : ℕ} (a : Fin m → Pt R n d) : Fin m → Pt k n d := fun j => mP φ (a j)
theorem mapInj (hφ : Function.Injective φ) {σ : Type} :
    Function.Injective (MvPowerSeries.map (σ := σ) φ) := by
  intro f g h
  ext n
  apply hφ
  rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]
theorem mPInj (hφ : Function.Injective φ) {n : ℕ} : Function.Injective (mP φ (n := n) (d := d)) := by
  intro x y h
  funext i
  exact mapInj φ hφ (congrFun h i)
theorem map_ev' {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) :
    MvPowerSeries.map φ (ev a f) = ev (mV φ a) (MvPowerSeries.map φ f) := by
  unfold ev
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2))]
  rfl
theorem mV_cons {m n : ℕ} (x : Pt R n d) (a : Fin m → Pt R n d) :
    mV φ (Matrix.vecCons x a) = Matrix.vecCons (mP φ x) (mV φ a) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [mV, Matrix.cons_val_zero]
  · simp only [mV, Matrix.cons_val_succ]
theorem mV_nil {n : ℕ} : mV φ (![] : Fin 0 → Pt R n d) = ![] := by
  funext j
  exact Fin.elim0 j
theorem mapPoint_pt {n : ℕ} (j : Fin n) : mP φ (pt R d j) = pt k d j := by
  funext i
  simp only [mP, pt, MvPowerSeries.map_X]
theorem mapPoint_zero {n : ℕ} : mP φ (0 : Pt R n d) = 0 := by
  funext i
  simp only [mP, Pi.zero_apply, map_zero]
theorem cc_pt' {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp only [pt, MvPowerSeries.constantCoeff_X]
theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext hc)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), smul_zero]
    simp [ha p.1 p.2, hp]
theorem cc_comp1' {n : ℕ} {ψ : Pt R 1 d} {x : Pt R n d} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 ψ x i) = 0 := by
  have hcz : CZ ![x] := by
    intro j i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simpa using hx i
  show constantCoeff (ev ![x] (ψ i)) = 0
  rw [cc_ev_lemma hcz, hψ]
theorem cc_addOf' {n : ℕ} {F : Fin d → PS R 2 d} {x y : Pt R n d} (hF : ∀ i, constantCoeff (F i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addOf F x y i) = 0 := by
  have hcz : CZ ![x, y] := by
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hx i
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simpa using hy i
  show constantCoeff (ev ![x, y] (F i)) = 0
  rw [cc_ev_lemma hcz, hF]
theorem cz_cons_iff {m n : ℕ} {p : Pt R n d} {a : Fin m → Pt R n d} :
    CZ (Matrix.vecCons p a) ↔ (∀ i, constantCoeff (p i) = 0) ∧ CZ a := by
  simp only [CZ, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
theorem cz_nil' {n : ℕ} : CZ (![] : Fin 0 → Pt R n d) ↔ True := by
  exact ⟨fun _ => trivial, fun _ j => Fin.elim0 j⟩
theorem mapPoint_comp1 {n : ℕ} (ψ : Pt R 1 d) {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    mP φ (comp1 ψ x) = comp1 (mP φ ψ) (mP φ x) := by
  funext i
  have hcz : CZ ![x] := cz_cons_iff.2 ⟨hx, cz_nil'.2 trivial⟩
  show MvPowerSeries.map φ (ev ![x] (ψ i)) = ev ![mP φ x] (MvPowerSeries.map φ (ψ i))
  rw [map_ev' φ hcz, mV_cons, mV_nil]
theorem mapPoint_addOf {n : ℕ} (F : Fin d → PS R 2 d) {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : mP φ (addOf F x y) = addOf (mP φ F) (mP φ x) (mP φ y) := by
  funext i
  have hcz : CZ ![x, y] := cz_cons_iff.2 ⟨hx, cz_cons_iff.2 ⟨hy, cz_nil'.2 trivial⟩⟩
  show MvPowerSeries.map φ (ev ![x, y] (F i)) = ev ![mP φ x, mP φ y] (MvPowerSeries.map φ (F i))
  rw [map_ev' φ hcz, mV_cons, mV_cons, mV_nil]
end Map
section Comparison₂
variable {R k O : Type} [CommRing R] [CommRing k] [CommRing O] [StarRing O] (φ : R →+* k) {d : ℕ}
structure IntTie (B : FB k d O) where
  FT : Pt R 2 d
  actT : O → Pt R 1 d
  ph1T : PS R 3 d
  ph2T : PS R 3 d
  syT : PS R 2 d
  adT : O → PS R 2 d
  hF : mP φ FT = B.G.F
  hA : ∀ a, mP φ (actT a) = B.A.act a
  h1 : MvPowerSeries.map φ ph1T = B.ph1
  h2 : MvPowerSeries.map φ ph2T = B.ph2
  hs : MvPowerSeries.map φ syT = B.sy
  had : ∀ a, MvPowerSeries.map φ (adT a) = B.ad a
variable {φ} {B : FB k d O} (t : IntTie φ B) (hφ : Function.Injective φ)
include hφ in
theorem IntTie.hFc (i : Fin d) : constantCoeff (t.FT i) = 0 := by
  have h1 : MvPowerSeries.map φ (t.FT i) = B.G.F i := congrFun t.hF i
  have h2 := congrArg (fun f => MvPowerSeries.constantCoeff f) h1
  simp only [MvPowerSeries.constantCoeff_map, B.G.const i] at h2
  exact hφ (h2.trans (map_zero φ).symm)
include hφ in
theorem IntTie.hAc (a : O) (i : Fin d) : constantCoeff (t.actT a i) = 0 := by
  have h1 : MvPowerSeries.map φ (t.actT a i) = B.A.act a i := congrFun (t.hA a) i
  have h2 := congrArg (fun f => MvPowerSeries.constantCoeff f) h1
  simp only [MvPowerSeries.constantCoeff_map, B.A.const a i] at h2
  exact hφ (h2.trans (map_zero φ).symm)
theorem IntTie.hFi (i : Fin d) : MvPowerSeries.map φ (t.FT i) = B.G.F i := by
  exact congrFun t.hF i
end Comparison₂
section Pull
variable {R k O : Type} [CommRing R] [CommRing k] [CommRing O] [StarRing O] {φ : R →+* k} {d : ℕ}
variable {B : FB k d O} (t : IntTie φ B) (hφ : Function.Injective φ)
def lawOf : FGLaw R d where
  F := t.FT
  const := t.hFc hφ
  unit i := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.unit i
  comm i := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.comm i
  assoc i := by
    show ev (n := 3) ![addOf t.FT (pt R d 0) (pt R d 1), pt R d 2] (t.FT i) =
      ev (n := 3) ![pt R d 0, addOf t.FT (pt R d 1) (pt R d 2)] (t.FT i)
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.assoc i
theorem lawOf_F : (lawOf t hφ).F = t.FT := rfl
def actOf : OAct O (lawOf t hφ) where
  act := t.actT
  const := t.hAc hφ
  hom a := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.hom a
  add_act a b := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.add_act a b
  mul_act a b := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.mul_act a b
  one_act := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.one_act
theorem actOf_act : (actOf t hφ).act = t.actT := rfl
def fbOf : FB R d O where
  G := lawOf t hφ
  A := actOf t hφ
  ph1 := t.ph1T
  ph2 := t.ph2T
  sy := t.syT
  ad := t.adT
  cocycleLeft_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_fst
  cocycleLeft_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_snd
  cocycleLeft_zero_thd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_thd
  cocycleRight_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_fst
  cocycleRight_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_snd
  cocycleRight_zero_thd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_thd
  symmetry_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.symmetry_zero_fst
  symmetry_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.symmetry_zero_snd
  adjoint_zero_fst a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_zero_fst a
  adjoint_zero_snd a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_zero_snd a
  cocycleLeft_assoc := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_assoc
  cocycleLeft_comm := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_comm
  cocycleRight_assoc := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_assoc
  cocycleRight_comm := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_comm
  interchange := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.interchange
  sy_inv := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.sy_inv
  sy_law := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.sy_law
  adjoint_compat_left a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_compat_left a
  adjoint_compat_right a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_compat_right a
  ad_sy a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_sy a
  ad_one := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_one
  ad_mul a b := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_mul a b
  ad_add a b := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_add a b
end Pull
section Gauge
variable {R k O : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing O] [StarRing O] {d : ℕ}
variable {B : FB k d O} (t : IntTie (algebraMap R k) B) (hφ : Function.Injective (algebraMap R k))
end Gauge
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA


