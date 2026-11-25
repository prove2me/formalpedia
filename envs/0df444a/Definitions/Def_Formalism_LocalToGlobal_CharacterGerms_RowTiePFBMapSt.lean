-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePFBMapSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePFBMapSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:47.63142+00:00
-- url     : https://prove2.me/theorems/a7da151a-44b7-40ca-a15e-431fde6a0c1f
-- title:
--   Row Tie PFBMap St
-- statement:
--   Definitions and structural lemmas for Row Tie PFBMap St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePFBMapSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

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
namespace Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
def mpt {n : ℕ} (a : Pt R n d) : Pt S n d := fun i => MvPowerSeries.map φ (a i)
theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]
theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j => mpt φ (a j)) (MvPowerSeries.map φ f) := by
  unfold ev
  exact MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)) f
theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS R 1 d) :
    MvPowerSeries.map φ (ev ![a] f) = ev ![mpt φ a] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a] (by intro j i; fin_cases j; simp [ha]) f]
  congr 1
  funext j
  fin_cases j
  rfl
theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mpt φ a, mpt φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem map_ev3 {n : ℕ} (a b c : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) (f : PS R 3 d) :
    MvPowerSeries.map φ (ev ![a, b, c] f) = ev ![mpt φ a, mpt φ b, mpt φ c] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b, c] (by intro j i; fin_cases j <;> simp [ha, hb, hc]) f]
  congr 1
  funext j
  fin_cases j <;> rfl
omit [CommRing S] in
theorem cc_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact (cc_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf
omit [CommRing S] in
@[simp] theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]
omit [CommRing S] in
@[simp] theorem cc_addOf {n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := cc_ev ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) (F i) (hF i)
omit [CommRing S] in
@[simp] theorem cc_comp1 {n : ℕ} (ψ : Pt R 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 ψ a i) = 0 := cc_ev ![a] (by intro j i; fin_cases j; simp [ha]) (ψ i) (hψ i)
omit [CommRing S] in
theorem zc_zero {n : ℕ} : ∀ i : Fin d, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp
@[simp] theorem mpt_pt {n : ℕ} (j : Fin n) : mpt φ (pt R d j) = pt S d j := by
  funext i
  simp [mpt, pt]
@[simp] theorem mpt_zero {n : ℕ} : mpt φ (0 : Pt R n d) = 0 := by
  funext i
  simp [mpt]
theorem mpt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    mpt φ (addOf F a b) = addOf (fun i => MvPowerSeries.map φ (F i)) (mpt φ a) (mpt φ b) := by
  funext i
  exact map_ev2 φ a b ha hb (F i)
theorem mpt_comp1 {n : ℕ} (ψ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mpt φ (comp1 ψ a) = comp1 (mpt φ ψ) (mpt φ a) := by
  funext i
  exact map_ev1 φ a ha (ψ i)
def mapLaw (G : FGLaw R d) : FGLaw S d where
  F := fun i => MvPowerSeries.map φ (G.F i)
  const := by intro i; simp [constantCoeff_map, G.const]
  unit := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.unit i)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_X, mpt_zero, mpt_pt] at h
    exact h
  comm := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.comm i)
    simpa [map_ev2] using h
  assoc := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.assoc i)
    change MvPowerSeries.map φ (ev ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i)) =
      MvPowerSeries.map φ (ev ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i)) at h
    change ev ![addOf (fun l => MvPowerSeries.map φ (G.F l)) (pt S d 0) (pt S d 1), pt S d 2]
        (MvPowerSeries.map φ (G.F i)) =
      ev ![pt S d 0, addOf (fun l => MvPowerSeries.map φ (G.F l)) (pt S d 1) (pt S d 2)]
        (MvPowerSeries.map φ (G.F i))
    simpa [map_ev2, mpt_addOf, G.const] using h
def mapAct {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapLaw φ G) where
  act := fun a => mpt φ (A.act a)
  const := by intro a i; simp [mpt, constantCoeff_map, A.const]
  hom := by
    intro a
    have h := congrArg (mpt φ) (A.hom a)
    simpa [FGLaw.add, mapLaw, mpt_comp1, mpt_addOf, G.const, A.const] using h
  add_act := by
    intro a b
    have h := congrArg (mpt φ) (A.add_act a b)
    simpa [FGLaw.add, mapLaw, mpt_addOf, A.const] using h
  mul_act := by
    intro a b
    have h := congrArg (mpt φ) (A.mul_act a b)
    simpa [mpt_comp1, A.const] using h
  one_act := by
    have h := congrArg (mpt φ) A.one_act
    simpa using h
def mapFB {O : Type} [CommRing O] [StarRing O] (B : FB R d O) : FB S d O where
  G := mapLaw φ B.G
  A := mapAct φ B.A
  ph1 := MvPowerSeries.map φ B.ph1
  ph2 := MvPowerSeries.map φ B.ph2
  sy := MvPowerSeries.map φ B.sy
  ad := fun a => MvPowerSeries.map φ (B.ad a)
  cocycleLeft_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_fst
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_snd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_zero_thd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_thd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_fst
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_snd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_thd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_thd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  symmetry_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.symmetry_zero_fst
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  symmetry_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.symmetry_zero_snd
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_assoc := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleLeft_assoc
  cocycleLeft_comm := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleLeft_comm
  cocycleRight_assoc := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleRight_assoc
  cocycleRight_comm := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleRight_comm
  interchange := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.interchange
  sy_inv := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.sy_inv
  sy_law := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.sy_law
  ad_one := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.ad_one
  adjoint_zero_fst := fun a => by
    have h := congrArg (MvPowerSeries.map φ) (B.adjoint_zero_fst a)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  adjoint_zero_snd := fun a => by
    have h := congrArg (MvPowerSeries.map φ) (B.adjoint_zero_snd a)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  adjoint_compat_left := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.adjoint_compat_left a)
  adjoint_compat_right := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.adjoint_compat_right a)
  ad_sy := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_sy a)
  ad_mul := fun a b => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_mul a b)
  ad_add := fun a b => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_add a b)
end Formalism.L2.FormalSeriesBounds.MapFB
namespace Formalism.L2.FormalSeriesBounds
end Formalism.L2.FormalSeriesBounds


