-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:13.004672+00:00
-- url     : https://prove2.me/theorems/93ab881c-6e41-4353-b61f-95237aff38e1
-- title:
--   Ker Eq Bot Of Coord
-- statement:
--   Definitions and structural lemmas for Ker Eq Bot Of Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/KerEqBotOfCoord.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
import Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_finiteCoord
import Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_infiniteCoord
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isCompatibleChart
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M OnePoint Filter Topology MeasureTheory
namespace ProjectiveLineResolution
abbrev Pt := (Σ k, PBlk 2 k) → ℂ
abbrev JJ : Ideal (MRing (PBlk 2)) := Ideal.span {Xc 2 0}
def vec (a b : ℂ) : Pt := fun q => ![a, b] q.2
@[simp] lemma vec0 (a b : ℂ) : vec a b ⟨(), 0⟩ = a := rfl
@[simp] lemma vec1 (a b : ℂ) : vec a b ⟨(), 1⟩ = b := rfl
lemma pt_ext {z z' : Pt} (h0 : z ⟨(), 0⟩ = z' ⟨(), 0⟩) (h1 : z ⟨(), 1⟩ = z' ⟨(), 1⟩) : z = z' := by
  funext ⟨k, i⟩
  cases k
  fin_cases i
  · exact h0
  · exact h1
open scoped Classical in

def lift (x y : OnePoint ℂ) : Pt := if x = ∞ then vec (crd1 y) 1 else vec 1 (crd0 y)
lemma lift_infty (y : OnePoint ℂ) : lift ∞ y = vec (crd1 y) 1 := if_pos rfl
lemma lift_coe (z : ℂ) (y : OnePoint ℂ) : lift (z : OnePoint ℂ) y = vec 1 (crd0 y) :=
  if_neg (coe_ne_infty z)
lemma mem_J_iff (z : Pt) : z ∈ mcPts JJ ↔ (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ z ⟨(), 0⟩ = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := h2 _ (Ideal.subset_span rfl)
    simpa [Xc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [Xc, h2]
lemma mem_bot (z : Pt) (h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) :=
  ⟨h, fun f hf => by rw [Ideal.mem_bot.mp hf]; simp⟩
lemma vec_ne (a b : ℂ) (h : a ≠ 0) : ∀ k, ∃ i, vec a b ⟨k, i⟩ ≠ 0 := fun _ => ⟨0, h⟩
lemma vec_ne' (a : ℂ) : ∀ k, ∃ i, vec a 1 ⟨k, i⟩ ≠ 0 := fun _ => ⟨1, one_ne_zero⟩
lemma lift_mem_bot (x y : OnePoint ℂ) : lift x y ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
  induction x with
  | infty => rw [lift_infty]; exact mem_bot _ (vec_ne' _)
  | coe z => rw [lift_coe]; exact mem_bot _ (vec_ne _ _ one_ne_zero)
lemma lift_mem_J (x : OnePoint ℂ) : lift x x ∈ mcPts JJ ↔ x = ∞ := by
  induction x with
  | infty =>
    refine iff_of_true ?_ rfl
    rw [lift_infty]
    exact (mem_J_iff _).2 ⟨vec_ne' _, by simp⟩
  | coe z =>
    refine iff_of_false (fun h => ?_) (coe_ne_infty z)
    rw [lift_coe] at h
    exact one_ne_zero ((mem_J_iff _).1 h).2
theorem holo (x : OnePoint ℂ) (p : Σ k, PBlk 2 k) :
    p1.HoloOn (fsPot.U x) (fun y => lift x y p) := by
  rcases p with ⟨⟨⟩, i⟩
  induction x with
  | infty =>
    rw [fsPot_U_infty]
    fin_cases i
    · have e : (fun y => lift ∞ y ⟨(), 0⟩) = crd1 := funext fun y => by rw [lift_infty]; rfl
      show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 0⟩)
      rw [e]; exact holomorphicOn_infiniteCoord
    · have e : (fun y => lift ∞ y ⟨(), 1⟩) = fun _ => 1 := funext fun y => by rw [lift_infty]; rfl
      show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 1⟩)
      rw [e]; exact holoOn_const _ 1
  | coe z =>
    rw [fsPot_U_coe]
    fin_cases i
    · have e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩) = fun _ => 1 :=
        funext fun y => by rw [lift_coe]; rfl
      show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩)
      rw [e]; exact holoOn_const _ 1
    · have e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩) = crd0 :=
        funext fun y => by rw [lift_coe]; rfl
      show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩)
      rw [e]; exact holomorphicOn_finiteCoord
lemma sameOrbit_refl (z : Pt) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩
theorem compat (x x' : OnePoint ℂ) (y : OnePoint ℂ) (hy : y ∈ fsPot.U x ∩ fsPot.U x') :
    SameOrbit (lift x y) (lift x' y) := by
  induction x with
  | infty =>
    induction x' with
    | infty => exact sameOrbit_refl _
    | coe z' =>
      rw [fsPot_U_infty, fsPot_U_coe] at hy
      obtain ⟨h0, ⟨ζ, rfl⟩⟩ := hy
      have hζ : ζ ≠ 0 := fun h => h0 (by rw [h])
      rw [lift_infty, lift_coe]
      refine ⟨fun _ => ζ⁻¹, fun _ => inv_ne_zero hζ, pt_ext ?_ ?_⟩
      · simp
      · simp [hζ]
  | coe z =>
    induction x' with
    | infty =>
      rw [fsPot_U_infty, fsPot_U_coe] at hy
      obtain ⟨⟨ζ, rfl⟩, h0⟩ := hy
      have hζ : ζ ≠ 0 := fun h => h0 (by rw [h])
      rw [lift_infty, lift_coe]
      refine ⟨fun _ => ζ, fun _ => hζ, pt_ext ?_ ?_⟩
      · simp [hζ]
      · simp
    | coe z' =>
      rw [lift_coe, lift_coe]
      exact sameOrbit_refl _
theorem surj (z : Pt) (hz : z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2)))) (hzJ : z ∉ mcPts JJ) :
    ∃ x, SameOrbit (lift x x) z := by
  have h0 : z ⟨(), 0⟩ ≠ 0 := fun h => hzJ ((mem_J_iff z).2 ⟨hz.1, h⟩)
  refine ⟨((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), fun _ => (z ⟨(), 0⟩)⁻¹,
    fun _ => inv_ne_zero h0, ?_⟩
  rw [lift_coe]
  refine pt_ext ?_ ?_
  · simp [h0]
  · simp [div_eq_inv_mul]
theorem inj (x x' : OnePoint ℂ) (hx : lift x x ∉ mcPts JJ)
    (h : SameOrbit (lift x x) (lift x' x')) : x = x' := by
  induction x with
  | infty => exact absurd ((lift_mem_J ∞).2 rfl) hx
  | coe ζ =>
    obtain ⟨c, hc, he⟩ := h
    induction x' with
    | infty =>
      have e0 := congrFun he ⟨(), 0⟩
      rw [lift_coe, lift_infty] at e0
      simp at e0
    | coe ζ' =>
      have e0 := congrFun he ⟨(), 0⟩
      have e1 := congrFun he ⟨(), 1⟩
      rw [lift_coe, lift_coe] at e0 e1
      simp only [vec0, vec1, finiteCoord_coe, mul_one] at e0 e1
      rw [e1, ← e0, one_mul]
lemma ker_eq_bot_of_coord {κ : Type*} [Fintype κ] {F : (Fin 1 → ℂ) → κ → ℂ} {y0 : Fin 1 → ℂ}
    (hF : DifferentiableAt ℂ F y0) (q : κ) (g : ℂ → ℂ) (d : ℂ) (hq : ∀ y, F y q = g (y 0))
    (hg : HasDerivAt g d (y0 0)) (hd : d ≠ 0) : (fderiv ℂ F y0).ker = ⊥ := by
  have h1 := (hasFDerivAt_apply (𝕜 := ℂ) q (F y0)).comp y0 hF.hasFDerivAt
  have e : (fun f : κ → ℂ => f q) ∘ F = g ∘ (fun y : Fin 1 → ℂ => y 0) := funext hq
  rw [e] at h1
  have h2 := hg.comp_hasFDerivAt y0 (hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 1) y0)
  have he := h1.unique h2
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  have hv' : fderiv ℂ F y0 v = 0 := hv
  have h3 := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ => L v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_apply, hv', Pi.zero_apply, smul_eq_mul] at h3
  have hv0 : v 0 = 0 := by
    rcases mul_eq_zero.1 h3.symm with h | h
    · exact absurd h hd
    · exact h
  funext i
  rw [Subsingleton.elim i 0]
  exact hv0
lemma diffAt (x : OnePoint ℂ) (p : (k : Unit) → PBlk 2 k) (hp : ∀ k, lift x x ⟨k, p k⟩ ≠ 0)
    (j : Fin p1.n) (hj : x ∈ (p1.chart j).source) :
    DifferentiableAt ℂ (fun y => affCoord p (lift x ((p1.chart j).symm y))) (p1.chart j x) := by
  have hy0 : p1.chart j x ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x := by
    refine ⟨(p1.chart j).map_source hj, ?_⟩
    show (p1.chart j).symm (p1.chart j x) ∈ fsPot.U x
    rw [(p1.chart j).left_inv hj]
    exact fsPot.mem_U x
  have hd : ∀ q, DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q) (p1.chart j x) :=
    fun q => (holo x q j _ hy0).differentiableAt
  refine differentiableAt_pi.2 fun q => ?_
  show DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q /
    lift x ((p1.chart j).symm y) ⟨q.1, p q.1⟩) _
  have hne : lift x ((p1.chart j).symm (p1.chart j x)) ⟨q.1, p q.1⟩ ≠ 0 := by
    rw [(p1.chart j).left_inv hj]
    exact hp q.1
  simp_rw [div_eq_mul_inv]
  exact (hd q).mul ((hd _).inv hne)
lemma p_cases (p : (k : Unit) → PBlk 2 k) : p () = 0 ∨ p () = 1 := by
  generalize p () = i
  fin_cases i
  · left; rfl
  · right; rfl
theorem immersion (x : OnePoint ℂ) (hx : lift x x ∉ mcPts JJ) (p : (k : Unit) → PBlk 2 k)
    (hp : ∀ k, lift x x ⟨k, p k⟩ ≠ 0) (j : Fin p1.n) (hj : x ∈ (p1.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (lift x ((p1.chart j).symm y))) (p1.chart j x)).ker = ⊥ := by
  have hD := diffAt x p hp j hj
  induction x with
  | infty => exact absurd ((lift_mem_J ∞).2 rfl) hx
  | coe ζ =>
    have hp0 := hp ()
    rw [lift_coe] at hp0
    fin_cases j
    · rcases p_cases p with h | h
      · refine ker_eq_bot_of_coord hD ⟨(), 1⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero
        simp [affCoord, lift_coe, h]
        rfl
      · rw [h] at hp0
        have hζ : ζ ≠ 0 := by simpa using hp0
        refine ker_eq_bot_of_coord hD ⟨(), 0⟩ (fun w => w⁻¹) _ (fun y => ?_)
          (hasDerivAt_inv hζ) (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hζ)))
        simp [affCoord, lift_coe, h]
        rfl
    · have hζ : ζ ≠ 0 := fun h0 => hj (by rw [h0])
      rcases p_cases p with h | h
      · refine ker_eq_bot_of_coord hD ⟨(), 1⟩ (fun w => w⁻¹) _ (fun y => ?_)
          (hasDerivAt_inv (inv_ne_zero hζ))
          (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hζ))))
        simp [affCoord, lift_coe, h]
        exact finiteCoord_projLineChart1_symm y
      · refine ker_eq_bot_of_coord hD ⟨(), 0⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero
        simp [affCoord, lift_coe, h]
        exact (congrArg (·⁻¹) (finiteCoord_projLineChart1_symm y)).trans (inv_inv _)
lemma eval_aeval (v : (Σ k, PBlk 2 k) → Polynomial ℂ) (F : MvPolynomial (Σ k, PBlk 2 k) ℂ)
    (w : ℂ) : (aeval v F).eval w = eval (fun q => (v q).eval w) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]
lemma eval_vec_poly (a b : Polynomial ℂ) (F : MvPolynomial (Σ k, PBlk 2 k) ℂ) (w : ℂ) :
    (aeval (fun q : Σ k, PBlk 2 k => ![a, b] q.2) F).eval w = eval (vec (a.eval w) (b.eval w)) F := by
  rw [eval_aeval, show (fun q : Σ k, PBlk 2 k => ((![a, b] q.2 : Polynomial ℂ)).eval w) =
    vec (a.eval w) (b.eval w) from pt_ext rfl rfl]
lemma factor (F : MvPolynomial (Σ k, PBlk 2 k) ℂ) (hF : ∀ w : ℂ, w ≠ 0 → eval (vec w 1) F ≠ 0) :
    ∃ (h : Polynomial ℂ) (m : ℕ), (∀ w, eval (vec w 1) F = w ^ m * h.eval w) ∧
      ∀ w, h.eval w ≠ 0 := by
  set G := aeval (fun q : Σ k, PBlk 2 k => ![(Polynomial.X : Polynomial ℂ), 1] q.2) F with hGdef
  have hG : ∀ w, G.eval w = eval (vec w 1) F := fun w => by
    rw [hGdef, eval_vec_poly]; simp
  have hne : G ≠ 0 := fun h0 => hF 1 one_ne_zero (by rw [← hG, h0, Polynomial.eval_zero])
  obtain ⟨h, hfac, hnd⟩ := G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hne 0
  have hev : ∀ w, eval (vec w 1) F = w ^ G.rootMultiplicity 0 * h.eval w := fun w => by
    rw [← hG]
    conv_lhs => rw [hfac]
    simp
  refine ⟨h, G.rootMultiplicity 0, hev, fun w h0 => ?_⟩
  by_cases hw : w = 0
  · subst hw
    exact hnd (Polynomial.dvd_iff_isRoot.2 h0)
  · exact hF w hw (by rw [hev, h0, mul_zero])
lemma holoOn_poly {U : Set (OnePoint ℂ)} {c : OnePoint ℂ → ℂ} (hc : p1.HoloOn U c)
    (P : Polynomial ℂ) : p1.HoloOn U (fun y => P.eval (c y)) :=
  fun j w hw => (P.differentiable.analyticAt _).comp (hc j w hw)
theorem snc (f : MRing (PBlk 2)) (hf : ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))),
      eval z (map (Int.castRingHom ℂ) f) = 0 → z ∈ mcPts JJ) :
    ∃ (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set (OnePoint ℂ)),
      IsSNC p1 (⟨fsPot.U, fsPot.isOpen_U, fsPot.mem_U, fun _ _ => 0⟩ : LocPot (OnePoint ℂ))
        (fun x y => eval (lift x y) (map (Int.castRingHom ℂ) f)) m W := by
  set F := map (Int.castRingHom ℂ) f with hFdef
  have nz : ∀ a b : ℂ, a ≠ 0 → eval (vec a b) F ≠ 0 := fun a b ha h0 =>
    ha ((mem_J_iff _).1 (hf _ (mem_bot _ (vec_ne a b ha)) h0)).2
  obtain ⟨h, m, hev, hh⟩ := factor F fun w hw => nz w 1 hw
  refine ⟨1, ![m], ![{∞}], ?_⟩
  intro x
  induction x with
  | infty =>
    refine ⟨projectiveLineChartAtInfinity, projLine_isCompatibleChart 1, OnePoint.infty_ne_coe 0, ?_, fun _ => Option.some 0, ?_, ?_,
      fun y => h.eval (crd1 y), holoOn_poly holomorphicOn_infiniteCoord h, fun y _ => hh _, ?_⟩
    · show projectiveLineChartAtInfinity.source ⊆ fsPot.U ∞
      rw [fsPot_U_infty]
    · intro k k' i _ _; exact Subsingleton.elim _ _
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1
        subst hy1
        exact ⟨hy2, 0, rfl, rfl⟩
      · rintro ⟨hy, i, _, hi⟩
        refine ⟨?_, hy⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff]
        induction y with
        | infty => rfl
        | coe ζ =>
          have hζ : ζ ≠ 0 := fun e => hy (by rw [e])
          exact absurd hi (by simp [projLineChart1_apply, hζ])
    · intro y _
      simp only [Fin.prod_univ_one, Matrix.cons_val_fin_one, projLineChart1_apply]
      rw [lift_infty, hev, mul_comm]
  | coe z =>
    refine ⟨projectiveLineChartAtZero, projLine_isCompatibleChart 0, ⟨z, rfl⟩, ?_, fun _ => none, ?_, ?_,
      fun y => eval (vec 1 (crd0 y)) F, ?_, fun y _ => nz 1 _ one_ne_zero, ?_⟩
    · show projectiveLineChartAtZero.source ⊆ fsPot.U (z : OnePoint ℂ)
      rw [fsPot_U_coe]
    · intro k k' i h; cases h
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1
        subst hy1
        exact absurd hy2 OnePoint.infty_notMem_range_coe
      · rintro ⟨_, i, h, _⟩
        cases h
    · have e : (fun y => eval (vec 1 (crd0 y)) F) =
          fun y => (aeval (fun q : Σ k, PBlk 2 k => ![(1 : Polynomial ℂ), Polynomial.X] q.2) F).eval (crd0 y) := by
        funext y; rw [eval_vec_poly]; simp
      rw [e]
      exact holoOn_poly holomorphicOn_finiteCoord _
    · intro y _
      simp only [Fin.prod_univ_one, mul_one]
      rw [lift_coe]
theorem null (j : Fin p1.n) : volume ((p1.chart j).target ∩
    (p1.chart j).symm ⁻¹' {x | lift x x ∈ mcPts JJ}) = 0 := by
  refine measure_mono_null ?_ (measure_singleton (0 : Fin 1 → ℂ))
  rintro y ⟨_, hy⟩
  have hy' : (p1.chart j).symm y = ∞ := (lift_mem_J _).1 hy
  fin_cases j
  · exact absurd hy' (OnePoint.coe_ne_infty _)
  · have h1 := infiniteCoord_projLineChart1_symm y
    rw [show projectiveLineChartAtInfinity.symm y = ∞ from hy', infiniteCoord_infty] at h1
    exact Set.mem_singleton_iff.2 (funext fun i => by rw [Subsingleton.elim i 0]; exact h1.symm)
theorem homog : IsMultiHomogIdeal JJ := by
  refine ⟨{Xc 2 0}, ?_, rfl⟩
  rintro f rfl
  refine ⟨fun _ => 1, fun m hm k => ?_⟩
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]
theorem nondeg : ¬ JJ ≤ ⊥ := fun h =>
  X_ne_zero _ (Ideal.mem_bot.mp (h (Ideal.subset_span (Set.mem_singleton _))))
def res : AnLogRes (⊥ : Ideal (MRing (PBlk 2))) JJ 1 where
  homog := homog
  nondeg := nondeg
  X := OnePoint ℂ
  A := p1
  U := fsPot.U
  isOpen_U := fsPot.isOpen_U
  mem_U := fsPot.mem_U
  lift := lift
  holo := holo
  mem x y _ := lift_mem_bot x y
  compat x x' y hy := compat x x' y hy
  surj := surj
  inj := inj
  immersion x hx p hp j hj := immersion x hx p hp j hj
  snc f _ _ _ hf := snc f hf
  null := null
end ProjectiveLineResolution
end ReciprocityTheory.ChartRestriction.G.Geo


