-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:04.724785+00:00
-- url     : https://prove2.me/theorems/4fa2cd31-0461-4254-9ae8-00129a46a0ff
-- title:
--   Formal Theta Sum Shift Period Div
-- statement:
--   Definitions and structural lemmas for Formal Theta Sum Shift Period Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
section Fourier
open MeasureTheory UnitAddTorus
local instance _p2m_local_instance_9149bae1c8_15 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_9149bae1c8_17 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem eq_zero_of_tsum_mFourier {d : Type} [Fintype d] {f : (d → ℤ) → ℂ} (hf : Summable f)
    (h : ∀ x : UnitAddTorus d, ∑' n, f n * mFourier n x = 0) : f = 0 := by
  classical
  have hs : Summable fun n => f n • mFourier n :=
    Summable.of_norm (by simpa only [norm_smul, mFourier_norm, mul_one] using hf.norm)
  have h0 : ∑' n, f n • mFourier n = 0 := by
    ext x
    have := ((ContinuousMap.evalCLM ℂ x).hasSum hs.hasSum).tsum_eq
    exact this.symm.trans (h x)
  have h1 : HasSum (fun n => f n • mFourier n) 0 := h0 ▸ hs.hasSum
  funext m
  have h2 := (innerSL ℂ (mFourierLp (d := d) 2 m)).hasSum
    ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus d)) ℂ).hasSum h1)
  simp only [map_smul, map_zero, innerSL_apply_apply, orthonormal_iff_ite.1 orthonormal_mFourier,
    smul_eq_mul] at h2
  have h3 : HasSum (fun n => f n * if m = n then (1 : ℂ) else 0) (f m) := by
    convert hasSum_ite_eq m (f m) using 2 with n
    by_cases hn : n = m
    · simp [hn]
    · simp [hn, Ne.symm hn]
  exact h3.unique h2
end Fourier
namespace AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
theorem e_def (x : ℂ) : eTwoPi x = Complex.exp (2 * Real.pi * Complex.I * x) := rfl
def lin (la : A.La) : A.V →ₗ[ℂ] ℂ where
  toFun v := Real.pi * A.H v.2 la.l - 2 * Real.pi * Complex.I * v.1 la.y
  map_add' v v' := by simp only [Prod.snd_add, Prod.fst_add, H_add_left, AddMonoidHom.add_apply]; ring
  map_smul' c v := by
    simp only [Prod.smul_snd, Prod.smul_fst, H_smul_left, AddMonoidHom.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem lin_apply (la : A.La) (v : A.V) :
    A.lin la v = Real.pi * A.H v.2 la.l - 2 * Real.pi * Complex.I * v.1 la.y := rfl
@[simp] theorem lin_zero : A.lin 0 = 0 := LinearMap.ext fun v => by simp [lin_apply]
def logConst (w : ℂ) (la : A.La) : ℂ :=
  Complex.log (A.chi la.l) - Complex.log (A.psi la.y) + Real.pi * A.H (A.ct la.y) la.l +
    Real.pi / 2 * A.H la.l la.l - 2 * Real.pi * Complex.I * (w * A.q la.y)
def L (w : ℂ) (la : A.La) (v : A.V) : ℂ := A.lin la v + A.logConst w la
@[simp] theorem perFactor_zero (w : ℂ) (v : A.V) : A.perFactor w 0 v = 1 := by simp [perFactor, ah]
section Shift
variable (k : ℕ) [NeZero k]
def shift (k : ℕ) [NeZero k] (la : A.La) (α : A.X) : ((Fin A.gB → ℂ) → ℂ) →ₗ[ℂ] ((Fin A.gB → ℂ) → ℂ) where
  toFun th z := eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
    th (z + (k : ℂ)⁻¹ • (A.P0 la).2)
  map_add' th th' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' c th := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
theorem shift_apply (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.shift k la α th z = eTwoPi ((A.T la.y α + la.n α - A.H (A.ct α) la.l / (2 * Complex.I)) / k) *
      Complex.exp (-(Real.pi * A.H z la.l)) * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l)) := rfl
@[simp] theorem shift_zero (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) : A.shift k 0 α th = th := by
  funext z; simp [shift_apply]
end Shift
theorem eq_zero_of_tsum_char {f : A.X → ℂ} (hf : Summable f)
    (h : ∀ l : A.X →+ ℂ, (∀ x, (l x).im = 0) → ∑' χ, f χ * eTwoPi (l χ) = 0) : f = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let E := b.equivFun.toEquiv
  have key : f ∘ E.symm = 0 := by
    refine eq_zero_of_tsum_mFourier (E.symm.summable_iff.2 hf) fun x => ?_
    choose t ht using fun i => QuotientAddGroup.mk_surjective (x i)
    have hl : ∀ χ, A.coord.symm (fun i => (t i : ℂ)) χ = ∑ i, (E χ i : ℂ) * t i := fun χ => by
      change b.constr ℤ (fun i => (t i : ℂ)) χ = _
      rw [Module.Basis.constr_apply_fintype]
      simp [E]
    have := h (A.coord.symm fun i => (t i : ℂ)) fun x => by simp [hl]
    rw [← E.symm.tsum_eq] at this
    refine Eq.trans (tsum_congr fun n => ?_) this
    rw [hl, Equiv.apply_symm_apply, eTwoPi, Finset.mul_sum, Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ht i, fourier_coe_apply]
    congr 1
    push_cast; ring
  funext χ
  simpa using congrFun key (E χ)
theorem sum_coeff_eq_zero [DecidableEq A.X] {j : ℕ} (hj : j ≠ 0) {ι : Type*} (s : Finset ι) (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') {a : ι → A.X → ℂ} (ha : ∀ p ∈ s, Summable (a p))
    (h : ∀ l : A.X →+ ℂ, (∀ x, (l x).im = 0) → ∑ p ∈ s, ∑' μ, a p μ * eTwoPi (l (wt p + j • μ)) = 0)
    (p₀ : ι) (μ₀ : A.X) : ∑ p ∈ s with wt p = wt p₀, a p μ₀ = 0 := by
  have : IsAddTorsionFree A.X := .of_isTorsionFree ℤ _
  have hinj : ∀ p, Function.Injective fun μ : A.X => wt p + j • μ := fun p μ ν hμ =>
    nsmul_right_injective hj (add_left_cancel hμ)
  let g : ι → A.X → ℂ := fun p => Function.extend (fun μ : A.X => wt p + j • μ) (a p) 0
  have hg : ∀ p μ, g p (wt p + j • μ) = a p μ := fun p μ => (hinj p).extend_apply _ _ μ
  have hg0 : ∀ p χ, χ ∉ Set.range (fun μ : A.X => wt p + j • μ) → g p χ = 0 := fun p χ hχ =>
    Function.extend_apply' _ _ _ hχ
  have hgs : ∀ p ∈ s, Summable (g p) := fun p hp =>
    ((hinj p).summable_iff (hg0 p)).1 ((ha p hp).congr fun μ => (hg p μ).symm)
  have key := A.eq_zero_of_tsum_char (f := fun χ => ∑ p ∈ s, g p χ) (summable_sum hgs) fun l hl => by
    have hn : ∀ χ, ‖eTwoPi (l χ)‖ = 1 := fun χ => by
      rw [e_def, Complex.norm_exp]; simp [hl χ]
    simp only [Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun p hp =>
      Summable.of_norm (by simpa only [norm_mul, hn, mul_one] using (hgs p hp).norm), ← h l hl]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (hinj p).tsum_eq (f := fun χ => g p χ * eTwoPi (l χ))]
    · simp only [hg]
    · intro χ hχ
      by_contra hc
      exact hχ (by simp [hg0 p χ hc])
  have h1 := congrFun key (wt p₀ + j • μ₀)
  rw [Finset.sum_filter]
  refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_) h1
  split_ifs with hp
  · rw [← hp, hg]
  · refine (hg0 p _ ?_).symm
    rintro ⟨μ, hμ⟩
    refine hp (hwt p p₀ (μ₀ - μ) ?_)
    rw [smul_sub, ← add_sub_assoc, ← hμ]
    simp
theorem term_eq_mul_char (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (l : A.X →+ ℂ) (z : Fin A.gB → ℂ) :
    A.term j α th μ (l, z) = A.term j α th μ (0, z) * eTwoPi (l (α + j • μ)) := by
  simp only [term, AddMonoidHom.zero_apply, e_zero]; ring
@[simp] theorem term_zero_zero (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.term j α th 0 (0, z) = th z := by simp [term]
@[simp] theorem exponent_zero (j : ℕ) (α : A.X) : A.exponent j α 0 = 0 := by simp [exponent]
theorem eq_zero_of_sum_filter {X W ι : Type*} [DecidableEq X] {s : Finset ι} {wt : ι → X} {th : ι → W → ℂ}
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) {r : ι → ℂ}
    (h : ∀ p₀ z, ∑ p ∈ s with wt p = wt p₀, r p * th p z = 0) : ∀ p ∈ s, r p = 0 := fun p₀ hp₀ =>
  linearIndepOn_iff'.1 (hth (wt p₀)) (s.filter fun p => wt p = wt p₀) r
    (fun p hp => (Finset.mem_filter.1 hp).2) (funext fun z => by simpa [Finset.sum_apply] using h p₀ z) p₀
    (Finset.mem_filter.2 ⟨hp₀, rfl⟩)
theorem hasSum_coeff_mul_FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V)
    (r : LaurentSeries ℂ) (n : ℤ) :
    HasSum (fun μ => r.coeff (n - A.exponent j α μ) * A.term j α th μ v) ((r * A.FSum j α th v).coeff n) := by
  classical
  have hP : (Set.Ici (-A.be α α)).IsPWO := (BddBelow.isWF bddBelow_Ici).isPWO
  rw [HahnSeries.coeff_mul_right' hP fun m hm => by
    by_contra hc
    exact hm (A.coeff_FSum_eq_zero j α th v (not_le.1 hc))]
  have h1 : ∀ p : ℤ × ℤ, HasSum (fun μ => if A.exponent j α μ = p.2 then r.coeff p.1 * A.term j α th μ v else 0)
      (r.coeff p.1 * (A.FSum j α th v).coeff p.2) := fun p => by
    rw [coeff_FSum, Finset.mul_sum]
    convert hasSum_sum_of_ne_finset_zero (s := A.level j α p.2) (L := SummationFilter.unconditional _)
      (f := fun μ => if A.exponent j α μ = p.2 then r.coeff p.1 * A.term j α th μ v else 0)
      fun μ hμ => if_neg (by simpa using hμ) using 1
    exact Finset.sum_congr rfl fun μ hμ => (if_pos (by simpa using hμ)).symm
  convert hasSum_sum fun p _ => h1 p using 2 with μ
  rw [Finset.sum_eq_single (n - A.exponent j α μ, A.exponent j α μ)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    refine if_neg fun hb => hne ?_
    have := (Finset.mem_antidiagonal.1 hab).2.2
    simp only at hb this
    ext <;> simp only <;> omega
  · intro hn
    rw [if_pos rfl]
    by_contra hc
    exact hn (Finset.mem_antidiagonal.2 ⟨left_ne_zero_of_mul hc, A.neg_be_le_exponent (NeZero.ne j) α μ, by simp⟩)
theorem linearIndependent_FSum (j : ℕ) [NeZero j] {ι : Type*} (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') (th : ι → (Fin A.gB → ℂ) → ℂ)
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) :
    LinearIndependent (LaurentSeries ℂ) fun p => A.FSum j (wt p) (th p) := by
  classical
  refine linearIndependent_iff'.2 fun s r hr p hp => ?_
  ext n
  refine eq_zero_of_sum_filter (r := fun p => (r p).coeff n) hth (fun p₀ z => ?_) p hp
  have := A.sum_coeff_eq_zero (NeZero.ne j) s wt hwt
    (a := fun p μ => (r p).coeff (n - A.exponent j (wt p) μ) * A.term j (wt p) (th p) μ (0, z))
    (fun p _ => (A.hasSum_coeff_mul_FSum j _ _ _ _ _).summable) (fun l _ => ?_) p₀ 0
  · simpa using this
  · refine Eq.trans ?_ (congrArg (fun S : LaurentSeries ℂ => S.coeff n) (congrFun hr (l, z)))
    rw [Finset.sum_apply, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← (A.hasSum_coeff_mul_FSum j _ _ _ _ _).tsum_eq]
    exact tsum_congr fun μ => by rw [A.term_eq_mul_char j _ _ μ l z]; ring
theorem linearIndepOn_sigma {X W C : Type*} {I : C → Type*} {rep : C → X} (hrep : Function.Injective rep)
    {th : ∀ c, I c → W → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) (α : X) :
    LinearIndepOn ℂ (fun p : Σ c, I c => th p.1 p.2) {p | rep p.1 = α} := by
  by_cases h : ∃ c, rep c = α
  · obtain ⟨c, rfl⟩ := h
    have : {p : Σ c, I c | rep p.1 = rep c} = Set.range (Sigma.mk c) := by
      ext ⟨c', i⟩
      simp only [Set.mem_setOf_eq, hrep.eq_iff, Set.mem_range]
      exact ⟨by rintro rfl; exact ⟨i, rfl⟩, by rintro ⟨i', hi⟩; exact (congrArg Sigma.fst hi).symm⟩
    rw [this]
    exact (linearIndepOn_range_iff sigma_mk_injective _).2 (hth c)
  · have : {p : Σ c, I c | rep p.1 = α} = ∅ := Set.eq_empty_of_forall_notMem fun p hp => h ⟨p.1, hp⟩
    rw [this]
    exact linearIndepOn_empty _ _
section Classes
variable {C : Type*} {I : C → Type*} {j : ℕ} {rep : C → A.X}
theorem linearIndependent_FSum_sigma [NeZero j] (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) :
    LinearIndependent (LaurentSeries ℂ) fun p : Σ c, I c => A.FSum j (rep p.1) (th p.1 p.2) :=
  A.linearIndependent_FSum j (fun p : Σ c, I c => rep p.1) (fun _ _ μ h => congrArg rep (hrep _ _ μ h)) _
    (linearIndepOn_sigma (fun c c' h => hrep c c' 0 (by simpa using h)) hth)
variable [Fintype C] [∀ c, Fintype (I c)]
end Classes
example (τ₀ : ℂ) : LinearIndependent (LaurentSeries ℂ)
    fun p : Σ _ : Fin 2, Unit => (tate τ₀).FSum 2 ((p.1 : ℕ) : ℤ) 1 :=
  (tate τ₀).linearIndependent_FSum_sigma (I := fun _ : Fin 2 => Unit) (rep := fun c => ((c : ℕ) : ℤ))
    (th := fun _ _ => 1)
    (fun c c' (μ : ℤ) h => by
      have h' : ((c : ℕ) : ℤ) = ((c' : ℕ) : ℤ) + (2 : ℕ) • μ := h
      rw [nsmul_eq_mul] at h'
      omega)
    fun _ => linearIndependent_unique_iff.2 one_ne_zero
end AnArc
end GlobalTheory


