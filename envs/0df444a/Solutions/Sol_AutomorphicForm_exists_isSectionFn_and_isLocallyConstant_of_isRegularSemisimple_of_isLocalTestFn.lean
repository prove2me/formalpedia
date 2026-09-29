-- Prove2me | solution 1 for AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/335417e8-ccd5-55ad-a58b-d7b0c18b1781

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace OrbitalCutoffAux
namespace Cyclic

variable {F : Type*} [Field F]

private def _root_.OrbitalCutoffAux.Cyclic.comp (t d : F) : Matrix (Fin 2) (Fin 2) F := !![0, -d; 1, t]

p2m_export "OrbitalCutoffAux.Cyclic" "comp"
private theorem det_comp (t d : F) : (comp t d).det = d := by
  simp [comp]

private def cycMat (a : Matrix (Fin 2) (Fin 2) F) (e0 e1 : F) : Matrix (Fin 2) (Fin 2) F :=
  !![e0, a 0 0 * e0 + a 0 1 * e1; e1, a 1 0 * e0 + a 1 1 * e1]

private theorem mul_cycMat (a : Matrix (Fin 2) (Fin 2) F) (e0 e1 : F) :
    a * cycMat a e0 e1 = cycMat a e0 e1 * comp a.trace a.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, comp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

private theorem det_cycMat_e1 (a : Matrix (Fin 2) (Fin 2) F) : (cycMat a 1 0).det = a 1 0 := by
  simp [cycMat]

private theorem det_cycMat_e2 (a : Matrix (Fin 2) (Fin 2) F) : (cycMat a 0 1).det = -a 0 1 := by
  simp [cycMat]

private theorem det_cycMat_e12 (a : Matrix (Fin 2) (Fin 2) F) :
    (cycMat a 1 1).det = a 1 0 + a 1 1 - (a 0 0 + a 0 1) := by
  simp [cycMat]

private theorem det_cycMat_ne_zero_or (a : Matrix (Fin 2) (Fin 2) F) (ha : a.trace ^ 2 - 4 * a.det ≠ 0) :
    (cycMat a 1 0).det ≠ 0 ∨ (cycMat a 0 1).det ≠ 0 ∨ (cycMat a 1 1).det ≠ 0 := by
  rcases eq_or_ne (a 1 0) 0 with h10 | h10
  · rcases eq_or_ne (a 0 1) 0 with h01 | h01
    · right; right
      rw [det_cycMat_e12, h10, h01]
      intro h
      apply ha
      have h' : a 1 1 = a 0 0 := by linear_combination h
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, h10, h01, h']
      ring
    · right; left
      rw [det_cycMat_e2]
      exact neg_ne_zero.2 h01
  · left
    rw [det_cycMat_e1]
    exact h10

private theorem exists_det_cycMat_ne_zero (a : Matrix (Fin 2) (Fin 2) F) (ha : a.trace ^ 2 - 4 * a.det ≠ 0) :
    ∃ e0 e1 : F, (cycMat a e0 e1).det ≠ 0 := by
  rcases det_cycMat_ne_zero_or a ha with h | h | h
  · exact ⟨1, 0, h⟩
  · exact ⟨0, 1, h⟩
  · exact ⟨1, 1, h⟩

private theorem exists_shape_of_mul_comp_eq (t d : F) (x : Matrix (Fin 2) (Fin 2) F)
    (hx : x * comp t d = comp t d * x) :
    ∃ α β : F, x = !![α, -(d * β); β, α + t * β] := by
  refine ⟨x 0 0, x 1 0, ?_⟩
  have h00 := congrFun (congrFun hx 0) 0
  have h10 := congrFun (congrFun hx 1) 0
  simp [comp, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination h00
  · simp
  · simp
    linear_combination h10

private theorem shape_mul_comm (t d α β α' β' : F) :
    !![α, -(d * β); β, α + t * β] * !![α', -(d * β'); β', α' + t * β'] =
      !![α', -(d * β'); β', α' + t * β'] * !![α, -(d * β); β, α + t * β] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem mul_comm_of_mul_comp_eq (t d : F) (x y : Matrix (Fin 2) (Fin 2) F)
    (hx : x * comp t d = comp t d * x) (hy : y * comp t d = comp t d * y) : x * y = y * x := by
  obtain ⟨α, β, rfl⟩ := exists_shape_of_mul_comp_eq t d x hx
  obtain ⟨α', β', rfl⟩ := exists_shape_of_mul_comp_eq t d y hy
  exact shape_mul_comm t d α β α' β'

private theorem isUnit_comp_of_isUnit (t d : F) (hd : IsUnit d) : IsUnit (comp t d) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_comp]
  exact hd

private noncomputable def compUnit (g : GL (Fin 2) F) : GL (Fin 2) F :=
  (isUnit_comp_of_isUnit (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g))).unit

private theorem coe_compUnit (g : GL (Fin 2) F) :
    (compUnit g : Matrix (Fin 2) (Fin 2) F) =
      comp (g : Matrix (Fin 2) (Fin 2) F).trace (g : Matrix (Fin 2) (Fin 2) F).det :=
  IsUnit.unit_spec _

private noncomputable def cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    GL (Fin 2) F :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)).unit

private theorem coe_cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    (cycUnit g e0 e1 h : Matrix (Fin 2) (Fin 2) F) = cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1 :=
  IsUnit.unit_spec _

private theorem mul_cycUnit
    (g : GL (Fin 2) F) (e0 e1 : F) (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    g * cycUnit g e0 e1 h = cycUnit g e0 e1 h * compUnit g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_cycUnit, coe_compUnit]
  exact mul_cycMat _ e0 e1

private theorem eq_cycUnit_mul_compUnit (g : GL (Fin 2) F) (e0 e1 : F)
    (h : (cycMat (g : Matrix (Fin 2) (Fin 2) F) e0 e1).det ≠ 0) :
    g = cycUnit g e0 e1 h * compUnit g * (cycUnit g e0 e1 h)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact mul_cycUnit g e0 e1 h

private theorem disc_ne_zero_of_isRegularSemisimple (g : GL (Fin 2) F) (hg : AutomorphicForm.IsRegularSemisimple g) :
    (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  (AutomorphicForm.isRegularSemisimple_iff_ne_zero g).1 hg

private theorem exists_conj_comp (g : GL (Fin 2) F) (hg : AutomorphicForm.IsRegularSemisimple g) :
    ∃ p : GL (Fin 2) F, g = p * compUnit g * p⁻¹ := by
  obtain ⟨e0, e1, h⟩ := exists_det_cycMat_ne_zero _ (disc_ne_zero_of_isRegularSemisimple g hg)
  exact ⟨cycUnit g e0 e1 h, eq_cycUnit_mul_compUnit g e0 e1 h⟩

private theorem trace_conj (g x : GL (Fin 2) F) :
    ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mul]

private theorem det_conj (g x : GL (Fin 2) F) :
    ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

private theorem compUnit_conj (g x : GL (Fin 2) F) : compUnit (x⁻¹ * g * x) = compUnit g := by
  apply Units.ext
  rw [coe_compUnit, coe_compUnit, trace_conj, det_conj]

private theorem exists_conj_of_trace_det (g h : GL (Fin 2) F) (hg : AutomorphicForm.IsRegularSemisimple g)
    (htr : (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace)
    (hdet : (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det) :
    ∃ y : GL (Fin 2) F, y * g * y⁻¹ = h := by
  have hh : AutomorphicForm.IsRegularSemisimple h := by
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, htr, hdet]
    exact disc_ne_zero_of_isRegularSemisimple g hg
  have hc : compUnit h = compUnit g := by
    apply Units.ext
    rw [coe_compUnit, coe_compUnit, htr, hdet]
  obtain ⟨p, hp⟩ := exists_conj_comp g hg
  obtain ⟨q, hq⟩ := exists_conj_comp h hh
  refine ⟨q * p⁻¹, ?_⟩
  rw [hq, hc]
  conv_lhs => rw [hp]
  group

private theorem mul_comm_of_conj (p c : GL (Fin 2) F) (t d : F) (hc : (c : Matrix (Fin 2) (Fin 2) F) = comp t d)
    (x y : GL (Fin 2) F) (hx : x * (p * c * p⁻¹) = p * c * p⁻¹ * x) (hy : y * (p * c * p⁻¹) = p * c * p⁻¹ * y) :
    x * y = y * x := by
  have hx' : (p⁻¹ * x * p) * c = c * (p⁻¹ * x * p) := by
    calc (p⁻¹ * x * p) * c = p⁻¹ * (x * (p * c * p⁻¹)) * p := by group
      _ = p⁻¹ * (p * c * p⁻¹ * x) * p := by rw [hx]
      _ = c * (p⁻¹ * x * p) := by group
  have hy' : (p⁻¹ * y * p) * c = c * (p⁻¹ * y * p) := by
    calc (p⁻¹ * y * p) * c = p⁻¹ * (y * (p * c * p⁻¹)) * p := by group
      _ = p⁻¹ * (p * c * p⁻¹ * y) * p := by rw [hy]
      _ = c * (p⁻¹ * y * p) := by group
  have hxm : ((p⁻¹ * x * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * comp t d =
      comp t d * ((p⁻¹ * x * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hc, ← Units.val_mul, ← Units.val_mul, hx']
  have hym : ((p⁻¹ * y * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * comp t d =
      comp t d * ((p⁻¹ * y * p : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hc, ← Units.val_mul, ← Units.val_mul, hy']
  have hm := mul_comm_of_mul_comp_eq t d _ _ hxm hym
  have hu : (p⁻¹ * x * p) * (p⁻¹ * y * p) = (p⁻¹ * y * p) * (p⁻¹ * x * p) :=
    Units.ext (by simpa only [Units.val_mul] using hm)
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hu]
    _ = y * x := by group

private theorem centralizer_comm (g : GL (Fin 2) F) (hg : AutomorphicForm.IsRegularSemisimple g) :
    ∀ a ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)),
      ∀ b ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)), a * b = b * a := by
  obtain ⟨p, hp⟩ := exists_conj_comp g hg
  intro a ha b hb
  rw [Subgroup.mem_centralizer_iff] at ha hb
  have ha' : g * a = a * g := ha g (Set.mem_singleton g)
  have hb' : g * b = b * g := hb g (Set.mem_singleton g)
  rw [hp] at ha' hb'
  exact mul_comm_of_conj p (compUnit g) _ _ (coe_compUnit g) a b ha'.symm hb'.symm

end OrbitalCutoffAux.Cyclic

namespace OrbitalCutoffAux
namespace Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def integralSubgroup : Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := AutomorphicForm.localIntegralSet K v
  one_mem' := AutomorphicForm.one_mem_localIntegralSet K v
  mul_mem' := by
    intro a b ha hb
    have ha' := (AutomorphicForm.mem_localIntegralSet K v (g := a)).1 ha
    have hb' := (AutomorphicForm.mem_localIntegralSet K v (g := b)).1 hb
    refine (AutomorphicForm.mem_localIntegralSet K v (g := a * b)).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (ha'.1 i k) (hb'.1 k j)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hb'.2 i k) (ha'.2 k j)
  inv_mem' := by
    intro a ha
    have ha' := (AutomorphicForm.mem_localIntegralSet K v (g := a)).1 ha
    refine (AutomorphicForm.mem_localIntegralSet K v (g := a⁻¹)).2 ⟨ha'.2, ?_⟩
    rw [inv_inv]
    exact ha'.1

private theorem coe_integralSubgroup :
    (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) = AutomorphicForm.localIntegralSet K v :=
  rfl

private theorem isCompact_integralSubgroup
    : IsCompact (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_integralSubgroup]
  exact AutomorphicForm.isCompact_localIntegralSet K v

private theorem isOpen_integralSubgroup : IsOpen (integralSubgroup K v : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_integralSubgroup]
  exact AutomorphicForm.isOpen_localIntegralSet K v

private theorem isClosed_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed (AutomorphicForm.localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have h : (AutomorphicForm.localCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) =
      {x | γ * x = x * γ} := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem borelSpace_localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (AutomorphicForm.localCentralizer K v γ) _ (AutomorphicForm.localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (AutomorphicForm.localCentralizerBorel K v γ) rfl

private theorem measurable_of_isLocallyConstant {w : GL (Fin 2) (v.adicCompletion K) → ℝ} (hw : IsLocallyConstant w) :
    @Measurable (GL (Fin 2) (v.adicCompletion K)) ℝ (AutomorphicForm.localGLBorel K v) _ w := by
  letI := AutomorphicForm.localGLBorel K v
  haveI := AutomorphicForm.borelSpace_localGLBorel K v
  exact hw.continuous.measurable

private theorem isSectionFn_of_cutoff (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (Ω : Set (GL (Fin 2) (v.adicCompletion K)))
    (w : GL (Fin 2) (v.adicCompletion K) → ℝ)
    (h0 : ∀ x, 0 ≤ w x) (hlc : IsLocallyConstant w) (hsupp : HasCompactSupport w)
    (hint : ∀ x : GL (Fin 2) (v.adicCompletion K),
      (∃ t ∈ AutomorphicForm.localCentralizer K v γ, ∃ d ∈ Ω, x = t * d) →
        ∫ t : AutomorphicForm.localCentralizer K v γ, w (t * x) ∂τ = 1)
    (hΩ : ∀ x : GL (Fin 2) (v.adicCompletion K), fv (x⁻¹ * γ * x) ≠ 0 →
      ∃ t ∈ AutomorphicForm.localCentralizer K v γ, ∃ d ∈ Ω, x = t * d) :
    AutomorphicForm.IsSectionFn K v γ τ fv w :=
  ⟨h0, measurable_of_isLocallyConstant K v hlc, hsupp, fun x hx => hint x (hΩ x hx)⟩

end OrbitalCutoffAux.Local

namespace OrbitalCutoffAux
namespace Orbit

open Topology

section Generic

variable {F : Type*} [Field F]

private def orbitSet (γ : GL (Fin 2) F) : Set (GL (Fin 2) F) :=
  {m | Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F)} ∩
    {m | Matrix.det (m : Matrix (Fin 2) (Fin 2) F) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) F)}

private theorem mem_orbitSet_iff {γ m : GL (Fin 2) F} :
    m ∈ orbitSet γ ↔
      Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ∧
        Matrix.det (m : Matrix (Fin 2) (Fin 2) F) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) :=
  Iff.rfl

private theorem self_mem_orbitSet (γ : GL (Fin 2) F) : γ ∈ orbitSet γ := ⟨rfl, rfl⟩

private theorem conj_mem_orbitSet {γ m : GL (Fin 2) F} (g : GL (Fin 2) F) (hm : m ∈ orbitSet γ) :
    g * m * g⁻¹ ∈ orbitSet γ := by
  obtain ⟨htr, hdet⟩ := hm
  have htr' : Matrix.trace ((g * m * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet' : Matrix.det ((g * m * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.det (m : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  exact ⟨htr'.trans htr, hdet'.trans hdet⟩

@[reducible] private def conjMulAction (γ : GL (Fin 2) F) : MulAction (GL (Fin 2) F) (orbitSet γ) where
  smul g m := ⟨g * m * g⁻¹, conj_mem_orbitSet g m.2⟩
  one_smul m := Subtype.ext (by
    show (1 : GL (Fin 2) F) * (m : GL (Fin 2) F) * 1⁻¹ = m
    rw [inv_one, mul_one, one_mul])
  mul_smul g h m := Subtype.ext (by
    show g * h * (m : GL (Fin 2) F) * (g * h)⁻¹ = g * (h * (m : GL (Fin 2) F) * h⁻¹) * g⁻¹
    simp only [mul_inv_rev, mul_assoc])

attribute [local instance] conjMulAction

private theorem val_smul (γ g : GL (Fin 2) F) (m : orbitSet γ) :
    ((g • m : orbitSet γ) : GL (Fin 2) F) = g * m * g⁻¹ := rfl

private theorem isPretransitive_conj (γ : GL (Fin 2) F)
    (hconj : ∀ m ∈ orbitSet γ, ∃ y : GL (Fin 2) F, y * γ * y⁻¹ = m) :
    MulAction.IsPretransitive (GL (Fin 2) F) (orbitSet γ) :=
  ⟨fun a b => by
    obtain ⟨ya, hya⟩ := hconj a.1 a.2
    obtain ⟨yb, hyb⟩ := hconj b.1 b.2
    refine ⟨yb * ya⁻¹, Subtype.ext ?_⟩
    rw [val_smul, ← hya, ← hyb]
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]⟩

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_trace_val :
    Continuous fun m : GL (Fin 2) F => Matrix.trace (m : Matrix (Fin 2) (Fin 2) F) :=
  (Units.continuous_val :
    Continuous fun m : GL (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F)).matrix_trace

private theorem continuous_det_val :
    Continuous fun m : GL (Fin 2) F => Matrix.det (m : Matrix (Fin 2) (Fin 2) F) :=
  (Units.continuous_val :
    Continuous fun m : GL (Fin 2) F => (m : Matrix (Fin 2) (Fin 2) F)).matrix_det

private theorem continuous_conj_val (γ : GL (Fin 2) F) :
    Continuous fun p : GL (Fin 2) F × orbitSet γ => ((p.1 • p.2 : orbitSet γ) : GL (Fin 2) F) := by
  show Continuous fun p : GL (Fin 2) F × orbitSet γ => p.1 * (p.2 : GL (Fin 2) F) * p.1⁻¹
  exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv

private theorem continuousSMul_conj (γ : GL (Fin 2) F) : ContinuousSMul (GL (Fin 2) F) (orbitSet γ) :=
  ⟨continuous_induced_rng.2 (continuous_conj_val γ)⟩

variable [T2Space F]

private theorem isClosed_orbitSet (γ : GL (Fin 2) F) : IsClosed (orbitSet γ) :=
  (isClosed_eq continuous_trace_val continuous_const).inter
    (isClosed_eq continuous_det_val continuous_const)

private theorem exists_isCompact_centralizer_mul
    [LocallyCompactSpace (GL (Fin 2) F)] [SigmaCompactSpace (GL (Fin 2) F)]
    (γ : GL (Fin 2) F)
    (hconj : ∀ m ∈ orbitSet γ, ∃ y : GL (Fin 2) F, y * γ * y⁻¹ = m)
    (K₀ : Subgroup (GL (Fin 2) F)) (hK₀c : IsCompact (K₀ : Set (GL (Fin 2) F)))
    (hK₀o : IsOpen (K₀ : Set (GL (Fin 2) F)))
    (C : Set (GL (Fin 2) F)) (hC : IsCompact C) :
    ∃ Ω : Set (GL (Fin 2) F), IsCompact Ω ∧
      ∀ x : GL (Fin 2) F, x⁻¹ * γ * x ∈ C →
        ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) F)), ∃ d ∈ Ω, x = t * d := by
  haveI : ContinuousSMul (GL (Fin 2) F) (orbitSet γ) := continuousSMul_conj γ
  haveI : MulAction.IsPretransitive (GL (Fin 2) F) (orbitSet γ) := isPretransitive_conj γ hconj
  haveI : LocallyCompactSpace (orbitSet γ) := (isClosed_orbitSet γ).locallyCompactSpace
  obtain ⟨γX, hγXv⟩ : ∃ m : orbitSet γ, (m : GL (Fin 2) F) = γ := ⟨⟨γ, self_mem_orbitSet γ⟩, rfl⟩
  have hopen : IsOpenMap fun g : GL (Fin 2) F => g • γX := isOpenMap_smul_of_sigmaCompact γX
  have hCXc : IsCompact (Subtype.val ⁻¹' C : Set (orbitSet γ)) :=
    (isClosed_orbitSet γ).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hWo : ∀ g : GL (Fin 2) F, IsOpen ((fun g' : GL (Fin 2) F => g' • γX) ''
      ((fun k : GL (Fin 2) F => g * k) '' (K₀ : Set (GL (Fin 2) F)))) :=
    fun g => hopen _ (isOpenMap_mul_left g _ hK₀o)
  have hcov : (Subtype.val ⁻¹' C : Set (orbitSet γ)) ⊆ ⋃ g : GL (Fin 2) F,
      (fun g' : GL (Fin 2) F => g' • γX) ''
        ((fun k : GL (Fin 2) F => g * k) '' (K₀ : Set (GL (Fin 2) F))) := by
    intro m _
    obtain ⟨y, hy⟩ := hconj m.1 m.2
    refine Set.mem_iUnion.2 ⟨y, y * 1, ⟨1, K₀.one_mem, rfl⟩, Subtype.ext ?_⟩
    rw [val_smul, mul_one, hγXv]
    exact hy
  obtain ⟨s, hs⟩ := hCXc.elim_finite_subcover _ hWo hcov
  refine ⟨⋃ g ∈ s, (fun k : GL (Fin 2) F => k⁻¹ * g⁻¹) '' (K₀ : Set (GL (Fin 2) F)), ?_, ?_⟩
  · exact s.isCompact_biUnion fun g _ => hK₀c.image (continuous_inv.mul continuous_const)
  · intro x hx
    have hxm : x⁻¹ * γ * x ∈ orbitSet γ := by
      have h := conj_mem_orbitSet x⁻¹ (self_mem_orbitSet γ)
      rwa [inv_inv] at h
    have hmem : (⟨x⁻¹ * γ * x, hxm⟩ : orbitSet γ) ∈ (Subtype.val ⁻¹' C : Set (orbitSet γ)) := hx
    obtain ⟨g, hg, hW⟩ := Set.mem_iUnion₂.1 (hs hmem)
    obtain ⟨g', ⟨k, hk, hgk⟩, hk'⟩ := hW
    subst hgk
    have h1 : g * k * γ * (g * k)⁻¹ = x⁻¹ * γ * x := by
      have h0 := congrArg Subtype.val hk'
      simp only [val_smul, hγXv] at h0
      exact h0
    have h2 : g * k * γ = x⁻¹ * γ * x * (g * k) := mul_inv_eq_iff_eq_mul.mp h1
    have h3 : x * (g * k) * γ = γ * (x * (g * k)) := by
      rw [mul_assoc, h2]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    refine ⟨x * (g * k), ?_, k⁻¹ * g⁻¹, Set.mem_iUnion₂.2 ⟨g, hg, k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact h3.symm
    · simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Generic

section Local

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem secondCountableTopology_localGL :
    SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem sigmaCompactSpace_localGL : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  haveI := AutomorphicForm.locallyCompactSpace_localGL K v
  haveI := secondCountableTopology_localGL K v
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

private theorem exists_isCompact_localCentralizer_mul (γ : GL (Fin 2) (v.adicCompletion K))
    (hconj : ∀ m ∈ orbitSet γ, ∃ y : GL (Fin 2) (v.adicCompletion K), y * γ * y⁻¹ = m)
    (K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hK₀c : IsCompact (K₀ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hK₀o : IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))))
    (C : Set (GL (Fin 2) (v.adicCompletion K))) (hC : IsCompact C) :
    ∃ Ω : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ * x ∈ C →
        ∃ t ∈ AutomorphicForm.localCentralizer K v γ, ∃ d ∈ Ω, x = t * d := by
  haveI := AutomorphicForm.locallyCompactSpace_localGL K v
  haveI := sigmaCompactSpace_localGL K v
  exact exists_isCompact_centralizer_mul γ hconj K₀ hK₀c hK₀o C hC

end Local

end OrbitalCutoffAux.Orbit

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
      AutomorphicForm.IsSectionFn K v γ τ fv w ∧ IsLocallyConstant w := by
  obtain ⟨D, hD, hDx⟩ :=
    OrbitalCutoffAux.Orbit.exists_isCompact_localCentralizer_mul K v γ
      (fun m hm => OrbitalCutoffAux.Cyclic.exists_conj_of_trace_det γ m hγ hm.1 hm.2)
      (OrbitalCutoffAux.Local.integralSubgroup K v) (OrbitalCutoffAux.Local.isCompact_integralSubgroup K v)
      (OrbitalCutoffAux.Local.isOpen_integralSubgroup K v) (tsupport fv) hfv.2
  obtain ⟨w, h0, hlc, hsupp, hint⟩ :=
    @MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one _ _ _ _
      (OrbitalCutoffAux.Local.integralSubgroup K v) (OrbitalCutoffAux.Local.isCompact_integralSubgroup K v)
      (OrbitalCutoffAux.Local.isOpen_integralSubgroup K v)
      (AutomorphicForm.localCentralizer K v γ) (OrbitalCutoffAux.Local.isClosed_localCentralizer K v γ)
      (OrbitalCutoffAux.Cyclic.centralizer_comm γ hγ)
      (AutomorphicForm.localCentralizerBorel K v γ)
        (OrbitalCutoffAux.Local.borelSpace_localCentralizerBorel K v γ) τ ‹_› D hD
  exact ⟨w, OrbitalCutoffAux.Local.isSectionFn_of_cutoff K v γ τ fv D w h0 hlc hsupp hint
    fun x hx => hDx x (subset_tsupport fv hx), hlc⟩

end S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn (solution)
