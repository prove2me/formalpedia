-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:10.864366+00:00
-- url     : https://prove2.me/theorems/f4fd0597-3a81-44df-bb91-5738d67b4116
-- title:
--   Imported Analytic Inputs
-- statement:
--   Definitions and structural lemmas for Imported Analytic Inputs, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
abbrev Circle := AddCircle (2 * Real.pi)
noncomputable def μCircle : MeasureTheory.Measure Circle :=
  AddCircle.haarAddCircle
noncomputable abbrev muCircle : MeasureTheory.Measure Circle := μCircle
def Cavg : ℝ := 1
def Crot : ℝ := 64 * Real.pi
noncomputable def zeta (x : Circle) : ℂ :=
  AddCircle.toCircle x
noncomputable def circleChar (n : Nat) : Circle -> ℂ :=
  fun x => zeta x ^ n
structure CircleArc where
  /-- `left`: left. -/
  left : ℝ
  /-- `right`: right. -/
  right : ℝ
  left_le_right : left ≤ right
  width_le_period : right - left ≤ 2 * Real.pi
def arcLength (I : CircleArc) : ℝ := I.right - I.left
def arcParam (I : CircleArc) (t : ℝ) : Circle :=
  QuotientAddGroup.mk (I.left + t * arcLength I)
def arcSet (I : CircleArc) : Set Circle :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, arcParam I t = x}
noncomputable def carrierArc (N : Nat) (k : Fin N) : CircleArc where
  left := (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ)
  right := (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
  left_le_right := by
    have hN : 0 <= (N : ℝ) := by exact_mod_cast Nat.le_of_lt k.pos
    apply div_le_div_of_nonneg_right ?_ hN
    gcongr
    exact_mod_cast Nat.le_succ k.1
  width_le_period := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
    have hNge : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast k.pos
    have hpi_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
    have hwidth :
        (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
          (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) =
        (2 * Real.pi) / (N : ℝ) := by
      field_simp [ne_of_gt hNpos]
      norm_num
    rw [hwidth]
    exact div_le_self hpi_nonneg hNge
noncomputable def carrierAverage {N : Nat} (k : Fin N)
    (f : Circle -> ℂ) : ℂ :=
  (N : ℂ) * ∫ x in arcSet (carrierArc N k), f x ∂ μCircle
noncomputable def arcIntegral (I : CircleArc) (f : Circle -> ℝ) : ℝ :=
  ∫ x in arcSet I, f x ∂ μCircle
noncomputable def arcAverage (I : CircleArc) (f : Circle -> ℂ) : ℂ :=
  (arcLength I)⁻¹ • ∫ x in arcSet I, f x ∂ μCircle
abbrev RealVec (d : Nat) := EuclideanSpace ℝ (Fin d)
abbrev PhaseSpace (d : Nat) := RealVec d × RealVec d
abbrev L2Real (d : Nat) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
noncomputable def stftRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun h f ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) t) *
        star ((h : RealVec d -> ℂ) (t - ξ.1)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))
noncomputable def ambiguityRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun f g ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • ξ.1))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • ξ.1))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))
noncomputable def symplecticFourierRep {d : Nat}
    (F : PhaseSpace d -> ℂ) : PhaseSpace d -> ℂ :=
  fun ξ =>
    ∫ η : PhaseSpace d,
      F η * Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))
def symplecticFormLinear {d : Nat} : PhaseSpace d →ₗ[ℝ] PhaseSpace d →ₗ[ℝ] ℝ where
  toFun η :=
    { toFun := fun ξ => inner ℝ η.1 ξ.2 - inner ℝ η.2 ξ.1
      map_add' := by
        intro ξ ζ
        simp [inner_add_right]
        ring
      map_smul' := by
        intro c ξ
        simp [inner_smul_right]
        ring }
  map_add' := by
    intro η θ
    apply LinearMap.ext
    intro ξ
    simp [inner_add_left]
    ring
  map_smul' := by
    intro c η
    apply LinearMap.ext
    intro ξ
    simp [inner_smul_left]
    ring
theorem exists_schwartz_lpNorm_sub_le_realVec {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SchwartzMap (RealVec d) ℂ,
      MeasureTheory.lpNorm (f - (s : RealVec d -> ℂ)) 2
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) ≤ ε := by
  let μ : MeasureTheory.Measure (RealVec d) := MeasureTheory.volume
  obtain ⟨g, hg₁, hg₂, hg₃⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (μ := μ) (p := (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (by norm_num : 1 ≤ (2 : ENNReal)) hf hε
  let s : SchwartzMap (RealVec d) ℂ := hg₁.toSchwartzMap hg₂
  have hs : MeasureTheory.MemLp (f - (s : RealVec d -> ℂ)) 2 μ :=
    hf.sub (s.memLp 2 μ)
  have hg₃' :
      MeasureTheory.eLpNorm (f - (s : RealVec d -> ℂ)) 2 μ ≤ ENNReal.ofReal ε := hg₃
  refine ⟨s, ?_⟩
  rw [← MeasureTheory.toReal_eLpNorm hs.aestronglyMeasurable]
  exact (ENNReal.toReal_le_toReal hs.eLpNorm_ne_top (by simp)).mpr hg₃' |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)
noncomputable def schwartzApproxRealVec {d : Nat}
    {f : RealVec d -> ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
    (n : Nat) : SchwartzMap (RealVec d) ℂ :=
  Classical.choose <|
    exists_schwartz_lpNorm_sub_le_realVec (f := f) hf
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
def IsL2Rep {d : Nat} (f : L2Real d) (fRep : RealVec d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp fRep 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)),
    hf_mem.toLp fRep = f
noncomputable def translateL2 {d : Nat} (a : RealVec d) (f : L2Real d) : L2Real d :=
  DomAddAct.mk a +ᵥ f
noncomputable def modulationPhase {d : Nat} (ω : RealVec d) (t : RealVec d) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))
theorem modulationPhase_norm {d : Nat} (ω t : RealVec d) :
    ‖modulationPhase ω t‖ = 1 := by
  unfold modulationPhase
  rw [Complex.norm_exp]
  have hre :
      (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]
theorem sub_const_hasTemperateGrowth {d : Nat} (a : RealVec d) :
    (fun x : RealVec d => x - a).HasTemperateGrowth := by fun_prop
theorem sub_const_antilipschitz {d : Nat} (a : RealVec d) :
    AntilipschitzWith 1 (fun x : RealVec d => x - a) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  simp
noncomputable def schwartzCompSubConstCLM {d : Nat} (a : RealVec d) :
    SchwartzMap (RealVec d) ℂ →L[ℂ] SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (K := 1) (g := fun x : RealVec d => x - a)
    (by exact sub_const_hasTemperateGrowth a)
    (by exact sub_const_antilipschitz a)
@[simp] theorem schwartzCompSubConstCLM_apply {d : Nat} (a : RealVec d)
    (f : SchwartzMap (RealVec d) ℂ) :
    schwartzCompSubConstCLM a f = f ∘ fun x : RealVec d => x - a := by rfl
def stftWindowSchwartz {d : Nat} (x : RealVec d)
    (h : SchwartzMap (RealVec d) ℂ) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (F := ℂ) (G := ℂ) Complex.conjCLE
    (schwartzCompSubConstCLM x h)
@[simp] theorem stftWindowSchwartz_apply {d : Nat}
    (x t : RealVec d) (h : SchwartzMap (RealVec d) ℂ) :
    stftWindowSchwartz x h t = star (h (t - x)) := by simp [stftWindowSchwartz]
def stftSliceSchwartz {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (stftWindowSchwartz x h).hasTemperateGrowth f
@[simp] theorem stftSliceSchwartz_apply {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x t : RealVec d) :
    stftSliceSchwartz h f x t = f t * star (h (t - x)) := by simp [stftSliceSchwartz]
theorem modulateL2_mem {d : Nat} (ω : RealVec d) (f : L2Real d) :
    MeasureTheory.MemLp
      (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
      2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  have hf := MeasureTheory.Lp.memLp f
  refine hf.of_le ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by
      unfold modulationPhase
      fun_prop)).mul hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul, modulationPhase_norm]
      simp
noncomputable def modulateL2 {d : Nat} (ω : RealVec d) (f : L2Real d) : L2Real d :=
  (private_decl% (modulateL2_mem ω f)).toLp
    (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
end DimdPolyLEAN


