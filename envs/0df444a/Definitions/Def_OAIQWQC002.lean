-- Prove2me | Definitions.Def_OAIQWQC002
-- name    : OAIQWQC002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:04:23.834002+00:00
-- url     : https://prove2.me/theorems/b5c807af-12e8-482c-8937-fc519ba7041e
-- title:
--   OpenAI quadric-surface split: the bundle defined by three graphs and its trace metrics (definitions bundle 3 of 5)
-- statement:
--   The third definitions bundle of the split of OpenAI's proof of the counterexample to Griffiths' positivity conjecture on the quadric surface (`OAI.QuadricCounterexample.main_theorem`). It holds OpenAI's definitions from the modules listed below of `lean/OAI/Geometry/QuadricBundles` (OpenAI, *Ample rank-two bundles on the quadric surface without Griffiths-positive metrics*, OpenAI Math Release, September 24, 2026, result family 050, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them:
--   - the standard charts of $\mathbb P^1 \times \mathbb P^1$ and their coordinate changes (`StandardChart`, `coordinateChange`, `globalTransition`), the power pullbacks and twists (`pullbackPolynomial`, `powerPullbackTwist`);
--   - OpenAI's equalizer data and the bundle glued from three graphs of Section 2 of the paper (`EqualizerData`, `bundle`, `GraphScalars`, `graphOne`, `graphTwo`, `graphThree`, with the matrices and polynomials they use);
--   - the weak limits, trace metrics and matrix dynamics of Sections 4–5 (modules `WeakLimits`, `TraceMetrics`, `TraceExtraction`, `MatrixDynamics`).
--
--   Several of these structures carry proof fields, so the bundle also contains the 385 lemmas their bodies need. One of them is the plurisubharmonicity of $C^2$ functions with nonnegative Levi form (`DiskPshOn.of_C2_leviTrace_nonneg`). That lemma uses the subharmonicity of $C^2$ functions with nonnegative Laplacian, which this bundle does not prove again: it imports the published statement `OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg` of this split, which must be Proved first.
--
--   The compatibility lemmas `ite_eq_left`, `ite_eq_right` and `dite_eq_left` (the corresponding `if_pos`, `if_neg`, `dif_pos`; OpenAI's code uses these newer Lean names) are declared at the top inside namespace `OAI`. One proof here differs from OpenAI's text: after `convert hh using 1`, this Mathlib leaves an instance side goal that the trailing `rfl` does not close, so the step is `exact hh` (the goal is definitionally `hh`).
--
--   The definitions of the published statement come from the published bundle `Def_QuadricBundles`. The bundle also imports the definitions bundle `OAIQWQC001`.
--
--   Modules: `BinaryForms.lean`, `Charts.lean`, `Compactness.lean`, `Compat.lean` (the compatibility lemmas), `DualForms.lean`, `Embedding.lean`, `Equalizer.lean`, `Gluing.lean`, `Graphs.lean`, `LaurentCech.lean`, `LineFactors.lean`, `MatrixDynamics.lean`, `MatrixRepresentative.lean`, `Noncollapse.lean`, `Plurisubharmonic.lean`, `PointwiseRepresentative.lean`, `PolynomialGeneration.lean`, `ProjectiveEquations.lean`, `Regularity.lean`, `RegularMatrices.lean`, `RootTrace.lean`, `SymmetricFlags.lean`, `TraceExtraction.lean`, `TraceMetrics.lean`, `TriangularSections.lean`, `WeakBaseChange.lean`, `WeakLimits.lean`.
-- source:
--   OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf, Sections 2–4; Apache License 2.0); definitions carved from lean/OAI/Geometry/QuadricBundles at commit adc7f12

import Mathlib
import Definitions.Def_QuadricBundles
import Definitions.Def_OAIQWQC001
import Theorems.Thm_OAI_QuadricCounterexample_DiskSubharmonicOn_of_C2_laplacian_nonneg

section
-- module Solutions.OAIQW_QuadricCounterexample.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Charts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology Metric OnePoint
noncomputable section
open scoped Matrix.Norms.Elementwise ComplexOrder

@[simp] lemma reciprocalP1_infty : reciprocalP1 ∞ = (0 : ℂ) := rfl
@[simp] lemma reciprocalP1_zero : reciprocalP1 (0 : ℂ) = ∞ := by simp [reciprocalP1]
lemma reciprocalP1_coe {z : ℂ} (hz : z ≠ 0) : reciprocalP1 z = (z⁻¹ : ℂ) := by
  simp [reciprocalP1,hz]

@[simp] lemma reciprocalP1_involutive (x : ProjectiveLine) :
    reciprocalP1 (reciprocalP1 x) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z; simp
    · rw [reciprocalP1_coe hz, reciprocalP1_coe (inv_ne_zero hz), inv_inv]

lemma affineP1_cover (x : ProjectiveLine) : ∃ i : Fin 2, ∃ z : ℂ, affineP1 i z = x := by
  induction x using OnePoint.rec with
  | infty => exact ⟨0,0,by simp [affineP1]⟩
  | coe z => exact ⟨1,z,rfl⟩

lemma affineQuadric_cover (x : QuadricSurface) :
    ∃ i : Fin 2 × Fin 2, ∃ z : ℂ × ℂ, affineQuadric i z = x := by
  obtain ⟨i,z,hz⟩ := affineP1_cover x.1
  obtain ⟨j,w,hw⟩ := affineP1_cover x.2
  exact ⟨(i,j),(z,w),Prod.ext hz hw⟩

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set OnePoint MvPolynomial
noncomputable section

@[simp] lemma coordP1_affine (i : Fin 2) (z : ℂ) : coordP1 i (affineP1 i z) = z := by
  fin_cases i <;> simp [coordP1, affineP1]

@[simp] lemma coordQuadric_affine (i : Fin 2 × Fin 2) (z : BaseCoordinates) :
    coordQuadric i (affineQuadric i z) = z := by
  ext <;> simp [coordQuadric, affineQuadric]

lemma affineQuadric_coord {i : Fin 2 × Fin 2} {x : QuadricSurface}
    (hx : x ∈ range (affineQuadric i)) : affineQuadric i (coordQuadric i x) = x := by
  obtain ⟨z,rfl⟩ := hx
  rw [coordQuadric_affine]

lemma mem_range_affineP1 (i : Fin 2) (x : ProjectiveLine) :
    x ∈ range (affineP1 i) ↔ if i = 0 then x ≠ (0 : ℂ) else x ≠ ∞ := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    constructor
    · rintro ⟨z,rfl⟩ h
      have hh := congrArg reciprocalP1 h
      simp [affineP1] at hh
    · intro hx
      refine ⟨coordP1 0 x, ?_⟩
      induction x using OnePoint.rec with
      | infty => simp [coordP1,affineP1]
      | coe z =>
        have hz : z ≠ 0 := by simpa using hx
        simp [coordP1,affineP1,reciprocalP1_coe hz, reciprocalP1_coe (inv_ne_zero hz)]
  · constructor
    · rintro ⟨z,rfl⟩; simp [affineP1]
    · intro hx
      induction x using OnePoint.rec with
      | infty => exact False.elim (hx rfl)
      | coe z => exact ⟨z,rfl⟩

lemma powerP1_affine {m : ℕ} (hm : 0 < m) (i : Fin 2) (z : ℂ) :
    powerP1 m (affineP1 i z) = affineP1 i (z^m) := by
  fin_cases i
  · by_cases hz : z = 0
    · subst z; simp [affineP1,powerP1,hm.ne']
    · simp [affineP1,reciprocalP1_coe hz, reciprocalP1_coe (pow_ne_zero m hz),
        powerP1,inv_pow]
  · rfl

lemma powerQuadric_affine {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2) (z : BaseCoordinates) :
    powerQuadric m (affineQuadric i z) = affineQuadric i (z.1^m,z.2^m) := by
  simp [powerQuadric,affineQuadric,powerP1_affine hm]

lemma powerP1_mem_range_iff {m : ℕ} (hm : 0 < m) (i : Fin 2) (x : ProjectiveLine) :
    powerP1 m x ∈ range (affineP1 i) ↔ x ∈ range (affineP1 i) := by
  rw [mem_range_affineP1,mem_range_affineP1]
  induction x using OnePoint.rec with
  | infty => simp [powerP1]
  | coe z =>
    by_cases hi : i = 0
    · simp [powerP1,hi,pow_eq_zero_iff hm.ne']
    · simp [powerP1,hi]

lemma mem_range_affineQuadric (i : Fin 2 × Fin 2) (x : QuadricSurface) :
    x ∈ range (affineQuadric i) ↔ x.1 ∈ range (affineP1 i.1) ∧ x.2 ∈ range (affineP1 i.2) := by
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨⟨z.1,rfl⟩,⟨z.2,rfl⟩⟩
  · rintro ⟨⟨z,hz⟩,⟨w,hw⟩⟩; exact ⟨(z,w),Prod.ext hz hw⟩

lemma powerQuadric_mem_range_iff {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2) (x : QuadricSurface) :
    powerQuadric m x ∈ range (affineQuadric i) ↔ x ∈ range (affineQuadric i) := by
  rw [mem_range_affineQuadric,mem_range_affineQuadric]
  exact and_congr (powerP1_mem_range_iff hm i.1 x.1) (powerP1_mem_range_iff hm i.2 x.2)

def pullbackPolynomial (m : ℕ) (p : BasePolynomial) : BasePolynomial :=
  (MvPolynomial.bind₁ fun j ↦ MvPolynomial.X j ^ m) p

lemma baseEval_pullback (m : ℕ) (p : BasePolynomial) (z : BaseCoordinates) :
    baseEval (pullbackPolynomial m p) z = baseEval p (z.1^m,z.2^m) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ ((MvPolynomial.bind₁ _) p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval _ p = MvPolynomial.eval _ p
  apply congrArg (fun f : Fin 2 → ℂ ↦ MvPolynomial.eval f p)
  funext j; fin_cases j <;> simp

lemma power_principalChart {m : ℕ} (hm : 0 < m) (i : Fin 2 × Fin 2)
    (p : BasePolynomial) (x : QuadricSurface) :
    x ∈ principalChart i (pullbackPolynomial m p) ↔ powerQuadric m x ∈ principalChart i p := by
  constructor
  · rintro ⟨hx,hp⟩
    obtain ⟨z,rfl⟩ := hx
    rw [powerQuadric_affine hm]
    constructor
    · exact ⟨_,rfl⟩
    · simpa only [coordQuadric_affine,baseEval_pullback] using hp
  · rintro ⟨hx,hp⟩
    have hx' := (powerQuadric_mem_range_iff hm i x).mp hx
    obtain ⟨z,rfl⟩ := hx'
    constructor
    · exact ⟨_,rfl⟩
    · simpa only [powerQuadric_affine hm,coordQuadric_affine,baseEval_pullback] using hp

lemma coordP1_overlap {i j : Fin 2} {x : ProjectiveLine}
    (hi : x ∈ range (affineP1 i)) (hj : x ∈ range (affineP1 j)) (hij : i ≠ j) :
    coordP1 i x * coordP1 j x = 1 := by
  obtain ⟨z,rfl⟩ := hi
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq,not_true_eq_false]
  · have hz : z ≠ 0 := by
      intro h; subst z
      simp [affineP1] at hj
    rw [coordP1_affine]
    simp [coordP1,affineP1,reciprocalP1_coe hz, mul_inv_cancel₀ hz]
  · have hz : z ≠ 0 := by
      rw [mem_range_affineP1] at hj
      simpa [affineP1] using hj
    simp [coordP1,affineP1,reciprocalP1_coe hz,mul_inv_cancel₀ hz]

lemma hyperplaneTransition_mul (i j k : Fin 2) (x : ProjectiveLine)
    (hi : x ∈ range (affineP1 i)) (hj : x ∈ range (affineP1 j))
    (hk : x ∈ range (affineP1 k)) :
    hyperplaneTransition i j x * hyperplaneTransition j k x = hyperplaneTransition i k x := by
  by_cases hij : i = j
  · subst j; simp [hyperplaneTransition]
  by_cases hjk : j = k
  · subst k; simp [hyperplaneTransition]
  have hik : i = k := by omega
  subst k
  simp only [hyperplaneTransition,hij,hjk,↓reduceIte]
  exact coordP1_overlap hi hj hij

lemma polarizationTransition_mul (i j k : Fin 2 × Fin 2) (x : QuadricSurface)
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j))
    (hk : x ∈ range (affineQuadric k)) :
    polarizationTransition i j x * polarizationTransition j k x = polarizationTransition i k x := by
  rw [mem_range_affineQuadric] at hi hj hk
  unfold polarizationTransition
  calc
    _ = (hyperplaneTransition i.1 j.1 x.1 * hyperplaneTransition j.1 k.1 x.1) *
        (hyperplaneTransition i.2 j.2 x.2 * hyperplaneTransition j.2 k.2 x.2) := by ring
    _ = _ := by rw [hyperplaneTransition_mul _ _ _ _ hi.1 hj.1 hk.1,
      hyperplaneTransition_mul _ _ _ _ hi.2 hj.2 hk.2]

@[simp] lemma baseEval_one (z : BaseCoordinates) : baseEval 1 z = 1 := by simp [baseEval]
@[simp] lemma baseEval_zero (z : BaseCoordinates) : baseEval 0 z = 0 := by simp [baseEval]
@[simp] lemma baseEval_mul (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p*q) z = baseEval p z * baseEval q z := by simp [baseEval]

lemma algebraicallyRegular_polynomial (U : Set BaseCoordinates) (p : BasePolynomial) :
    AlgebraicallyRegularOn U (baseEval p) := by
  intro z _
  exact ⟨p,1,by simp,fun w _ _ ↦ by simp⟩

lemma AlgebraicallyRegularOn.congr {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (he : ∀ z ∈ U, f z = g z) : AlgebraicallyRegularOn U g := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  exact ⟨p,q,hq,fun w hw hqw ↦ (he w hw).symm.trans (h w hw hqw)⟩

lemma AlgebraicallyRegularOn.mul {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hg : AlgebraicallyRegularOn U g) :
    AlgebraicallyRegularOn U (fun z ↦ f z * g z) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  obtain ⟨r,s,hs,k⟩ := hg z hz
  refine ⟨p*r,q*s,by simpa using mul_ne_zero hq hs,?_⟩
  intro w hw hqw
  have hh : baseEval q w ≠ 0 ∧ baseEval s w ≠ 0 := by simpa using hqw
  dsimp only
  rw [h w hw hh.1,k w hw hh.2,baseEval_mul,baseEval_mul,div_mul_div_comm]

lemma AlgebraicallyRegularOn.comp_power {U W : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (m : ℕ)
    (hU : ∀ z ∈ W, (z.1^m,z.2^m) ∈ U) :
    AlgebraicallyRegularOn W (fun z ↦ f (z.1^m,z.2^m)) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf (z.1^m,z.2^m) (hU z hz)
  refine ⟨pullbackPolynomial m p,pullbackPolynomial m q,by simpa [baseEval_pullback] using hq,?_⟩
  intro w hw hqw
  simp only [baseEval_pullback] at hqw ⊢
  exact h _ (hU w hw) hqw

lemma polarizationTransition_polynomial (i j : Fin 2 × Fin 2) (z : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i z) =
      baseEval ((if i.1=j.1 then 1 else MvPolynomial.X 0) *
        (if i.2=j.2 then 1 else MvPolynomial.X 1)) z := by
  simp only [polarizationTransition,hyperplaneTransition,affineQuadric,coordP1_affine]
  split_ifs <;> simp [baseEval]

lemma polarizationTransition_regular (i j : Fin 2 × Fin 2) (U : Set BaseCoordinates) :
    AlgebraicallyRegularOn U (fun z ↦ polarizationTransition i j (affineQuadric i z)) := by
  exact (algebraicallyRegular_polynomial U _).congr (fun z _ ↦ (polarizationTransition_polynomial i j z).symm)

def powerPullbackTwist (G : AlgebraicRankTwoBundle) (m : ℕ) (hm : 0 < m) :
    AlgebraicRankTwoBundle where
  numberOfCharts := G.numberOfCharts
  chart := G.chart
  equation i := pullbackPolynomial m (G.equation i)
  finiteCover i hi := by
    unfold pullbackPolynomial
    rw [G.finiteCover i hi]
    exact map_zero _
  covers x := by
    obtain ⟨i,hi⟩ := G.covers (powerQuadric m x)
    exact ⟨i,(power_principalChart hm _ _ _).mpr hi⟩
  transition i j x := polarizationTransition (G.chart i) (G.chart j) x •
    G.transition i j (powerQuadric m x)
  transition_self i x hx := by
    rw [G.transition_self i _ ((power_principalChart hm _ _ _).mp hx)]
    simp [polarizationTransition,hyperplaneTransition]
  transition_mul i j k x hi hj hk := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [polarizationTransition_mul _ _ _ _ hi.1 hj.1 hk.1]
    rw [G.transition_mul i j k _ ((power_principalChart hm _ _ _).mp hi)
      ((power_principalChart hm _ _ _).mp hj) ((power_principalChart hm _ _ _).mp hk)]
  transition_regular i j a b := by
    have hreg := (G.transition_regular i j a b).comp_power m
      (W := {z | baseEval (pullbackPolynomial m (G.equation i)) z ≠ 0 ∧
        affineQuadric (G.chart i) z ∈ principalChart (G.chart j) (pullbackPolynomial m (G.equation j))})
      (fun z hz ↦ show baseEval (G.equation i) (z.1^m,z.2^m) ≠ 0 ∧
          affineQuadric (G.chart i) (z.1^m,z.2^m) ∈ principalChart (G.chart j) (G.equation j) from
        ⟨by simpa only [baseEval_pullback] using hz.1,
         by rw [← powerQuadric_affine hm]; exact (power_principalChart hm _ _ _).mp hz.2⟩)
    apply ((polarizationTransition_regular (G.chart i) (G.chart j) _).mul hreg).congr
    intro z _
    simp only [powerQuadric_affine hm,Matrix.smul_apply,smul_eq_mul]

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology MvPolynomial
noncomputable section

@[simp] lemma baseEval_add (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p+q) z=baseEval p z+baseEval q z := by simp [baseEval]
@[simp] lemma baseEval_neg (p : BasePolynomial) (z : BaseCoordinates) :
    baseEval (-p) z= -baseEval p z := by simp [baseEval]
@[simp] lemma baseEval_sub (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p-q) z=baseEval p z-baseEval q z := by simp [baseEval]
@[simp] lemma baseEval_C (a : ℂ) (z : BaseCoordinates) : baseEval (C a) z=a := by simp [baseEval]

lemma analytic_baseEval (p : BasePolynomial) : AnalyticOnNhd ℂ (baseEval p) univ := by
  intro z _
  have hf : ∀ i : Fin 2, AnalyticAt ℂ (fun w : BaseCoordinates ↦ (![w.1,w.2] : Fin 2 → ℂ) i) z := by
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z
    · exact (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z
  have hh := AnalyticAt.aeval_mvPolynomial hf p
  simp only [aeval_eq_eval] at hh
  exact hh

lemma AlgebraicallyRegularOn.analyticOnNhd {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hU : IsOpen U) : AnalyticOnNhd ℂ f U := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  have ha := (analytic_baseEval p z (mem_univ _)).div (analytic_baseEval q z (mem_univ _)) hq
  apply ha.congr
  filter_upwards [hU.mem_nhds hz, (analytic_baseEval q z (mem_univ _)).continuousAt.eventually_ne hq]
    with w hw hqw
  exact (h w hw hqw).symm

lemma dense_polynomial_nonzero {p : BasePolynomial} (hp : p ≠ 0) :
    Dense {z | baseEval p z ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU ⟨z,hz⟩
  by_contra! h
  have he : baseEval p =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    by_contra hn
    have : w ∈ U ∩ {z | baseEval p z ≠ 0} := ⟨hw,hn⟩
    rw [h] at this
    exact this
  have hall := (analytic_baseEval p).eq_of_eventuallyEq analyticOnNhd_const he
  apply hp
  apply MvPolynomial.funext
  intro x
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx,map_zero]
  simpa only [baseEval] using congrFun hall (x 0,x 1)

lemma continuous_cancel_polynomial {U : Set BaseCoordinates} (hU : IsOpen U)
    {f g : BaseCoordinates → ℂ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    {p : BasePolynomial} (hp : p ≠ 0)
    (he : ∀ z ∈ U, baseEval p z*f z=baseEval p z*g z) : EqOn f g U := by
  intro z hz
  by_contra hne
  have hat : ContinuousAt (fun w ↦ f w-g w) z :=
    ((hf z hz).continuousAt (hU.mem_nhds hz)).sub ((hg z hz).continuousAt (hU.mem_nhds hz))
  have hn : ∀ᶠ w in 𝓝 z, w ∈ U ∧ f w ≠ g w := by
    filter_upwards [hU.mem_nhds hz,hat.eventually_ne (sub_ne_zero.mpr hne)] with w hw hnw
    exact ⟨hw,sub_ne_zero.mp hnw⟩
  obtain ⟨w,hw,hpw⟩ := mem_closure_iff_nhds.mp (dense_polynomial_nonzero hp z) _ hn
  exact hw.2 (mul_left_cancel₀ hpw (he w hw.1))

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
noncomputable section

def UniformlyRegularOn (U : Set BaseCoordinates) (f : BaseCoordinates → ℂ) : Prop :=
  ∃ p q : BasePolynomial, (∀ z ∈ U, baseEval q z ≠ 0) ∧
    ∀ z ∈ U, f z=baseEval p z/baseEval q z

lemma UniformlyRegularOn.regular {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) : AlgebraicallyRegularOn U f := by
  obtain ⟨p,q,hq,h⟩ := h
  exact fun z hz ↦ ⟨p,q,hq z hz,fun w hw _ ↦ h w hw⟩

lemma UniformlyRegularOn.congr {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) (he : EqOn f g U) : UniformlyRegularOn U g := by
  obtain ⟨p,q,hq,h⟩ := h
  exact ⟨p,q,hq,fun z hz ↦ (he hz).symm.trans (h z hz)⟩

lemma UniformlyRegularOn.mono {U V : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) (hVU : V ⊆ U) : UniformlyRegularOn V f := by
  obtain ⟨p,q,hq,h⟩ := h
  exact ⟨p,q,fun z hz ↦ hq z (hVU hz),fun z hz ↦ h z (hVU hz)⟩

lemma uniformlyRegular_polynomial (U : Set BaseCoordinates) (p : BasePolynomial) :
    UniformlyRegularOn U (baseEval p) := by
  exact ⟨p,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp⟩
lemma uniformlyRegular_const (U : Set BaseCoordinates) (c : ℂ) :
    UniformlyRegularOn U (fun _ ↦ c) := by
  exact ⟨C c,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp⟩

lemma UniformlyRegularOn.add {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z+g z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  obtain ⟨r,s,hs,k⟩ := hg
  refine ⟨p*s+q*r,q*s, fun z hz ↦ by simpa using mul_ne_zero (hq z hz) (hs z hz),?_⟩
  intro z hz
  dsimp only
  rw [h z hz,k z hz]
  simp only [baseEval_add,baseEval_mul]
  exact div_add_div _ _ (hq z hz) (hs z hz)

lemma UniformlyRegularOn.neg {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) : UniformlyRegularOn U (fun z ↦ - f z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  exact ⟨-p,q,hq,fun z hz ↦ by dsimp only; rw [h z hz,baseEval_neg,neg_div]⟩
lemma UniformlyRegularOn.sub {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma UniformlyRegularOn.mul {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z*g z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  obtain ⟨r,s,hs,k⟩ := hg
  refine ⟨p*r,q*s, fun z hz ↦ by simpa using mul_ne_zero (hq z hz) (hs z hz),?_⟩
  intro z hz
  dsimp only
  rw [h z hz,k z hz]
  simp only [baseEval_mul,mul_div_mul_comm]
lemma UniformlyRegularOn.inv {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hn : ∀ z ∈ U, f z ≠ 0) :
    UniformlyRegularOn U (fun z ↦ (f z)⁻¹) := by
  obtain ⟨p,q,hq,h⟩ := hf
  refine ⟨q,p,?_,?_⟩
  · intro z hz he
    apply hn z hz
    rw [h z hz,he,zero_div]
  · intro z hz
    dsimp only
    rw [h z hz,inv_div]
lemma UniformlyRegularOn.pow {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (n : ℕ) : UniformlyRegularOn U (fun z ↦ f z^n) := by
  induction n with
  | zero => simpa using uniformlyRegular_const U 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma UniformlyRegularOn.eval {U : Set BaseCoordinates} {f : Fin 2 → BaseCoordinates → ℂ}
    (hf : ∀ i, UniformlyRegularOn U (f i)) (p : BasePolynomial) :
    UniformlyRegularOn U (fun z ↦ MvPolynomial.eval (fun i ↦ f i z) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using uniformlyRegular_const U c
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,eval_X] using hp.mul (hf i)

lemma squarefree_dvd_of_baseEval_zero {d p : BasePolynomial} (hd : Squarefree d)
    (he : ∀ z, baseEval d z=0 → baseEval p z=0) : d ∣ p := by
  let J : Ideal BasePolynomial := Ideal.span {d}
  have hJ : J.IsRadical := isRadical_iff_span_singleton.mp hd.isRadical
  apply Ideal.mem_span_singleton.mp
  change p ∈ J
  rw [← hJ.radical,← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro z hz
  rw [MvPolynomial.zeroLocus_span] at hz
  have hh := hz _ (Set.mem_singleton _)
  have hz' : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
  rw [hz'] at hh ⊢
  simpa only [aeval_eq_eval,baseEval] using he (z 0,z 1) (by simpa [baseEval,aeval_eq_eval] using hh)

lemma exists_uniformlyRegular_division (r d : BasePolynomial) (hd : Squarefree d)
    (f : BaseCoordinates → ℂ) (hf : UniformlyRegularOn {z | baseEval r z ≠ 0} f)
    (he : ∀ z, baseEval r z ≠ 0 → baseEval d z=0 → f z=0) :
    ∃ k : BaseCoordinates → ℂ, UniformlyRegularOn {z | baseEval r z ≠ 0} k ∧
      ∀ z, baseEval r z ≠ 0 → baseEval d z*k z=f z := by
  obtain ⟨p,q,hq,h⟩ := hf
  have hdiv : d ∣ r*p := by
    apply squarefree_dvd_of_baseEval_zero hd
    intro z hz
    by_cases hr : baseEval r z=0
    · simp [hr]
    · have hv := he z hr hz
      rw [h z hr] at hv
      have hp : baseEval p z=0 := (div_eq_zero_iff).mp hv |>.resolve_right (hq z hr)
      simp [hp]
  obtain ⟨a,ha⟩ := hdiv
  refine ⟨fun z ↦ baseEval a z/baseEval (r*q) z,⟨a,r*q,?_,fun _ _ ↦ rfl⟩,?_⟩
  · intro z hz
    simpa using mul_ne_zero hz (hq z hz)
  · intro z hz
    have hqa := hq z hz
    have heq := congrArg (fun p ↦ baseEval p z) ha
    simp only [baseEval_mul] at heq
    dsimp only
    rw [baseEval_mul,h z hz]
    field_simp
    linear_combination -heq

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.LineFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set MvPolynomial
noncomputable section

abbrev StandardChart := Fin 2 × Fin 2

def overlapPolynomial (i j : StandardChart) : BasePolynomial :=
  (if i.1=j.1 then 1 else X 0)*(if i.2=j.2 then 1 else X 1)
def coordinateOverlap (i j : StandardChart) : Set BaseCoordinates :=
  {z | baseEval (overlapPolynomial i j) z ≠ 0}
def scalarCoordinateChange (i j : Fin 2) (z : ℂ) : ℂ := if i=j then z else z⁻¹
def coordinateChange (i j : StandardChart) (z : BaseCoordinates) : BaseCoordinates :=
  (scalarCoordinateChange i.1 j.1 z.1, scalarCoordinateChange i.2 j.2 z.2)
def scalarFactor (i j : Fin 2) (z : ℂ) : ℂ := if i=j then 1 else z

def firstFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := scalarFactor i.1 j.1 z.1
def secondFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := scalarFactor i.2 j.2 z.2

lemma coordinateOverlap_iff (i j : StandardChart) (z : BaseCoordinates) :
    z ∈ coordinateOverlap i j ↔ (i.1=j.1 ∨ z.1 ≠ 0) ∧ (i.2=j.2 ∨ z.2 ≠ 0) := by
  simp only [coordinateOverlap,mem_ofPred_eq,overlapPolynomial,baseEval_mul]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [h1,h2,baseEval]

lemma scalarCoordinateChange_coord (i j : Fin 2) (z : ℂ) :
    coordP1 j (affineP1 i z)=scalarCoordinateChange i j z := by
  by_cases hij : i=j
  · subst j; simp [scalarCoordinateChange]
  · fin_cases i <;> fin_cases j <;> simp_all only [not_true_eq_false]
    · by_cases hz : z=0
      · subst z; simp [coordP1,affineP1,scalarCoordinateChange]
      · simp [coordP1,affineP1,scalarCoordinateChange,reciprocalP1_coe hz]
    · by_cases hz : z=0
      · subst z; simp [coordP1,affineP1,scalarCoordinateChange]
      · simp [coordP1,affineP1,scalarCoordinateChange,reciprocalP1_coe hz]

lemma coordinateChange_coord (i j : StandardChart) (z : BaseCoordinates) :
    coordQuadric j (affineQuadric i z)=coordinateChange i j z := by
  ext <;> simp only [coordQuadric,affineQuadric,coordinateChange,scalarCoordinateChange_coord]

@[simp] lemma scalarCoordinateChange_self (i : Fin 2) (z : ℂ) :
    scalarCoordinateChange i i z=z := by simp [scalarCoordinateChange]
@[simp] lemma coordinateChange_self (i : StandardChart) (z : BaseCoordinates) :
    coordinateChange i i z=z := by simp [coordinateChange]
lemma scalarCoordinateChange_inv (i j : Fin 2) (z : ℂ) :
    scalarCoordinateChange j i (scalarCoordinateChange i j z)=z := by
  by_cases h : i=j <;> simp [scalarCoordinateChange,h,eq_comm]
lemma coordinateChange_inv (i j : StandardChart) (z : BaseCoordinates) :
    coordinateChange j i (coordinateChange i j z)=z := by
  ext <;> simp [coordinateChange,scalarCoordinateChange_inv]

lemma affineP1_mem_range (i j : Fin 2) (z : ℂ) :
    affineP1 i z ∈ range (affineP1 j) ↔ i=j ∨ z ≠ 0 := by
  by_cases hij : i=j
  · subst j; exact iff_of_true ⟨z,rfl⟩ (Or.inl rfl)
  · rw [mem_range_affineP1]
    fin_cases i <;> fin_cases j <;> simp_all only [not_true_eq_false]
    · by_cases hz : z=0
      · subst z; simp [affineP1]
      · simp [affineP1,reciprocalP1_coe hz,hz]
    · simp [affineP1]

lemma affineQuadric_mem_range (i j : StandardChart) (z : BaseCoordinates) :
    affineQuadric i z ∈ range (affineQuadric j) ↔ z ∈ coordinateOverlap i j := by
  rw [mem_range_affineQuadric,coordinateOverlap_iff]
  exact and_congr (affineP1_mem_range _ _ _) (affineP1_mem_range _ _ _)

lemma affine_coordinateChange (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) :
    affineQuadric j (coordinateChange i j z)=affineQuadric i z := by
  rw [← coordinateChange_coord]
  exact affineQuadric_coord ((affineQuadric_mem_range i j z).mpr hz)

lemma coordinateChange_comp (i j k : StandardChart) {z : BaseCoordinates}
    (hij : z ∈ coordinateOverlap i j) :
    coordinateChange j k (coordinateChange i j z)=coordinateChange i k z := by
  rw [← coordinateChange_coord,affine_coordinateChange i j hij,coordinateChange_coord]

lemma coordinateOverlap_third (i j k : StandardChart) {z : BaseCoordinates}
    (hij : z ∈ coordinateOverlap i j) (hik : z ∈ coordinateOverlap i k) :
    coordinateChange i j z ∈ coordinateOverlap j k := by
  rw [← affineQuadric_mem_range,affine_coordinateChange i j hij]
  exact (affineQuadric_mem_range i k z).mpr hik

lemma coordinateOverlap_open (i j : StandardChart) : IsOpen (coordinateOverlap i j) :=
  isOpen_ne.preimage (analytic_baseEval (overlapPolynomial i j)).continuous

lemma uniformlyRegular_fst (U : Set BaseCoordinates) : UniformlyRegularOn U Prod.fst := by
  exact ⟨X 0,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp [baseEval]⟩
lemma uniformlyRegular_snd (U : Set BaseCoordinates) : UniformlyRegularOn U Prod.snd := by
  exact ⟨X 1,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp [baseEval]⟩

lemma UniformlyRegularOn.comp {U V : Set BaseCoordinates}
    {f : BaseCoordinates → ℂ} {g : BaseCoordinates → BaseCoordinates}
    (hf : UniformlyRegularOn U f)
    (h0 : UniformlyRegularOn V (fun z ↦ (g z).1))
    (h1 : UniformlyRegularOn V (fun z ↦ (g z).2))
    (hg : MapsTo g V U) : UniformlyRegularOn V (fun z ↦ f (g z)) := by
  have hadd (p : BasePolynomial) : UniformlyRegularOn V (fun z ↦ baseEval p (g z)) := by
    have h : ∀ i : Fin 2, UniformlyRegularOn V (fun z ↦ (![ (g z).1,(g z).2 ] : Fin 2 → ℂ) i) := by
      intro i; fin_cases i
      · exact h0
      · exact h1
    exact UniformlyRegularOn.eval h p
  obtain ⟨p,q,hq,h⟩ := hf
  have hn : ∀ z ∈ V, baseEval q (g z) ≠ 0 := fun z hz ↦ hq (g z) (hg hz)
  exact ((hadd p).mul ((hadd q).inv hn)).congr (fun z hz ↦ by
    rw [h (g z) (hg hz),div_eq_mul_inv])

lemma firstFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (firstFactor i j) := by
  unfold firstFactor scalarFactor
  by_cases h : i.1=j.1
  · simpa only [ite_eq_left h] using uniformlyRegular_const U 1
  · simpa only [ite_eq_right h] using uniformlyRegular_fst U
lemma secondFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (secondFactor i j) := by
  unfold secondFactor scalarFactor
  by_cases h : i.2=j.2
  · simpa only [ite_eq_left h] using uniformlyRegular_const U 1
  · simpa only [ite_eq_right h] using uniformlyRegular_snd U

lemma firstFactor_ne_zero {i j : StandardChart} {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) : firstFactor i j z ≠ 0 := by
  have h := ((coordinateOverlap_iff i j z).mp hz).1
  unfold firstFactor scalarFactor
  split_ifs with hi
  · exact one_ne_zero
  · exact h.resolve_left hi
lemma secondFactor_ne_zero {i j : StandardChart} {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) : secondFactor i j z ≠ 0 := by
  have h := ((coordinateOverlap_iff i j z).mp hz).2
  unfold secondFactor scalarFactor
  split_ifs with hi
  · exact one_ne_zero
  · exact h.resolve_left hi

lemma coordinateChange_fst_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ (coordinateChange i j z).1) := by
  by_cases h : i.1=j.1
  · simpa only [coordinateChange,scalarCoordinateChange,ite_eq_left h] using
      uniformlyRegular_fst (coordinateOverlap i j)
  · have hn : ∀ z ∈ coordinateOverlap i j, z.1 ≠ 0 := fun z hz ↦
      (((coordinateOverlap_iff i j z).mp hz).1).resolve_left h
    simpa only [coordinateChange,scalarCoordinateChange,ite_eq_right h] using
      (uniformlyRegular_fst (coordinateOverlap i j)).inv hn
lemma coordinateChange_snd_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ (coordinateChange i j z).2) := by
  by_cases h : i.2=j.2
  · simpa only [coordinateChange,scalarCoordinateChange,ite_eq_left h] using
      uniformlyRegular_snd (coordinateOverlap i j)
  · have hn : ∀ z ∈ coordinateOverlap i j, z.2 ≠ 0 := fun z hz ↦
      (((coordinateOverlap_iff i j z).mp hz).2).resolve_left h
    simpa only [coordinateChange,scalarCoordinateChange,ite_eq_right h] using
      (uniformlyRegular_snd (coordinateOverlap i j)).inv hn

lemma firstFactor_transition (i j : StandardChart) (z : BaseCoordinates) :
    firstFactor i j z=hyperplaneTransition i.1 j.1 (affineQuadric i z).1 := by
  simp [firstFactor,scalarFactor,hyperplaneTransition,affineQuadric]
lemma secondFactor_transition (i j : StandardChart) (z : BaseCoordinates) :
    secondFactor i j z=hyperplaneTransition i.2 j.2 (affineQuadric i z).2 := by
  simp [secondFactor,scalarFactor,hyperplaneTransition,affineQuadric]

lemma firstFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    firstFactor i j z*firstFactor j k (coordinateChange i j z)=firstFactor i k z := by
  rw [firstFactor_transition,firstFactor_transition,firstFactor_transition,affine_coordinateChange i j hj]
  apply hyperplaneTransition_mul
  · exact ⟨z.1,rfl⟩
  · exact (mem_range_affineQuadric j _).mp ((affineQuadric_mem_range i j z).mpr hj) |>.1
  · exact (mem_range_affineQuadric k _).mp ((affineQuadric_mem_range i k z).mpr hk) |>.1
lemma secondFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    secondFactor i j z*secondFactor j k (coordinateChange i j z)=secondFactor i k z := by
  rw [secondFactor_transition,secondFactor_transition,secondFactor_transition,affine_coordinateChange i j hj]
  apply hyperplaneTransition_mul
  · exact ⟨z.2,rfl⟩
  · exact (mem_range_affineQuadric j _).mp ((affineQuadric_mem_range i j z).mpr hj) |>.2
  · exact (mem_range_affineQuadric k _).mp ((affineQuadric_mem_range i k z).mpr hk) |>.2

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Equalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set MvPolynomial Matrix
noncomputable section

structure EqualizerData where
  divisor : StandardChart → BasePolynomial
  lift : StandardChart → BasePolynomial
  reduced : ∀ i, Squarefree (divisor i)
  nonzero : ∀ i, divisor i ≠ 0
  divisor_change : ∀ i j z, z ∈ coordinateOverlap i j →
    baseEval (divisor i) z = (firstFactor i j z*secondFactor i j z)^3*
      baseEval (divisor j) (coordinateChange i j z)
  lift_change : ∀ i j z, z ∈ coordinateOverlap i j → baseEval (divisor i) z=0 →
    secondFactor i j z^24*baseEval (lift j) (coordinateChange i j z)=
      baseEval (lift i) z*firstFactor i j z^24
  lift_unit : ∀ i z, baseEval (divisor i) z=0 → baseEval (lift i) z ≠ 0

namespace EqualizerData
variable (D : EqualizerData)

def topFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := firstFactor i j z^24
def quotientFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := secondFactor i j z^24
def bottomFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  (firstFactor i j z)⁻¹^3*secondFactor i j z^21

def numerator (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  quotientFactor i j z*baseEval (D.lift j) (coordinateChange i j z)-
    baseEval (D.lift i) z*topFactor i j z

lemma topFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (topFactor i j) := (firstFactor_regular i j U).pow 24
lemma quotientFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (quotientFactor i j) := (secondFactor_regular i j U).pow 24
lemma bottomFactor_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (bottomFactor i j) :=
  (((firstFactor_regular i j _).inv fun _ hz ↦ firstFactor_ne_zero hz).pow 3).mul
    ((secondFactor_regular i j _).pow 21)

lemma numerator_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (D.numerator i j) := by
  have h := (uniformlyRegular_polynomial univ (D.lift j)).comp
    (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j)
    (fun _ _ ↦ mem_univ _)
  exact ((quotientFactor_regular i j _).mul h).sub
    ((uniformlyRegular_polynomial _ (D.lift i)).mul (topFactor_regular i j _))

lemma exists_low (i j : StandardChart) :
    ∃ k : BaseCoordinates → ℂ, UniformlyRegularOn (coordinateOverlap i j) k ∧
      ∀ z ∈ coordinateOverlap i j, baseEval (D.divisor i) z*k z=D.numerator i j z := by
  apply exists_uniformlyRegular_division (overlapPolynomial i j) (D.divisor i) (D.reduced i)
    (D.numerator i j) (D.numerator_regular i j)
  intro z hz hd
  exact sub_eq_zero.mpr (D.lift_change i j z hz hd)

def low (i j : StandardChart) : BaseCoordinates → ℂ := (D.exists_low i j).choose
lemma low_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (D.low i j) := (D.exists_low i j).choose_spec.1
lemma low_spec (i j : StandardChart) {z : BaseCoordinates} (hz : z ∈ coordinateOverlap i j) :
    baseEval (D.divisor i) z*D.low i j z=D.numerator i j z := (D.exists_low i j).choose_spec.2 z hz

lemma divisor_factor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) :
    baseEval (D.divisor i) z*bottomFactor i j z=
      quotientFactor i j z*baseEval (D.divisor j) (coordinateChange i j z) := by
  rw [D.divisor_change i j z hz]
  unfold bottomFactor quotientFactor
  have hn := firstFactor_ne_zero hz
  field_simp

lemma topFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    topFactor i j z*topFactor j k (coordinateChange i j z)=topFactor i k z := by
  unfold topFactor
  rw [← mul_pow,firstFactor_mul i j k hj hk]
lemma quotientFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    quotientFactor i j z*quotientFactor j k (coordinateChange i j z)=quotientFactor i k z := by
  unfold quotientFactor
  rw [← mul_pow,secondFactor_mul i j k hj hk]
lemma bottomFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    bottomFactor i j z*bottomFactor j k (coordinateChange i j z)=bottomFactor i k z := by
  unfold bottomFactor
  rw [← firstFactor_mul i j k hj hk,← secondFactor_mul i j k hj hk]
  simp only [_root_.mul_inv_rev,mul_pow]
  ring

lemma numerator_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    baseEval (D.divisor i) z *
      (D.low i j z*topFactor j k (coordinateChange i j z)+
        bottomFactor i j z*D.low j k (coordinateChange i j z))=
      baseEval (D.divisor i) z*D.low i k z := by
  have hjk := coordinateOverlap_third i j k hj hk
  calc
    _ = (baseEval (D.divisor i) z*D.low i j z)*topFactor j k (coordinateChange i j z)+
      (baseEval (D.divisor i) z*bottomFactor i j z)*D.low j k (coordinateChange i j z) := by ring
    _ = D.numerator i j z*topFactor j k (coordinateChange i j z)+
      quotientFactor i j z*(baseEval (D.divisor j) (coordinateChange i j z)*
        D.low j k (coordinateChange i j z)) := by rw [D.low_spec i j hj,D.divisor_factor i j hj]; ring
    _ = D.numerator i j z*topFactor j k (coordinateChange i j z)+
      quotientFactor i j z*D.numerator j k (coordinateChange i j z) := by rw [D.low_spec j k hjk]
    _ = D.numerator i k z := by
      unfold numerator
      rw [coordinateChange_comp i j k hj]
      rw [← topFactor_mul i j k hj hk,← quotientFactor_mul i j k hj hk]
      ring
    _ = _ := (D.low_spec i k hk).symm

lemma low_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    D.low i j z*topFactor j k (coordinateChange i j z)+
      bottomFactor i j z*D.low j k (coordinateChange i j z)=D.low i k z := by
  let U := coordinateOverlap i j ∩ coordinateOverlap i k
  have hU : IsOpen U := (coordinateOverlap_open i j).inter (coordinateOverlap_open i k)
  have h0 := (coordinateChange_fst_regular i j).mono (show U ⊆ coordinateOverlap i j from inter_subset_left)
  have h1 := (coordinateChange_snd_regular i j).mono (show U ⊆ coordinateOverlap i j from inter_subset_left)
  have ha := (topFactor_regular j k univ).comp h0 h1 (fun _ _ ↦ mem_univ _)
  have hl := (D.low_regular j k).comp h0 h1 (fun _ hw ↦ coordinateOverlap_third i j k hw.1 hw.2)
  have hf := (((D.low_regular i j).mono inter_subset_left).mul ha).add
    (((bottomFactor_regular i j).mono inter_subset_left).mul hl)
  have hg := (D.low_regular i k).mono (show U ⊆ coordinateOverlap i k from inter_subset_right)
  exact continuous_cancel_polynomial hU (hf.regular.analyticOnNhd hU).continuousOn
    (hg.regular.analyticOnNhd hU).continuousOn (D.nonzero i)
    (fun w hw ↦ D.numerator_mul i j k hw.1 hw.2) ⟨hj,hk⟩

@[simp] lemma topFactor_self (i : StandardChart) (z : BaseCoordinates) : topFactor i i z=1 := by
  simp [topFactor,firstFactor,scalarFactor]
@[simp] lemma quotientFactor_self (i : StandardChart) (z : BaseCoordinates) : quotientFactor i i z=1 := by
  simp [quotientFactor,secondFactor,scalarFactor]
@[simp] lemma bottomFactor_self (i : StandardChart) (z : BaseCoordinates) : bottomFactor i i z=1 := by
  simp [bottomFactor,firstFactor,secondFactor,scalarFactor]
@[simp] lemma coordinateOverlap_self (i : StandardChart) : coordinateOverlap i i=univ := by
  ext z; simp [coordinateOverlap_iff]

lemma low_self (i : StandardChart) (z : BaseCoordinates) : D.low i i z=0 := by
  have hr := D.low_regular i i
  rw [coordinateOverlap_self] at hr
  apply continuous_cancel_polynomial isOpen_univ
    (hr.regular.analyticOnNhd isOpen_univ).continuousOn continuousOn_const (D.nonzero i) _ (mem_univ z)
  intro w _
  have h := D.low_spec i i (z := w) (by simp)
  simpa [numerator] using h

def coordinateTransition (i j : StandardChart) (z : BaseCoordinates) : TwoMatrix :=
  !![topFactor i j z,0;D.low i j z,bottomFactor i j z]

lemma coordinateTransition_self (i : StandardChart) (z : BaseCoordinates) :
    D.coordinateTransition i i z=1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [coordinateTransition,D.low_self]

lemma coordinateTransition_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    D.coordinateTransition i j z*D.coordinateTransition j k (coordinateChange i j z)=
      D.coordinateTransition i k z := by
  ext a b; fin_cases a <;> fin_cases b
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using topFactor_mul i j k hj hk
  · simp [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two]
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using D.low_mul i j k hj hk
  · simpa [coordinateTransition,Matrix.mul_apply,Fin.sum_univ_two] using bottomFactor_mul i j k hj hk

lemma coordinateTransition_regular (i j : StandardChart) (a b : Fin 2) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ D.coordinateTransition i j z a b) := by
  fin_cases a <;> fin_cases b
  · exact topFactor_regular i j _
  · exact uniformlyRegular_const _ 0
  · exact D.low_regular i j
  · exact bottomFactor_regular i j

end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix
noncomputable section

def standardChartNat (n : ℕ) : StandardChart :=
  if n=0 then (0,0) else if n=1 then (0,1) else if n=2 then (1,0) else (1,1)
def standardEquationNat (n : ℕ) : BasePolynomial := if n<4 then 1 else 0

lemma standardChartNat_surj (i : StandardChart) : ∃ n : ℕ, n<4 ∧ standardChartNat n=i := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · exact ⟨0,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨1,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨2,by norm_num,by simp [standardChartNat]⟩
  · exact ⟨3,by norm_num,by simp [standardChartNat]⟩

lemma principalChart_one (i : StandardChart) : principalChart i 1=range (affineQuadric i) := by
  ext x; simp [principalChart]

lemma standardCharts_cover (x : QuadricSurface) :
    ∃ n, x ∈ principalChart (standardChartNat n) (standardEquationNat n) := by
  obtain ⟨i,z,hz⟩ := affineQuadric_cover x
  obtain ⟨n,hn,hi⟩ := standardChartNat_surj i
  refine ⟨n,?_⟩
  rw [standardEquationNat,ite_eq_left hn,principalChart_one,hi]
  exact ⟨z,hz⟩

namespace EqualizerData
variable (D : EqualizerData)

def globalTransition (i j : StandardChart) (x : QuadricSurface) : TwoMatrix :=
  D.coordinateTransition i j (coordQuadric i x)

lemma globalTransition_self (i : StandardChart) (x : QuadricSurface) :
    D.globalTransition i i x=1 := D.coordinateTransition_self i (coordQuadric i x)

lemma coord_mem_overlap (i j : StandardChart) {x : QuadricSurface}
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j)) :
    coordQuadric i x ∈ coordinateOverlap i j := by
  rw [← affineQuadric_mem_range,affineQuadric_coord hi]
  exact hj

lemma globalTransition_mul (i j k : StandardChart) {x : QuadricSurface}
    (hi : x ∈ range (affineQuadric i)) (hj : x ∈ range (affineQuadric j))
    (hk : x ∈ range (affineQuadric k)) :
    D.globalTransition i j x*D.globalTransition j k x=D.globalTransition i k x := by
  have hc : coordinateChange i j (coordQuadric i x)=coordQuadric j x := by
    rw [← coordinateChange_coord,affineQuadric_coord hi]
  simpa only [globalTransition,hc] using
    D.coordinateTransition_mul i j k (coord_mem_overlap i j hi hj) (coord_mem_overlap i k hi hk)

def bundle : AlgebraicRankTwoBundle where
  numberOfCharts := 4
  chart := standardChartNat
  equation := standardEquationNat
  finiteCover := fun i hi ↦ by simp [standardEquationNat,not_lt.mpr hi]
  covers := standardCharts_cover
  transition := fun i j ↦ D.globalTransition (standardChartNat i) (standardChartNat j)
  transition_self := fun i x _ ↦ D.globalTransition_self _ x
  transition_mul := fun i j k x hi hj hk ↦ D.globalTransition_mul _ _ _ hi.1 hj.1 hk.1
  transition_regular := by
    intro i j a b
    have hr := (D.coordinateTransition_regular (standardChartNat i) (standardChartNat j) a b).mono
      (show {z | baseEval (standardEquationNat i) z ≠ 0 ∧
        affineQuadric (standardChartNat i) z ∈ principalChart (standardChartNat j) (standardEquationNat j)}
        ⊆ coordinateOverlap (standardChartNat i) (standardChartNat j) from
          fun z hz ↦ (affineQuadric_mem_range _ _ z).mp hz.2.1)
    simpa only [globalTransition,coordQuadric_affine] using hr.regular

end EqualizerData
end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Graphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

namespace QuadricCounterexample
open Polynomial
noncomputable section

structure GraphScalars where
  a : ℂ
  s : ℂ
  b : ℂ
  c : ℂ
  a_cube : a^3 = -1
  determinant : s*(1-s) = 1+b*c
  relative_trace : s+a^2*(1-s)+(Real.sqrt 2 : ℂ)*a=0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0

namespace GraphScalars
variable (T : GraphScalars)

def N₁ : ℂ[X] := X^2-X+1
def N₂ : ℂ[X] := X^2+C ((Real.sqrt 2 : ℂ)*T.a)*X+C (T.a^2)
def N₂other : ℂ[X] := X^2-C ((Real.sqrt 2 : ℂ)*T.a)*X+C (T.a^2)
def P₁ : ℂ[X] := C T.c*X^2+C (1-2*T.s)*X-C T.b
def P₂ : ℂ[X] := C T.c*X^2+C (T.a^2*(1-T.s)-T.s)*X-C (T.a^2*T.b)
def L : ℂ[X] := C T.s-C T.c*X
def J : ℂ[X] := C T.b-C (1-T.s)*X

lemma a_twentyfour : T.a^24=1 := by
  rw [show (24 : ℕ)=3*8 by norm_num,pow_mul,T.a_cube]; norm_num

lemma sqrt_two_square : (Real.sqrt 2 : ℂ)^2=2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma N₁_dvd : N₁ ∣ (X : ℂ[X])^24-1 := by
  have h : ((X : ℂ[X])^3+1) ∣ (X^3)^8-(-1)^8 := by
    simpa using sub_dvd_pow_sub_pow (X^3 : ℂ[X]) (-1) 8
  have hd : N₁ ∣ (X : ℂ[X])^3+1 := ⟨X+1,by unfold N₁; ring⟩
  convert hd.trans h using 1; ring

lemma N₂_factor : T.N₂*T.N₂other = (X : ℂ[X])^4+C (T.a^4) := by
  unfold N₂ N₂other
  have hs : (C (Real.sqrt 2 : ℂ) : ℂ[X])^2=2 := by
    rw [← map_pow,sqrt_two_square]; norm_num [map_ofNat]
  simp only [map_mul,map_pow]
  linear_combination -(C T.a*X)^2*hs

lemma N₂_dvd : T.N₂ ∣ (X : ℂ[X])^24-1 := by
  have h : ((X : ℂ[X])^4+C (T.a^4)) ∣ (X^4)^6-(-C (T.a^4))^6 := by
    simpa only [sub_neg_eq_add] using sub_dvd_pow_sub_pow (X^4 : ℂ[X]) (-C (T.a^4)) 6
  have hh : (-C (T.a^4) : ℂ[X])^6=1 := by
    rw [Even.neg_pow (by decide : Even (6 : ℕ))]
    rw [← map_pow,← pow_mul,show (4*6 : ℕ)=24 by norm_num,T.a_twentyfour,map_one]
  have hd : T.N₂ ∣ (X : ℂ[X])^4+C (T.a^4) := ⟨T.N₂other,T.N₂_factor.symm⟩
  convert hd.trans h using 1
  rw [hh,← pow_mul]

lemma N_coprime : IsCoprime N₁ T.N₂ := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro z
  by_contra! hz
  have h1 : z^2-z+1=0 := by simpa [N₁] using hz.1
  have h2 : z^2+(Real.sqrt 2 : ℂ)*T.a*z+T.a^2=0 := by simpa [N₂] using hz.2
  have hz3 : z^3=-1 := by linear_combination (z+1)*h1
  have hz4 : z^4+T.a^4=0 := by
    linear_combination (z^2-(Real.sqrt 2 : ℂ)*T.a*z+T.a^2)*h2 +
      (T.a*z)^2*sqrt_two_square
  have ha := T.a_cube
  have hza : z = -T.a := by
    linear_combination -hz4+z*(hz3)+T.a*ha
  rw [hza,neg_pow,ha] at hz3
  norm_num at hz3

lemma exists_N_quotient : ∃ Q : ℂ[X], X^24-1=N₁*T.N₂*Q :=
  T.N_coprime.mul_dvd N₁_dvd T.N₂_dvd

def Nquotient : ℂ[X] := T.exists_N_quotient.choose
lemma Nquotient_spec : (X : ℂ[X])^24-1=N₁*T.N₂*T.Nquotient := T.exists_N_quotient.choose_spec

lemma N₁_comp_L : N₁.comp T.L=C T.c*T.P₁ := by
  unfold N₁ L P₁
  simp only [sub_comp,pow_comp,X_comp,add_comp,one_comp]
  have hd := congrArg (C : ℂ →+* ℂ[X]) T.determinant
  simp only [map_mul,map_sub,map_one,map_add] at hd
  simp only [map_sub,map_mul,map_one,map_ofNat]
  linear_combination -hd

lemma N₂_comp_L : T.N₂.comp T.L=C T.c*T.P₂ := by
  unfold N₂ L P₂
  simp only [add_comp,pow_comp,X_comp,mul_comp,C_comp]
  have hd := congrArg (C : ℂ →+* ℂ[X]) T.determinant
  have ht := congrArg (C : ℂ →+* ℂ[X]) T.relative_trace
  simp only [map_mul,map_sub,map_one,map_add,map_pow,map_zero] at hd ht
  simp only [map_sub,map_mul,map_one,map_pow]
  linear_combination (C T.s-C T.c*X)*ht-(C T.a)^2*hd

lemma P_coprime : IsCoprime T.P₁ T.P₂ := by
  have h := T.N_coprime.map (Polynomial.aeval T.L).toRingHom
  have h1 : Polynomial.aeval T.L N₁ = N₁.comp T.L := by simp [aeval_def,comp]
  have h2 : Polynomial.aeval T.L T.N₂ = T.N₂.comp T.L := by simp [aeval_def,comp]
  change IsCoprime (Polynomial.aeval T.L N₁) (Polynomial.aeval T.L T.N₂) at h
  rw [h1,h2,T.N₁_comp_L,T.N₂_comp_L] at h
  exact (h.of_isCoprime_of_dvd_left (dvd_mul_left _ _)).of_isCoprime_of_dvd_right (dvd_mul_left _ _)

lemma J_mod_P₁ : T.J+X*T.L = -T.P₁ := by
  unfold J L P₁
  simp only [map_sub,map_mul,map_one,map_ofNat]
  ring

lemma J_mod_P₂ : C (T.a^2)*T.J+X*T.L = -T.P₂ := by
  unfold J L P₂
  simp only [map_sub,map_mul,map_one,map_pow]
  ring

def graphOne (mixed : Bool) (x y : ℂ) : ℂ := if mixed then x*y-1 else y-x
def graphTwo (mixed : Bool) (x y : ℂ) : ℂ := if mixed then x*y-T.a^2 else y-T.a^2*x
def graphThree (mixed : Bool) (x y : ℂ) : ℂ :=
  if mixed then y*((1-T.s)*x+T.c)-(T.b*x+T.s) else y*(T.c*x+1-T.s)-(T.s*x+T.b)
def betaPolynomial (mixed : Bool) : ℂ[X] := if mixed then T.J else T.L

lemma a_ne_zero : T.a ≠ 0 := by
  intro h
  have hc := T.a_cube
  rw [h] at hc
  norm_num at hc

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open MvPolynomial
noncomputable section
abbrev BPoly := MvPolynomial (Fin 2) ℂ

def affineLinear (a b : ℂ) : BPoly := C a*X 0+C b

lemma affineLinear_regular_variable (a b : ℂ) : (1 : Fin 2) ∉ (affineLinear a b).vars := by
  intro h
  have hf := vars_add_subset (C a*X (0 : Fin 2)) (C b)
  have hg := vars_mul (C a : BPoly) (X 0)
  simp only [vars_C,vars_X,Finset.empty_union] at hg
  simp only [vars_C,Finset.union_empty] at hf
  have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := hg (hf h)
  norm_num at this

lemma affineLinear_ne_zero_of_left {a b : ℂ} (ha : a ≠ 0) : affineLinear a b ≠ 0 := by
  intro he
  have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (0 : ℂ))) he
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℂ))) he
  simp only [affineLinear,map_add,map_mul,eval_C,eval_X,map_zero,mul_zero,zero_add] at h0
  simp only [affineLinear,map_mul,eval_C,eval_X,map_zero,mul_one,h0,add_zero] at h1
  exact ha h1

lemma affineLinear_ne_zero_of_right {a b : ℂ} (hb : b ≠ 0) : affineLinear a b ≠ 0 := by
  intro he
  have h := congrArg (MvPolynomial.eval (fun _ : Fin 2 ↦ (0 : ℂ))) he
  exact hb (by simpa [affineLinear] using h)

lemma determinant_graph_irreducible (p q r s : ℂ) (hd : p*s-q*r ≠ 0)
    (hn : p ≠ 0 ∨ q ≠ 0) :
    Irreducible ((C p*X 0+C q)*X 1+(C r*X 0+C s) : BPoly) := by
  apply MvPolynomial.irreducible_mul_X_add
  · rcases hn with h | h
    · exact affineLinear_ne_zero_of_left h
    · exact affineLinear_ne_zero_of_right h
  · exact affineLinear_regular_variable p q
  · exact affineLinear_regular_variable r s
  · apply IsCoprime.isRelPrime
    refine ⟨C (-r/(p*s-q*r)),C (p/(p*s-q*r)),?_⟩
    have h : (-r/(p*s-q*r))*p+(p/(p*s-q*r))*r=0 := by ring
    have h' : (-r/(p*s-q*r))*q+(p/(p*s-q*r))*s=1 := by
      calc
        _ = (p*s-q*r)/(p*s-q*r) := by ring
        _ = 1 := div_self hd
    calc
      (C (-r/(p*s-q*r)) : BPoly)*(C p*X 0+C q)+C (p/(p*s-q*r))*(C r*X 0+C s)
        = C ((-r/(p*s-q*r))*p+(p/(p*s-q*r))*r)*X 0+
          C ((-r/(p*s-q*r))*q+(p/(p*s-q*r))*s) := by
            simp only [map_add,map_mul]; ring
      _ = 1 := by rw [h,h']; simp

namespace GraphScalars
variable (T : GraphScalars)
def G1 (mixed : Bool) : BPoly := if mixed then X 0*X 1-1 else X 1-X 0
def G2 (mixed : Bool) : BPoly := if mixed then X 0*X 1-C (T.a^2) else X 1-C (T.a^2)*X 0
def G3 (mixed : Bool) : BPoly :=
  if mixed then X 1*(C (1-T.s)*X 0+C T.c)-(C T.b*X 0+C T.s)
  else X 1*(C T.c*X 0+C (1-T.s))-(C T.s*X 0+C T.b)

@[simp] lemma eval_G1 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (G1 mixed)=graphOne mixed x y := by
  cases mixed <;> simp [G1,graphOne]
@[simp] lemma eval_G2 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (T.G2 mixed)=T.graphTwo mixed x y := by
  cases mixed <;> simp [G2,graphTwo]
@[simp] lemma eval_G3 (mixed : Bool) (x y : ℂ) :
    MvPolynomial.eval ![x,y] (T.G3 mixed)=T.graphThree mixed x y := by
  cases mixed <;> simp only [G3,graphThree,Bool.false_eq_true,↓reduceIte,map_sub,map_mul,eval_X,eval_C,map_add,Matrix.cons_val_zero,Matrix.cons_val_one]; ring

lemma G1_irreducible (mixed : Bool) : Irreducible (G1 mixed) := by
  cases mixed
  · convert determinant_graph_irreducible 0 1 (-1) 0 (by norm_num) (by norm_num) using 1;
      simp [G1]; ring
  · convert determinant_graph_irreducible 1 0 0 (-1) (by norm_num) (by norm_num) using 1;
      simp [G1]; ring

lemma G2_irreducible (mixed : Bool) : Irreducible (T.G2 mixed) := by
  cases mixed
  · convert determinant_graph_irreducible 0 1 (-T.a^2) 0
      (by simpa using pow_ne_zero 2 T.a_ne_zero) (by norm_num) using 1;
      simp [G2]; ring
  · convert determinant_graph_irreducible 1 0 0 (-T.a^2)
      (by simpa using pow_ne_zero 2 T.a_ne_zero) (by norm_num) using 1;
      simp [G2]; ring

lemma G3_irreducible (mixed : Bool) : Irreducible (T.G3 mixed) := by
  have hd := T.determinant
  cases mixed
  · have hh : T.c*(-T.b)-(1-T.s)*(-T.s) ≠ 0 := by
      have : T.c*(-T.b)-(1-T.s)*(-T.s)=1 := by linear_combination hd
      rw [this]; norm_num
    convert determinant_graph_irreducible T.c (1-T.s) (-T.s) (-T.b) hh
      (Or.inl T.c_ne_zero) using 1; simp only [G3,Bool.false_eq_true,↓reduceIte,map_neg]; ring
  · have hh : (1-T.s)*(-T.s)-T.c*(-T.b) ≠ 0 := by
      have : (1-T.s)*(-T.s)-T.c*(-T.b)= -1 := by linear_combination -hd
      rw [this]; norm_num
    convert determinant_graph_irreducible (1-T.s) T.c (-T.b) (-T.s) hh
      (Or.inr T.c_ne_zero) using 1; simp only [G3,↓reduceIte,map_neg]; ring

lemma a_square_ne_one : T.a^2 ≠ 1 := by
  intro ha
  have ht := T.relative_trace
  rw [ha] at ht
  have hh : (Real.sqrt 2 : ℂ)*T.a= -1 := by linear_combination ht
  have hs := congrArg (fun z : ℂ ↦ z^2) hh
  rw [mul_pow,sqrt_two_square,ha] at hs
  norm_num at hs

lemma G1_G2_relPrime (mixed : Bool) : IsRelPrime (G1 mixed) (T.G2 mixed) := by
  apply (G1_irreducible mixed).isRelPrime_iff_not_dvd.mpr
  rintro ⟨p,hp⟩
  have he := congrArg (MvPolynomial.eval ![(1:ℂ),1]) hp
  simp only [map_mul,eval_G1,eval_G2] at he
  have hz : graphOne mixed 1 1=0 := by cases mixed <;> norm_num [graphOne]
  have hj : T.graphTwo mixed 1 1=1-T.a^2 := by cases mixed <;> norm_num [graphTwo]
  rw [hz,hj,zero_mul] at he
  exact T.a_square_ne_one (sub_eq_zero.mp he).symm

lemma G1_G3_relPrime (mixed : Bool) : IsRelPrime (G1 mixed) (T.G3 mixed) := by
  cases mixed
  · apply (G1_irreducible false).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),0]) hp
    simp [graphOne,graphThree] at he
    exact T.b_ne_zero he
  · apply IsRelPrime.symm
    apply (T.G3_irreducible true).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),T.s/T.c]) hp
    simp [graphOne,graphThree,T.c_ne_zero] at he

lemma G2_G3_relPrime (mixed : Bool) : IsRelPrime (T.G2 mixed) (T.G3 mixed) := by
  cases mixed
  · apply (T.G2_irreducible false).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),0]) hp
    simp [graphTwo,graphThree] at he
    exact T.b_ne_zero he
  · apply IsRelPrime.symm
    apply (T.G3_irreducible true).isRelPrime_iff_not_dvd.mpr
    rintro ⟨p,hp⟩
    have he := congrArg (MvPolynomial.eval ![(0:ℂ),T.s/T.c]) hp
    simp [graphTwo,graphThree,T.c_ne_zero] at he
    exact T.a_ne_zero he

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix

noncomputable def source_a : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 3)
noncomputable def source_s : ℂ :=
  1 / 2 - Complex.I * (1 + 2 * (Real.sqrt 2 : ℂ)) / (2 * (Real.sqrt 3 : ℂ))
noncomputable def source_A : Matrix (Fin 2) (Fin 2) ℂ := !![source_a, 0; 0, source_a⁻¹]
noncomputable def source_B : Matrix (Fin 2) (Fin 2) ℂ :=
  !![source_s, 1; (Real.sqrt 2 : ℂ) / 3, 1 - source_s]

lemma source_a_eq : source_a = 1 / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  unfold source_a
  rw [show Complex.I * (Real.pi : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

lemma sqrt_two_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma sqrt_three_sq_complex : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

lemma source_a_inv_eq : source_a⁻¹ = 1 / 2 - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  rw [source_a_eq]
  calc
    (1 / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I) *
      (1 / 2 - (Real.sqrt 3 : ℂ) / 2 * Complex.I) =
      1 / 4 - (Real.sqrt 3 : ℂ) ^ 2 * Complex.I ^ 2 / 4 := by ring
    _ = 1 := by rw [sqrt_three_sq_complex, Complex.I_sq]; norm_num

lemma source_a_add_inv : source_a + source_a⁻¹ = 1 := by
  rw [source_a_inv_eq, source_a_eq]
  ring

lemma source_a_ne_zero : source_a ≠ 0 := Complex.exp_ne_zero _

lemma source_a_mul_inv : source_a * source_a⁻¹ = 1 := mul_inv_cancel₀ source_a_ne_zero

lemma source_s_mul_complement : source_s * (1 - source_s) =
    1 + (Real.sqrt 2 : ℂ) / 3 := by
  unfold source_s
  field_simp
  ring_nf
  rw [sqrt_three_sq_complex, sqrt_two_sq_complex, Complex.I_sq]
  ring

open Polynomial
noncomputable section

lemma source_a_square : source_a ^ 2 - source_a + 1 = 0 := by
  have h := congrArg (fun z : ℂ ↦ source_a * z) source_a_add_inv
  rw [mul_add, source_a_mul_inv] at h
  linear_combination h

lemma source_a_cube : source_a ^ 3 = -1 := by
  linear_combination (source_a + 1) * source_a_square

end
end QuadricCounterexample

namespace QuadricCounterexample
noncomputable section

lemma source_graph_trace : source_s+source_a^2*(1-source_s)+
    (Real.sqrt 2 : ℂ)*source_a=0 := by
  have hh : source_a⁻¹*source_s+source_a*(1-source_s)= -(Real.sqrt 2 : ℂ) := by
    rw [source_a_inv_eq,source_a_eq]
    unfold source_s
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have ha := source_a_mul_inv
  linear_combination source_a*hh-source_s*ha

def sourceGraphScalars : GraphScalars where
  a := source_a
  s := source_s
  b := 1
  c := (Real.sqrt 2 : ℂ)/3
  a_cube := source_a_cube
  determinant := by simpa only [one_mul] using source_s_mul_complement
  relative_trace := source_graph_trace
  b_ne_zero := one_ne_zero
  c_ne_zero := div_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))
    (by norm_num)

namespace GraphScalars
variable (T : GraphScalars)

def swapped : GraphScalars where
  a := T.a⁻¹
  s := 1-T.s
  b := T.c
  c := T.b
  a_cube := by rw [inv_pow,T.a_cube]; norm_num
  determinant := by have h:=T.determinant; linear_combination h
  relative_trace := by
    have h:=T.relative_trace
    field_simp [T.a_ne_zero]
    linear_combination h
  b_ne_zero := T.c_ne_zero
  c_ne_zero := T.b_ne_zero

@[simp] lemma swapped_swapped : T.swapped.swapped=T := by
  cases T
  simp [swapped]

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section

def affineRepresentative {R : Type u1} [Zero R] [One R] (i : Fin 2) (z : R) : Fin 2 → R :=
  if i=0 then ![1,z] else ![z,1]

@[simp] lemma affineRepresentative_index {R : Type u2} [Zero R] [One R]
    (i : Fin 2) (z : R) : affineRepresentative i z i=1 := by
  fin_cases i <;> simp [affineRepresentative]

def matrixGraphValue (M : TwoMatrix) (i : StandardChart) (z : BaseCoordinates) : ℂ :=
  let X := affineRepresentative i.1 z.1
  let Y := affineRepresentative i.2 z.2
  Y 0*(M 1 0*X 0+M 1 1*X 1)-Y 1*(M 0 0*X 0+M 0 1*X 1)

def matrixGraphPolynomial (M : TwoMatrix) (i : StandardChart) : BasePolynomial :=
  let x := affineRepresentative i.1 (X 0 : BasePolynomial)
  let y := affineRepresentative i.2 (X 1 : BasePolynomial)
  y 0*(C (M 1 0)*x 0+C (M 1 1)*x 1)-y 1*(C (M 0 0)*x 0+C (M 0 1)*x 1)

@[simp] lemma baseEval_matrixGraphPolynomial (M : TwoMatrix) (i : StandardChart)
    (z : BaseCoordinates) : baseEval (matrixGraphPolynomial M i) z=matrixGraphValue M i z := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [baseEval,matrixGraphPolynomial,matrixGraphValue,affineRepresentative]

namespace GraphScalars
variable (T : GraphScalars)

def matrices (k : Fin 3) : TwoMatrix :=
  ![(1 : TwoMatrix),!![T.a,0;0,T.a⁻¹],!![T.s,T.b;T.c,1-T.s]] k

end GraphScalars
end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix MvPolynomial
noncomputable section
namespace GraphScalars
variable (T : GraphScalars)

def branchGraph (k : Fin 3) (mixed : Bool) (x y : ℂ) : ℂ :=
  ![graphOne mixed x y,T.graphTwo mixed x y,T.graphThree mixed x y] k

@[simp] lemma baseEval_pow (p : BasePolynomial) (n : ℕ) (z : BaseCoordinates) :
    baseEval (p^n) z=baseEval p z^n := map_pow (MvPolynomial.eval _) _ _

end GraphScalars

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Plurisubharmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise

attribute [local instance] Measure.Subtype.measureSpace

attribute [local instance] OAI.QuadricCounterexample.realDualComplexGroup
attribute [local instance] OAI.QuadricCounterexample.realDualComplexSpace
lemma hessian_comp_apply {X : Type u3} {Y : Type u4} {Z : Type u5}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {g : Y → Z} {x : X}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) (v w : X) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x v w =
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) +
        fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hg2 := (hg.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ g (f y)).comp (fderiv ℝ f y)) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt.eventually (hg.eventually (by norm_num))] with y hy hy'
    exact fderiv_comp y (hy'.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  have hc := (hg2.hasFDerivAt.comp x hf1.hasFDerivAt).clm_comp hf2.hasFDerivAt
  dsimp only [Function.comp_def] at hc
  rw [he.fderiv_eq,hc.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma holomorphic_real_hessian_trace {E : Type u6} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] {γ : ℂ → E} {z : ℂ} (hγ : AnalyticAt ℂ γ z) :
    fderiv ℝ (fderiv ℝ γ) z 1 1 +
      fderiv ℝ (fderiv ℝ γ) z Complex.I Complex.I = 0 := by
  have hh := hγ.harmonicAt.2.self_of_nhds
  simpa only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.empty_val',Pi.zero_apply] using hh

lemma holomorphic_real_derivative_I {E : Type u7} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    {γ : ℂ → E} {z : ℂ} (hγ : DifferentiableAt ℂ γ z) :
    fderiv ℝ γ z Complex.I = Complex.I • fderiv ℝ γ z 1 := by
  rw [hγ.fderiv_restrictScalars ℝ]
  change fderiv ℂ γ z Complex.I = Complex.I • fderiv ℂ γ z 1
  rw [← map_smul]
  simp

def leviTrace {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : E → ℝ) (x v : E) : ℝ :=
  fderiv ℝ (fderiv ℝ q) x v v +
    fderiv ℝ (fderiv ℝ q) x (Complex.I • v) (Complex.I • v)

lemma holomorphic_disk_hessian_trace {E : Type u9} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] {γ : ℂ → E} {q : E → ℝ} {z : ℂ}
    (hγ : AnalyticAt ℂ γ z) (hq : ContDiffAt ℝ 2 q (γ z)) :
    fderiv ℝ (fderiv ℝ (q ∘ γ)) z 1 1 +
      fderiv ℝ (fderiv ℝ (q ∘ γ)) z Complex.I Complex.I =
        leviTrace q (γ z) (fderiv ℝ γ z 1) := by
  have hc : ContDiffAt ℝ 2 γ z := hγ.contDiffAt.restrict_scalars ℝ
  rw [hessian_comp_apply hc hq,hessian_comp_apply hc hq]
  rw [holomorphic_real_derivative_I hγ.differentiableAt]
  have hh := holomorphic_real_hessian_trace hγ
  have he := congrArg (fderiv ℝ q (γ z)) hh
  rw [map_add,map_zero] at he
  unfold leviTrace
  linarith

theorem DiskPshOn.of_C2_leviTrace_nonneg {E : Type u11} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set E} {q : E → ℝ}
    (hΩ : IsOpen Ω) (hq : ContDiffOn ℝ 2 q Ω)
    (hlevi : ∀ x∈Ω, ∀ v : E, 0≤leviTrace q x v) : DiskPshOn Ω q := by
  refine ⟨hq.continuousOn.upperSemicontinuousOn, ?_⟩
  intro D hD γ hγ hmap
  have ha : ∀ z∈D, AnalyticAt ℂ γ z := fun z hz ↦
    hγ.analyticOnNhd hD z hz
  apply DiskSubharmonicOn.of_C2_laplacian_nonneg hD
  · intro z hz
    exact ((hq.contDiffAt (hΩ.mem_nhds (hmap hz))).comp z
      ((ha z hz).contDiffAt.restrict_scalars ℝ)).contDiffWithinAt
  · intro z hz
    change 0≤fderiv ℝ (fderiv ℝ (q ∘ γ)) z 1 1 +
      fderiv ℝ (fderiv ℝ (q ∘ γ)) z Complex.I Complex.I
    rw [holomorphic_disk_hessian_trace (ha z hz) (hq.contDiffAt (hΩ.mem_nhds (hmap hz)))]
    exact hlevi (γ z) (hmap hz) _

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.RootTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section

lemma DiskPshOn.sum {E : Type u9} {ι : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (s : Finset ι) (q : ι → E → ℝ) (hq : ∀ i ∈ s, DiskPshOn U (q i)) :
    DiskPshOn U (fun x ↦ ∑ i ∈ s, q i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using diskPshOn_const U 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hq i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ hq j (Finset.mem_insert_of_mem hj)))

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
open Matrix
open scoped ComplexOrder

noncomputable def quadraticValue {n : Type u1} [Fintype n]
    (H : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (H *ᵥ v)).re

lemma basis_pair {n : Type u3} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ (H *ᵥ Pi.single j 1) = H i j := by
  simp [single_dotProduct]

lemma quadraticValue_basis {n : Type u4} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i : n) : quadraticValue H (Pi.single i 1) = (H i i).re := by
  rw [quadraticValue, basis_pair]

lemma quadraticValue_add_basis {n : Type u5} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    quadraticValue H (Pi.single i 1 + Pi.single j 1) =
      (H i i).re + (H i j).re + (H j i).re + (H j j).re := by
  simp only [quadraticValue, star_add, mulVec_add, add_dotProduct, dotProduct_add,
    basis_pair, Complex.add_re]
  ring

lemma quadraticValue_add_I_basis {n : Type u6} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (i j : n) :
    quadraticValue H (Pi.single i 1 + Complex.I • Pi.single j 1) =
      (H i i).re - (H i j).im + (H j i).im + (H j j).re := by
  simp only [quadraticValue, star_add, star_smul, mulVec_add, mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, basis_pair,
    smul_eq_mul, Complex.star_def, Complex.conj_I, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.neg_re,
    Complex.I_im, Complex.I_re]
  ring

noncomputable def matrixFromQuadratic {n : Type u7} [DecidableEq n]
    (q : (n → ℂ) → ℝ) : Matrix n n ℂ := fun i j ↦
  ⟨(q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1) - q (Pi.single j 1)) / 2,
   (q (Pi.single i 1) + q (Pi.single j 1) -
     q (Pi.single i 1 + Complex.I • Pi.single j 1)) / 2⟩

lemma matrixFromQuadratic_value {n : Type u8} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    matrixFromQuadratic (quadraticValue H) = H := by
  funext i j
  apply Complex.ext
  all_goals
    have hre := congrArg Complex.re (hH.apply i j)
    have him := congrArg Complex.im (hH.apply i j)
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hre him
    simp only [matrixFromQuadratic, quadraticValue_add_basis, quadraticValue_add_I_basis,
      quadraticValue_basis]
    linarith

local instance matrixContinuousENorm_r467536_1 {n : Type u12} [Fintype n] :
    ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))
noncomputable def quadraticValueCLM {n : Type u13} [Fintype n]
    (v : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ where
  toFun H := quadraticValue H v
  map_add' H K := by
    simp only [quadraticValue, add_mulVec, dotProduct_add, Complex.add_re]
  map_smul' a H := by
    simp [quadraticValue, smul_mulVec, dotProduct_smul, RCLike.real_smul_eq_coe_mul]
  cont := by unfold quadraticValue; fun_prop

lemma quadraticValue_nonneg {n : Type u18} [Fintype n]
    {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) : 0 ≤ quadraticValue H v :=
  (hH.dotProduct_mulVec_nonneg v).1

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

theorem DiskPshOn.base_submean
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {q : ℂ × ℂ → ℝ}
    (hq : DiskPshOn Ω q) {x : ℂ × ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hb : closedBall x r ⊆ Ω) (hi : IntegrableOn q (ball x r)) :
    (volume (ball x r)).toReal * q x ≤ ∫ y in ball x r, q y := by
  have hprod : Integrable q
      ((volume.restrict (ball x.1 r)).prod (volume.restrict (ball x.2 r))) := by
    rw [Measure.prod_restrict, ball_prod_same]
    exact hi
  have h1 : DiskSubharmonicOn ((fun z : ℂ ↦ (z,x.2)) ⁻¹' Ω)
      (fun z ↦ q (z,x.2)) :=
    hq.2 _ (hΩ.preimage (by fun_prop)) _ (by fun_prop) (fun _ h ↦ h)
  have hb1 : closedBall x.1 r ⊆ (fun z : ℂ ↦ (z,x.2)) ⁻¹' Ω := by
    intro z hz
    apply hb
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_le_iff] using
      And.intro (show dist z x.1 ≤ r from hz) hr.le
  have hs1 := h1.2 x.1 hx r hr hb1
  have h2 (z : ℂ) (hz : z ∈ ball x.1 r) :
      (volume (ball x.2 r)).toReal * q (z,x.2) ≤ ∫ w in ball x.2 r, q (z,w) := by
    have hh : DiskSubharmonicOn ((fun w : ℂ ↦ (z,w)) ⁻¹' Ω) (fun w ↦ q (z,w)) :=
      hq.2 _ (hΩ.preimage (by fun_prop)) _ (by fun_prop) (fun _ h ↦ h)
    have hbs : closedBall x.2 r ⊆ (fun w : ℂ ↦ (z,w)) ⁻¹' Ω := by
      intro w hw
      apply hb
      simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
        And.intro (le_of_lt (show dist z x.1 < r from hz)) (show dist w x.2 ≤ r from hw)
    exact (hh.2 x.2 (hbs (mem_closedBall_self hr.le)) r hr hbs).2
  have hmeasure : (volume (ball x r)).toReal =
      (volume (ball x.1 r)).toReal * (volume (ball x.2 r)).toReal := by
    rw [← ball_prod_same]
    change ((volume.prod volume) (ball x.1 r ×ˢ ball x.2 r)).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  rw [hmeasure]
  calc
    (volume (ball x.1 r)).toReal * (volume (ball x.2 r)).toReal * q x =
        (volume (ball x.2 r)).toReal * ((volume (ball x.1 r)).toReal * q x) := by ring
    _ ≤ (volume (ball x.2 r)).toReal * (∫ z in ball x.1 r, q (z,x.2)) :=
      mul_le_mul_of_nonneg_left hs1.2 ENNReal.toReal_nonneg
    _ = ∫ z in ball x.1 r, (volume (ball x.2 r)).toReal * q (z,x.2) :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ z in ball x.1 r, ∫ w in ball x.2 r, q (z,w) :=
      integral_mono_ae (hs1.1.const_mul _) hprod.integral_prod_left
        ((ae_restrict_mem measurableSet_ball).mono h2)
    _ = ∫ y in ball x r, q y := by
      rw [← integral_prod q hprod, Measure.prod_restrict, ball_prod_same]
      rfl

end QuadricCounterexample

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

noncomputable def coefficientsToMatrix {n : Type u22} [Fintype n] :
    EuclideanSpace ℂ (n × n) →ₗ[ℂ] Matrix n n ℂ where
  toFun v i j := v (i,j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma DiskPshOn.base_average_submean
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {q : ℂ × ℂ → ℝ}
    (hq : DiskPshOn Ω q) {x : ℂ × ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hb : closedBall x r ⊆ Ω) (hi : IntegrableOn q (ball x r)) :
    q x ≤ ⨍ y in ball x r, q y := by
  have hm : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume x hr)) measure_ball_lt_top.ne
  rw [setAverage_eq, smul_eq_mul, measureReal_def, ← div_eq_inv_mul, le_div_iff₀ hm]
  simpa only [mul_comm] using hq.base_submean hΩ hx hr hb hi

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance instContinuousENormMatrixComplexOfFintype_solutions_2_r467536_1 {n : Type u13} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))
noncomputable def matrixToCoefficients {n : Type u14} [Fintype n] :
    Matrix n n ℂ →ₗ[ℂ] EuclideanSpace ℂ (n × n) where
  toFun H := WithLp.toLp 2 (fun ij ↦ H ij.1 ij.2)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def standardChartIndex (i : StandardChart) : ℕ := (standardChartNat_surj i).choose
lemma standardChartIndex_lt (i : StandardChart) : standardChartIndex i<4 :=
  (standardChartNat_surj i).choose_spec.1
@[simp] lemma standardChartNat_index (i : StandardChart) :
    standardChartNat (standardChartIndex i)=i := (standardChartNat_surj i).choose_spec.2

lemma EqualizerData.twist_coordinateDomain (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).coordinateDomain (standardChartIndex i)=univ := by
  ext z
  simp [AlgebraicRankTwoBundle.coordinateDomain,powerPullbackTwist,EqualizerData.bundle,
    standardEquationNat,standardChartIndex_lt,baseEval_pullback]

lemma EqualizerData.twist_chart (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).chart (standardChartIndex i)=i :=
  standardChartNat_index i

lemma EqualizerData.twist_domain (D : EqualizerData) (m : ℕ) (hm : 0 < m)
    (i : StandardChart) :
    (powerPullbackTwist D.bundle m hm).domain (standardChartIndex i)=range (affineQuadric i) := by
  ext x
  simp [AlgebraicRankTwoBundle.domain,powerPullbackTwist,EqualizerData.bundle,
    standardEquationNat,standardChartIndex_lt,principalChart,baseEval_pullback]

section Trace
variable (m : ℕ) [NeZero m]

local instance instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_3_r467536_1 : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _
lemma polarizationTransition_affine (i j : StandardChart) (x : BaseCoordinates) :
    polarizationTransition i j (affineQuadric i x)=firstFactor i j x*secondFactor i j x := by
  simp only [polarizationTransition,hyperplaneTransition,affineQuadric,coordP1_affine,
    firstFactor,secondFactor,scalarFactor]

lemma quadraticValue_congruence (A H : TwoMatrix) (v : FiberCoordinates) :
    quadraticValue (A.conjTranspose*H*A) v=quadraticValue H (A.mulVec v) := by
  simp only [quadraticValue,star_mulVec,dotProduct_mulVec,vecMul_vecMul]

def traceScalar (i j : StandardChart) (z : BaseCoordinates) : ℝ :=
  ‖polarizationTransition i j (affineQuadric i z)‖ ^ (2/(m : ℝ))

end Trace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

structure TwistedPshForm (D : EqualizerData) (m : ℕ) where
  matrix : StandardChart → BaseCoordinates → TwoMatrix
  continuous : ∀ i, Continuous (matrix i)
  positive : ∀ i z, (matrix i z).PosDef
  psh : ∀ i, DiskPshOn univ (fun p : BaseCoordinates × FiberCoordinates ↦
    quadraticValue (matrix i p.1) p.2)
  compatible : ∀ i j z, z ∈ coordinateOverlap i j → ∀ v,
    quadraticValue (matrix i z) v = traceScalar m i j z *
      quadraticValue (matrix j (coordinateChange i j z))
        ((D.coordinateTransition i j z).transpose.mulVec v)

namespace TwistedPshForm
variable {D : EqualizerData} {m : ℕ}
def value (P : TwistedPshForm D m) (i : StandardChart)
    (p : BaseCoordinates × FiberCoordinates) : ℝ := quadraticValue (P.matrix i p.1) p.2

lemma value_continuous (P : TwistedPshForm D m) (i : StandardChart) : Continuous (P.value i) := by
  unfold value quadraticValue
  have hc := P.continuous i
  fun_prop

lemma value_nonneg (P : TwistedPshForm D m) (i : StandardChart)
    (z : BaseCoordinates) (v : FiberCoordinates) : 0 ≤ P.value i (z,v) :=
  quadraticValue_nonneg (P.positive i z).posSemidef v

def rescale (P : TwistedPshForm D m) (c : ℝ) (hc : 0<c) : TwistedPshForm D m where
  matrix i z := c • P.matrix i z
  continuous i := by
    have hi := P.continuous i
    fun_prop
  positive i z := (P.positive i z).smul hc
  psh i := by
    have he (p : BaseCoordinates × FiberCoordinates) :
        quadraticValue (c • P.matrix i p.1) p.2 = c*P.value i p := by
      change (quadraticValueCLM p.2) (c • P.matrix i p.1)=_
      rw [map_smul]; rfl
    simp_rw [he]
    exact (P.psh i).const_mul_of_continuous (P.value_continuous i).continuousOn hc.le
  compatible i j z hz v := by
    have he (H : TwoMatrix) (w : FiberCoordinates) :
        quadraticValue (c • H) w = c*quadraticValue H w := by
      change (quadraticValueCLM w) (c • H)=_
      rw [map_smul]; rfl
    rw [he,he,P.compatible i j z hz v]
    ring

@[simp] lemma value_rescale (P : TwistedPshForm D m) (c : ℝ) (hc : 0<c)
    (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) :
    (P.rescale c hc).value i p=c*P.value i p := by
  change (quadraticValueCLM p.2) (c • P.matrix i p.1)=_
  rw [map_smul]; rfl

end TwistedPshForm

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma norm_transpose_mulVec_le (A : TwoMatrix) (v : FiberCoordinates) :
    ‖A.transpose.mulVec v‖ ≤ 2*‖A‖*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hA (j : Fin 2) : ‖A j i‖≤‖A‖ := (norm_le_pi_norm (A j) i).trans (norm_le_pi_norm A j)
  have hv (j : Fin 2) : ‖v j‖≤‖v‖ := norm_le_pi_norm v j
  simp only [Matrix.mulVec, dotProduct,Fin.sum_univ_two,Matrix.transpose_apply]
  calc
    ‖A 0 i*v 0+A 1 i*v 1‖ ≤ ‖A 0 i*v 0‖+‖A 1 i*v 1‖ := norm_add_le _ _
    _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul (hA 0) (hv 0) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (hA 1) (hv 1) (norm_nonneg _) (norm_nonneg _))
    _ = 2*‖A‖*‖v‖ := by ring

lemma traceScalar_le (m : ℕ) (hm : 0 < m) (i j : StandardChart) (z : BaseCoordinates) :
    traceScalar m i j z ≤ 1+‖polarizationTransition i j (affineQuadric i z)‖^2 := by
  unfold traceScalar
  have hm' : (1:ℝ)≤ m := by exact_mod_cast hm
  by_cases hg : 1≤‖polarizationTransition i j (affineQuadric i z)‖
  · have he : 2/(m:ℝ)≤2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have hh := Real.rpow_le_rpow_of_exponent_le hg he
    rw [Real.rpow_two] at hh
    linarith
  · exact (Real.rpow_le_one (norm_nonneg _) (le_of_not_ge hg) (by positivity)).trans
      (by nlinarith [sq_nonneg ‖polarizationTransition i j (affineQuadric i z)‖])

lemma EqualizerData.coordinateTransition_continuousOn (D : EqualizerData) (i j : StandardChart) :
    ContinuousOn (D.coordinateTransition i j) (coordinateOverlap i j) := by
  apply continuousOn_pi.mpr; intro a
  apply continuousOn_pi.mpr; intro b
  exact ((D.coordinateTransition_regular i j a b).regular.analyticOnNhd
    (coordinateOverlap_open i j)).continuousOn

def switchRegion (R : ℝ) (i j : StandardChart) : Set BaseCoordinates :=
  closedBall 0 R ∩ {z | (i.1=j.1 ∨ 1≤‖z.1‖) ∧ (i.2=j.2 ∨ 1≤‖z.2‖)}

lemma switchRegion_compact (R : ℝ) (i j : StandardChart) : IsCompact (switchRegion R i j) := by
  have hc1 : IsClosed {z : BaseCoordinates | 1≤‖z.1‖} :=
    isClosed_le continuous_const (by fun_prop)
  have hc2 : IsClosed {z : BaseCoordinates | 1≤‖z.2‖} :=
    isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {z : BaseCoordinates | i.1=j.1 ∨ 1≤‖z.1‖} := by
    by_cases h : i.1=j.1
    · simp [h]
    · simpa [h] using hc1
  have h2 : IsClosed {z : BaseCoordinates | i.2=j.2 ∨ 1≤‖z.2‖} := by
    by_cases h : i.2=j.2
    · simp [h]
    · simpa [h] using hc2
  exact (isCompact_closedBall _ _).inter_right (h1.inter h2)

lemma switchRegion_subset (R : ℝ) (i j : StandardChart) :
    switchRegion R i j ⊆ coordinateOverlap i j := by
  intro z hz
  apply (coordinateOverlap_iff i j z).mpr
  exact ⟨hz.2.1.imp_right (fun h ↦ norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one h)),
    hz.2.2.imp_right (fun h ↦ norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one h))⟩

lemma exists_unit_coordinateChange (i : StandardChart) (z : BaseCoordinates) (R : ℝ) (hR : ‖z‖≤R) :
    ∃ j, z∈switchRegion R i j ∧ ‖coordinateChange i j z‖≤1 := by
  have hs (a : Fin 2) (w : ℂ) :
      ∃ b : Fin 2, (a=b ∨ 1≤‖w‖) ∧ ‖scalarCoordinateChange a b w‖≤1 := by
    by_cases hw : ‖w‖≤1
    · exact ⟨a,Or.inl rfl,by simpa only [scalarCoordinateChange_self] using hw⟩
    · have ha : a≠1-a := by fin_cases a <;> decide
      refine ⟨1-a,Or.inr (le_of_not_ge hw),?_⟩
      simp only [scalarCoordinateChange,ite_eq_right ha,norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_not_ge hw)
  obtain ⟨j₁,h₁,b₁⟩ := hs i.1 z.1
  obtain ⟨j₂,h₂,b₂⟩ := hs i.2 z.2
  refine ⟨(j₁,j₂),⟨by simpa only [mem_closedBall,dist_zero_right] using hR,h₁,h₂⟩,?_⟩
  exact max_le b₁ b₂

lemma TwistedPshForm.local_bound (D : EqualizerData) (i : StandardChart) (R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ m, 0 < m → ∀ P : TwistedPshForm D m,
      (∀ j z, ‖z‖≤1 → ∀ v, P.value j (z,v)≤‖v‖^2) →
      ∀ z, ‖z‖≤R → ∀ v, P.value i (z,v)≤C*‖v‖^2 := by
  let F (j : StandardChart) (z : BaseCoordinates) : ℝ :=
    (1+‖polarizationTransition i j (affineQuadric i z)‖^2)*(2*‖D.coordinateTransition i j z‖)^2
  have hc (j : StandardChart) : ContinuousOn (F j) (switchRegion R i j) := by
    have hT := (D.coordinateTransition_continuousOn i j).mono (switchRegion_subset R i j)
    have hg : Continuous (fun z ↦ polarizationTransition i j (affineQuadric i z)) := by
      simp_rw [polarizationTransition_polynomial]
      exact continuousOn_univ.mp (analytic_baseEval _).continuousOn
    exact (continuousOn_const.add (hg.norm.continuousOn.pow 2)).mul
      ((continuousOn_const.mul hT.norm).pow 2)
  choose B hB using fun j ↦ (switchRegion_compact R i j).exists_bound_of_continuousOn (hc j)
  let C : ℝ := ∑ j : StandardChart, |B j|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨C,hC,?_⟩
  intro m hm P hP z hz v
  obtain ⟨j,hzj,hsmall⟩ := exists_unit_coordinateChange i z R hz
  have hcov := P.compatible i j z (switchRegion_subset R i j hzj) v
  have hq := hP j (coordinateChange i j z) hsmall ((D.coordinateTransition i j z).transpose.mulVec v)
  have hs : 0≤traceScalar m i j z := Real.rpow_nonneg (norm_nonneg _) _
  have hbound : F j z≤C := calc
    F j z ≤ ‖F j z‖ := le_abs_self _
    _ ≤ B j := hB j z hzj
    _ ≤ |B j| := le_abs_self _
    _ ≤ C := by
      change |B j|≤ ∑ k : StandardChart, |B k|
      exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (B k)) (Finset.mem_univ j)
  calc
    P.value i (z,v) = traceScalar m i j z *
      P.value j (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v) := hcov
    _ ≤ traceScalar m i j z * ‖(D.coordinateTransition i j z).transpose.mulVec v‖^2 :=
      mul_le_mul_of_nonneg_left hq hs
    _ ≤ (1+‖polarizationTransition i j (affineQuadric i z)‖^2) *
      (2*‖D.coordinateTransition i j z‖*‖v‖)^2 := by
      apply mul_le_mul (traceScalar_le m hm i j z) _ (sq_nonneg _) (by positivity)
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (norm_transpose_mulVec_le _ _)
    _ = F j z*‖v‖^2 := by dsimp [F]; ring
    _ ≤ C*‖v‖^2 := mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

local instance instPseudoMetrizableSpaceTwoMatrix_r467536_1 : TopologicalSpace.PseudoMetrizableSpace TwoMatrix :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
abbrev TraceIndex := StandardChart × ℕ
abbrev CoefficientSpace := EuclideanSpace ℂ (Fin 2 × Fin 2)
abbrev CoefficientL2 := Lp CoefficientSpace 2 (volume : Measure BaseCoordinates)
def traceInterior (a : TraceIndex) : Set BaseCoordinates := ball 0 ((a.2:ℝ)+2)
def traceDomain (a : TraceIndex) : Set BaseCoordinates := ball 0 ((a.2:ℝ)+3)
def traceSupport (a : TraceIndex) : Set BaseCoordinates := closedBall 0 ((a.2:ℝ)+4)
def traceBound (D : EqualizerData) (a : TraceIndex) : ℝ :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose
lemma traceBound_nonneg (D : EqualizerData) (a : TraceIndex) : 0≤traceBound D a :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose_spec.1

def cutoffTrace {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m) (a : TraceIndex) :
    BaseCoordinates → TwoMatrix := (traceSupport a).indicator (P.matrix a.1)

lemma cutoffTrace_eq {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m) (a : TraceIndex)
    {z : BaseCoordinates} (hz : z∈traceSupport a) : cutoffTrace P a z=P.matrix a.1 z :=
  indicator_of_mem hz _
lemma traceDomain_subset_support (a : TraceIndex) : traceDomain a ⊆ traceSupport a :=
  ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
lemma traceInterior_subset_domain (a : TraceIndex) : traceInterior a ⊆ traceDomain a :=
  ball_subset_ball (by linarith)

structure ExtractedTrace {D : EqualizerData} (ex : ℕ → ℕ) (P : ∀ k, TwistedPshForm D (ex k)) where
  matrix : TraceIndex → BaseCoordinates → TwoMatrix
  f : ℕ → TraceIndex → CoefficientL2
  w : TraceIndex → CoefficientL2
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  coefficients : ∀ k a, (fun x ↦ coefficientsToMatrix (f k a x)) =ᵐ[volume] cutoffTrace (P k) a
  bound : ∀ k a, ∀ᵐ x ∂volume, ‖f k a x‖≤8*traceBound D a ∧
    (x∉traceSupport a → f k a x=0)
  representative : ∀ a, matrix a =ᵐ[volume.restrict (traceInterior a)]
    fun x ↦ coefficientsToMatrix (w a x)
  weak : ∀ a v, Tendsto (fun k ↦ inner ℂ (f (subsequence k) a) v) atTop (𝓝 (inner ℂ (w a) v))
  positive : ∀ a x, x∈traceInterior a → (matrix a x).PosSemidef
  psh : ∀ a, DiskPshOn (traceInterior a ×ˢ univ)
    (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (matrix a p.1) p.2)
  averages : ∀ a x r v, ball x r ⊆ traceInterior a →
    Tendsto (fun k ↦ ⨍ y in ball x r, quadraticValue (cutoffTrace (P (subsequence k)) a y) v)
      atTop (𝓝 (⨍ y in ball x r, quadraticValue (matrix a y) v))

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.PointwiseRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
noncomputable section

local instance instIsAddHaarMeasureProdComplexVolume_solutions_4_r467536_1 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
lemma upperSemicontinuousOn_aestronglyMeasurable {E : Type u1}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} (hΩ : MeasurableSet Ω) {q : E → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (μ : Measure E) :
    AEStronglyMeasurable q (μ.restrict Ω) :=
  (aemeasurable_restrict_of_measurable_subtype hΩ
    (upperSemicontinuousOn_iff_restrict.mpr hq).measurable).aestronglyMeasurable

lemma DiskPshOn.le_of_ae {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q)
    (hr : UpperSemicontinuousOn r Ω) (hpos : ∀ x∈Ω, 0≤q x)
    (hae : q ≤ᵐ[volume.restrict Ω] r) : ∀ x∈Ω, q x≤r x := by
  intro x hx
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hrx : UpperSemicontinuousAt r x := by
    intro b hb
    simpa only [hΩ.nhdsWithin_eq hx] using hr x hx b hb
  have hevent : {y | r y<c} ∩ Ω ∈ 𝓝 x :=
    inter_mem (hrx c hc) (hΩ.mem_nhds hx)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hcb : closedBall x (R/2) ⊆ Ω := by
    intro y hy
    exact (hball (lt_of_le_of_lt (show dist y x≤R/2 from hy) (by linarith))).2
  have hbc : ∀ y∈ball x (R/2), r y≤c := by
    intro y hy
    exact (hball (lt_trans (show dist y x<R/2 from hy) (by linarith))).1.le
  have hBΩ : ball x (R/2) ⊆ Ω := ball_subset_closedBall.trans hcb
  have hmeas : AEStronglyMeasurable q (volume.restrict (ball x (R/2))) :=
    (upperSemicontinuousOn_aestronglyMeasurable hΩ.measurableSet hq.1 volume).mono_measure
      (Measure.restrict_mono hBΩ le_rfl)
  have hle : q ≤ᵐ[volume.restrict (ball x (R/2))] fun _ ↦ c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBΩ hae,
      ae_restrict_mem measurableSet_ball] with y he hy
    exact he.trans (hbc y hy)
  have hnorm : ∀ᵐ y ∂volume.restrict (ball x (R/2)), ‖q y‖≤c := by
    filter_upwards [hle,ae_restrict_mem measurableSet_ball] with y he hy
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos y (hBΩ hy))] using he
  have hconst : IntegrableOn (fun _ : ℂ × ℂ ↦ c) (ball x (R/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hi : IntegrableOn q (ball x (R/2)) := hconst.mono' hmeas hnorm
  have hm : 0 < (volume (ball x (R/2))).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x (by linarith)).ne' measure_ball_lt_top.ne
  have hsub := hq.base_submean hΩ hx (show 0<R/2 by linarith) hcb hi
  have hu := integral_mono_ae hi hconst hle
  simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hu
  exact (mul_le_mul_iff_right₀ hm).mp (hsub.trans hu)

lemma DiskPshOn.eqOn_of_ae {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (hae : q =ᵐ[volume.restrict Ω] r) : EqOn q r Ω := by
  intro x hx
  exact le_antisymm (hq.le_of_ae hΩ hr.1 hqpos (hae.mono fun _ h ↦ h.le) x hx)
    (hr.le_of_ae hΩ hq.1 hrpos (hae.mono fun _ h ↦ h.ge) x hx)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

local instance instIsAddHaarMeasureProdComplexVolume_solutions_5_r467536_1 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
lemma UpperSemicontinuousOn.integrableOn_compact_nonneg {E : Type u2}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {Ω K : Set E} (hΩ : MeasurableSet Ω) {q : E → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (hK : IsCompact K) (hKmeas : MeasurableSet K)
    (hKΩ : K ⊆ Ω) (hpos : ∀ x∈K, 0≤q x) : IntegrableOn q K μ := by
  obtain ⟨C,hC⟩ := (hq.mono hKΩ).bddAbove_of_isCompact hK
  have hm := (upperSemicontinuousOn_aestronglyMeasurable hΩ hq μ).mono_measure
    (Measure.restrict_mono hKΩ le_rfl)
  have hc : IntegrableOn (fun _ : E ↦ C) K μ := integrableOn_const hK.measure_ne_top
  apply hc.mono' hm
  filter_upwards [ae_restrict_mem hKmeas] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos x hx)] using hC (mem_image_of_mem q hx)

lemma DiskPshOn.integrableOn_ball_nonneg {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hpos : ∀ x∈Ω, 0≤q x)
    {x : ℂ × ℂ} {r : ℝ} (hb : closedBall x r ⊆ Ω) : IntegrableOn q (ball x r) :=
  (UpperSemicontinuousOn.integrableOn_compact_nonneg hΩ.measurableSet hq.1 (isCompact_closedBall _ _) measurableSet_closedBall
    hb (fun x hx ↦ hpos x (hb hx))).mono_set ball_subset_closedBall

lemma DiskPshOn.le_of_averages {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (havg : ∀ x ρ, 0<ρ → closedBall x ρ ⊆ Ω →
      (⨍ y in ball x ρ, q y) ≤ ⨍ y in ball x ρ, r y) : ∀ x∈Ω, q x≤r x := by
  intro x hx
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hrx : UpperSemicontinuousAt r x := by
    intro b hb
    simpa only [hΩ.nhdsWithin_eq hx] using hr.1 x hx b hb
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hrx c hc) (hΩ.mem_nhds hx))
  have hcb : closedBall x (R/2) ⊆ Ω := by
    intro y hy
    exact (hball (lt_of_le_of_lt (show dist y x≤R/2 from hy) (by linarith))).2
  have hbc : ∀ y∈ball x (R/2), r y≤c := by
    intro y hy
    exact (hball (lt_trans (show dist y x<R/2 from hy) (by linarith))).1.le
  have hi := hr.integrableOn_ball_nonneg hΩ hrpos hcb
  have hconst : IntegrableOn (fun _ : ℂ × ℂ ↦ c) (ball x (R/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hu := integral_mono_ae hi hconst ((ae_restrict_mem measurableSet_ball).mono hbc)
  have hm : 0 < (volume (ball x (R/2))).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x (by linarith)).ne' measure_ball_lt_top.ne
  have hsub := hq.base_average_submean hΩ hx (show 0<R/2 by linarith) hcb
    (hq.integrableOn_ball_nonneg hΩ hqpos hcb)
  have hav := havg x (R/2) (by linarith) hcb
  apply (hsub.trans hav).trans
  rw [setAverage_eq,smul_eq_mul,measureReal_def,← div_eq_inv_mul,div_le_iff₀ hm]
  simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hu

lemma DiskPshOn.eqOn_of_averages {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (havg : ∀ x ρ, 0<ρ → closedBall x ρ ⊆ Ω →
      (⨍ y in ball x ρ, q y) = ⨍ y in ball x ρ, r y) : EqOn q r Ω := by
  intro x hx
  exact le_antisymm
    (hq.le_of_averages hΩ hr hqpos hrpos (fun x r hr hb ↦ (havg x r hr hb).le) x hx)
    (hr.le_of_averages hΩ hq hrpos hqpos (fun x r hr hb ↦ (havg x r hr hb).ge) x hx)

namespace ExtractedTrace
local instance instIsAddHaarMeasureProdComplexVolume_solutions_5_r467536_2 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
  (X : ExtractedTrace ex P)
def value (a : TraceIndex) (p : BaseCoordinates × FiberCoordinates) : ℝ :=
  quadraticValue (X.matrix a p.1) p.2
lemma base_psh (a : TraceIndex) (v : FiberCoordinates) :
    DiskPshOn (traceInterior a) (fun x ↦ X.value a (x,v)) :=
  (X.psh a).comp (by fun_prop) (fun _ hx ↦ ⟨hx,mem_univ _⟩)
lemma value_nonneg (a : TraceIndex) {x : BaseCoordinates} (hx : x∈traceInterior a) (v : FiberCoordinates) :
    0≤X.value a (x,v) := quadraticValue_nonneg (X.positive a x hx) v

lemma exhaustion_value_eq (i : StandardChart) (n n' : ℕ) {x : BaseCoordinates}
    (hx : x∈traceInterior (i,n)) (hx' : x∈traceInterior (i,n')) (v : FiberCoordinates) :
    X.value (i,n) (x,v)=X.value (i,n') (x,v) := by
  let Ω := traceInterior (i,n) ∩ traceInterior (i,n')
  have havg : ∀ y r, 0<r → closedBall y r ⊆ Ω →
      (⨍ z in ball y r, X.value (i,n) (z,v)) = ⨍ z in ball y r, X.value (i,n') (z,v) := by
    intro y r _ hb
    have hbn := (ball_subset_closedBall.trans hb).trans inter_subset_left
    have hbn' := (ball_subset_closedBall.trans hb).trans inter_subset_right
    have h1 := X.averages (i,n) y r v hbn
    have h2 := X.averages (i,n') y r v hbn'
    have he (k : ℕ) : (⨍ z in ball y r,
        quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n) z) v) =
        ⨍ z in ball y r, quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n') z) v := by
      apply average_congr
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [cutoffTrace_eq _ _ (traceDomain_subset_support _ (traceInterior_subset_domain _ (hbn hz))),
        cutoffTrace_eq _ _ (traceDomain_subset_support _ (traceInterior_subset_domain _ (hbn' hz)))]
    simpa only [value] using tendsto_nhds_unique (h1.congr he) h2
  exact ((X.base_psh (i,n) v).mono inter_subset_left).eqOn_of_averages
    (isOpen_ball.inter isOpen_ball) ((X.base_psh (i,n') v).mono inter_subset_right)
    (fun y hy ↦ X.value_nonneg _ hy.1 v) (fun y hy ↦ X.value_nonneg _ hy.2 v) havg ⟨hx,hx'⟩
end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def traceLevel (z : BaseCoordinates) : ℕ := Nat.ceil ‖z‖
lemma mem_traceInterior_level (i : StandardChart) (z : BaseCoordinates) :
    z∈traceInterior (i,traceLevel z) := by
  change dist z 0 < _
  rw [dist_zero_right]
  have h : ‖z‖≤(traceLevel z : ℝ) := Nat.le_ceil _
  dsimp
  linarith

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
  (X : ExtractedTrace ex P)
def globalMatrix (i : StandardChart) (z : BaseCoordinates) : TwoMatrix :=
  X.matrix (i,traceLevel z) z
def globalValue (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) : ℝ :=
  quadraticValue (X.globalMatrix i p.1) p.2
lemma globalValue_eq_value (i : StandardChart) (n : ℕ)
    {p : BaseCoordinates × FiberCoordinates} (hp : p.1∈traceInterior (i,n)) :
    X.globalValue i p=X.value (i,n) p :=
  X.exhaustion_value_eq i _ n (mem_traceInterior_level i p.1) hp p.2
lemma globalMatrix_positive (i : StandardChart) (z : BaseCoordinates) : (X.globalMatrix i z).PosSemidef :=
  X.positive _ _ (mem_traceInterior_level i z)
lemma globalValue_nonneg (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) :
    0≤X.globalValue i p := quadraticValue_nonneg (X.globalMatrix_positive i p.1) p.2

lemma globalValue_upperSemicontinuous (i : StandardChart) : UpperSemicontinuous (X.globalValue i) := by
  intro p c hc
  let n := traceLevel p.1
  have hp : p∈traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates) :=
    ⟨mem_traceInterior_level i p.1,mem_univ _⟩
  have hU : IsOpen (traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates)) := isOpen_ball.prod isOpen_univ
  have hsc := (X.psh (i,n)).1 p hp c (by
    change X.value (i,n) p < c
    rwa [← X.globalValue_eq_value i n hp.1])
  rw [hU.nhdsWithin_eq hp] at hsc
  filter_upwards [hsc,hU.mem_nhds hp] with y hy hyU
  change X.value (i,n) y < c at hy
  rwa [X.globalValue_eq_value i n hyU.1]

lemma exists_traceInterior_of_compact (i : StandardChart) {K : Set BaseCoordinates} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ traceInterior (i,n) := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image continuous_norm.continuousOn
  obtain ⟨n,hn⟩ := exists_nat_gt C
  refine ⟨n,fun x hx ↦ ?_⟩
  have h := hC (mem_image_of_mem _ hx)
  change dist x 0 < (n:ℝ)+2
  rw [dist_zero_right]
  linarith

lemma globalValue_psh (i : StandardChart) : DiskPshOn univ (X.globalValue i) := by
  refine ⟨(X.globalValue_upperSemicontinuous i).upperSemicontinuousOn univ,?_⟩
  intro U hU γ hγ _
  have hsc : UpperSemicontinuousOn (X.globalValue i ∘ γ) U :=
    ((X.globalValue_upperSemicontinuous i).upperSemicontinuousOn univ).comp hγ.continuousOn (mapsTo_univ _ _)
  refine ⟨hsc,?_⟩
  intro z hz r hr hball
  have hcompact : IsCompact ((fun w ↦ (γ w).1) '' closedBall z r) :=
    (isCompact_closedBall z r).image_of_continuousOn (hγ.continuousOn.fst.mono hball)
  obtain ⟨n,hn⟩ := exists_traceInterior_of_compact i hcompact
  let V := U ∩ γ ⁻¹' (traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates))
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (isOpen_ball.prod isOpen_univ)
  have hB : closedBall z r ⊆ V := by
    intro w hw
    exact ⟨hball hw,hn (mem_image_of_mem _ hw),mem_univ _⟩
  have hp := (X.psh (i,n)).2 V hV γ (hγ.mono inter_subset_left) (fun _ h ↦ h.2)
  have he : EqOn (X.globalValue i ∘ γ) (X.value (i,n) ∘ γ) V :=
    fun w hw ↦ X.globalValue_eq_value i n hw.2.1
  have he' : EqOn (X.globalValue i ∘ γ) (X.value (i,n) ∘ γ) (ball z r) :=
    he.mono (ball_subset_closedBall.trans hB)
  have hs := hp.2 z (hB (mem_closedBall_self hr.le)) r hr hB
  refine ⟨hs.1.congr_fun he'.symm measurableSet_ball,?_⟩
  rw [he (hB (mem_closedBall_self hr.le))]
  have hint : (∫ w in ball z r, (X.globalValue i ∘ γ) w)=
      ∫ w in ball z r, (X.value (i,n) ∘ γ) w := integral_congr_ae
    ((ae_restrict_mem measurableSet_ball).mono fun w hw ↦ he' hw)
  rw [hint]
  exact hs.2
end ExtractedTrace
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.WeakBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory
open scoped ENNReal
noncomputable section

section Composition
variable {α : Type u1} {β : Type u2} {E : Type u3} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {T : α → β} {c : ℝ≥0∞}

def boundedCompositionLp (hT : Measurable T) (hc : c ≠ ∞)
    (hdom : Measure.map T μ ≤ c • ν) : Lp E p ν →L[ℝ] Lp E p μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ T (⟨hT,rfl⟩ : MeasurePreserving T μ (Measure.map T μ))).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hc hdom)

lemma boundedCompositionLp_coe (hT : Measurable T) (hc : c ≠ ∞)
    (hdom : Measure.map T μ ≤ c • ν) (f : Lp E p ν) :
    boundedCompositionLp hT hc hdom f =ᵐ[μ] fun x ↦ f (T x) := by
  have hpres : MeasurePreserving T μ (Measure.map T μ) := ⟨hT,rfl⟩
  have he := hpres.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul hc hdom f)
  exact (Lp.coeFn_compMeasurePreserving _ hpres).trans he
end Composition

section Weak
variable {E : Type u4} {F : Type u5} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

local instance instInnerProductSpaceReal_solutions_r467536_1 : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
local instance instInnerProductSpaceReal_solutions_1 : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F

omit [CompleteSpace E] in
lemma complex_weak_implies_real {u : ℕ → E} {w : E}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (u k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ v, Tendsto (fun k ↦ inner ℝ (u k) v) atTop (𝓝 (inner ℝ w v)) := by
  intro v
  simpa only [real_inner_eq_re_inner ℂ, RCLike.re_eq_complex_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp (hw v)

lemma real_weakLimit_map (A : E →L[ℝ] F) {u : ℕ → E} {w : E}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℝ (u k) v) atTop (𝓝 (inner ℝ w v))) :
    ∀ v, Tendsto (fun k ↦ inner ℝ (A (u k)) v) atTop (𝓝 (inner ℝ (A w) v)) := by
  intro v
  simpa only [← ContinuousLinearMap.adjoint_inner_right] using hw (A.adjoint v)

end Weak

section Jacobian
variable {X : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma map_restrict_involution_le {T : X → X} {K : Set X} {C : ℝ}
    (hT : Measurable T) (hi : Function.Involutive T)
    (hTK : MeasurableSet (T '' K)) {T' : X → X →L[ℝ] X}
    (hd : ∀ x ∈ T '' K, HasFDerivWithinAt T (T' x) (T '' K) x)
    (hb : ∀ x ∈ T '' K, |(T' x).det| ≤ C) :
    Measure.map T (μ.restrict K) ≤ ENNReal.ofReal C • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hT hs,Measure.restrict_apply (hT hs),Measure.smul_apply]
  have he : T ⁻¹' s ∩ K = T '' (s ∩ T '' K) := by
    ext x
    constructor
    · rintro ⟨hxs,hxK⟩
      exact ⟨T x,⟨hxs,⟨x,hxK,rfl⟩⟩,hi x⟩
    · rintro ⟨y,⟨hys,⟨z,hzK,hzy⟩⟩,hyx⟩
      have hTx : T x=y := by rw [← hyx,hi]
      refine ⟨by simpa only [mem_preimage,hTx] using hys,?_⟩
      have hxz : x=z := by rw [← hyx,← hzy,hi]
      simpa only [hxz] using hzK
  rw [he]
  calc
    μ (T '' (s ∩ T '' K)) ≤ ∫⁻ x in s ∩ T '' K, ENNReal.ofReal |(T' x).det| ∂μ :=
      addHaar_image_le_lintegral_abs_det_fderiv μ (hs.inter hTK)
        (fun x hx ↦ (hd x hx.2).mono inter_subset_right)
    _ ≤ ∫⁻ _x in s ∩ T '' K, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono measurable_const (fun x hx ↦ ENNReal.ofReal_le_ofReal (hb x hx.2))
    _ = ENNReal.ofReal C * μ (s ∩ T '' K) := by simp
    _ ≤ ENNReal.ofReal C • μ s := by simpa only [smul_eq_mul] using mul_le_mul_right (measure_mono inter_subset_left) (ENNReal.ofReal C)
end Jacobian
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory
open scoped ENNReal
noncomputable section
section Multiplier
variable {α : Type u7} {E : Type u8} {F : Type u9} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {A : α → E →L[ℝ] F} {C : ℝ}

omit [Fact (1 ≤ p)] in
lemma boundedMultiplier_memLp (hA : AEStronglyMeasurable A μ)
    (_hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (f : Lp E p μ) :
    MemLp (fun x ↦ A x (f x)) p μ := by
  apply (((Lp.memLp f).norm).const_smul C).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable f)))
  filter_upwards [hb] with x hx
  simpa only [Pi.smul_apply,smul_eq_mul] using
    (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def boundedMultiplierLp (hA : AEStronglyMeasurable A μ)
    (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : Lp E p μ →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (boundedMultiplier_memLp hA hC hb f).toLp (fun x ↦ A x (f x))
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [(boundedMultiplier_memLp hA hC hb (f+g)).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb f).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb g).coeFn_toLp,
          Lp.coeFn_add f g,
          Lp.coeFn_add ((boundedMultiplier_memLp hA hC hb f).toLp _)
            ((boundedMultiplier_memLp hA hC hb g).toLp _)] with x hfg hf hg hadd hsum
        simp only [hfg,hf,hg,hadd,map_add,hsum,Pi.add_apply]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [(boundedMultiplier_memLp hA hC hb (c • f)).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb f).coeFn_toLp,
          Lp.coeFn_smul c f, Lp.coeFn_smul c ((boundedMultiplier_memLp hA hC hb f).toLp _)]
          with x hcf hf hsmul hout
        simp only [hcf,hf,hsmul,map_smul,hout,RingHom.id_apply,Pi.smul_apply] }
    C (fun f ↦ by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(boundedMultiplier_memLp hA hC hb f).coeFn_toLp,hb] with x hx hbx
      change ‖((boundedMultiplier_memLp hA hC hb f).toLp (fun x ↦ A x (f x))) x‖ ≤ C * ‖f x‖
      rw [hx]
      exact (A x).le_opNorm (f x) |>.trans
        (mul_le_mul_of_nonneg_right hbx (norm_nonneg _)))

lemma boundedMultiplierLp_coe (hA : AEStronglyMeasurable A μ)
    (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (f : Lp E p μ) :
    boundedMultiplierLp hA hC hb f =ᵐ[μ] fun x ↦ A x (f x) :=
  (boundedMultiplier_memLp hA hC hb f).coeFn_toLp
end Multiplier
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory
noncomputable section

lemma compact_involution_map_bound {X : Type u10} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {T : X → X} {U K : Set X}
    (hT : Measurable T) (hi : Function.Involutive T) (hU : IsOpen U)
    (hd : ContDiffOn ℝ 1 T U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hTU : MapsTo T U U) :
    ∃ C : ℝ, 0 ≤ C ∧ Measure.map T (μ.restrict K) ≤ ENNReal.ofReal C • μ := by
  have hTK : IsCompact (T '' K) := hK.image_of_continuousOn (hd.continuousOn.mono hKU)
  have hTKU : T '' K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact hTU (hKU hx)
  have hc : ContinuousOn (fun x ↦ |(fderiv ℝ T x).det|) (T '' K) :=
    (continuous_abs.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn
        (hd.continuousOn_fderiv_of_isOpen hU le_rfl))).mono hTKU
  obtain ⟨C,hC⟩ := hTK.bddAbove_image hc
  refine ⟨max C 0,le_max_right _ _,map_restrict_involution_le (T' := fderiv ℝ T) hT hi hTK.measurableSet ?_ ?_⟩
  · intro x hx
    exact ((hd.differentiableOn_one x (hTKU hx)).differentiableAt
      (hU.mem_nhds (hTKU hx))).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section
abbrev MatrixCoefficients := EuclideanSpace ℂ (Fin 2 × Fin 2)

lemma matrix_eq_of_quadratic_eq {H K : TwoMatrix} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (h : ∀ v : FiberCoordinates, quadraticValue H v=quadraticValue K v) : H=K := by
  rw [← matrixFromQuadratic_value hH,← matrixFromQuadratic_value hK]
  congr 1
  exact funext h

def congruenceCoefficients (A : TwoMatrix) : MatrixCoefficients →L[ℂ] MatrixCoefficients :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c ↦ matrixToCoefficients (A.conjTranspose*coefficientsToMatrix c*A)
      map_add' := fun c d ↦ by simp only [map_add,mul_add,add_mul]
      map_smul' := fun t c ↦ by simp only [map_smul,Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }

lemma continuous_congruenceCoefficients : Continuous congruenceCoefficients := by
  apply continuous_clm_apply.mpr
  intro c
  change Continuous (fun A : TwoMatrix ↦ matrixToCoefficients (A.conjTranspose*coefficientsToMatrix c*A))
  have hm : Continuous (matrixToCoefficients (n := Fin 2)) := LinearMap.continuous_of_finiteDimensional _
  exact hm.comp (by fun_prop)

lemma TwistedPshForm.matrix_compatible {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m)
    (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    P.matrix i z= traceScalar m i j z •
      ((D.coordinateTransition i j z).transpose.conjTranspose *
        P.matrix j (coordinateChange i j z)*(D.coordinateTransition i j z).transpose) := by
  apply matrix_eq_of_quadratic_eq (P.positive i z).isHermitian
    ((Matrix.isHermitian_conjTranspose_mul_mul _ (P.positive j (coordinateChange i j z)).isHermitian).smul (by simp [IsSelfAdjoint]))
  intro v
  rw [P.compatible i j z hz,← quadraticValue_congruence]
  change _=(quadraticValueCLM v) (_ • _)
  rw [map_smul,smul_eq_mul]
  rfl

lemma coordinateChange_symm (i j : StandardChart) : coordinateChange i j=coordinateChange j i := by
  funext z
  simp only [coordinateChange,scalarCoordinateChange,eq_comm]

lemma coordinateChange_involutive (i j : StandardChart) : Function.Involutive (coordinateChange i j) := by
  intro z
  rw [coordinateChange_symm i j] at *
  simpa only [← coordinateChange_symm i j] using coordinateChange_inv i j z

lemma coordinateChange_measurable (i j : StandardChart) : Measurable (coordinateChange i j) := by
  unfold coordinateChange scalarCoordinateChange
  split_ifs <;> fun_prop

lemma coordinateChange_contDiffOn (i j : StandardChart) :
    ContDiffOn ℝ 1 (coordinateChange i j) (coordinateOverlap i j) := by
  apply ContDiffOn.prodMk
  · by_cases h : i.1=j.1
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact contDiffOn_fst.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).1.resolve_left h)
  · by_cases h : i.2=j.2
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact contDiffOn_snd.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).2.resolve_left h)

lemma coordinateChange_mapsTo_overlap (i j : StandardChart) :
    MapsTo (coordinateChange i j) (coordinateOverlap i j) (coordinateOverlap i j) := by
  intro z hz
  rw [coordinateOverlap_iff] at hz ⊢
  constructor
  · rcases hz.1 with h|h
    · exact Or.inl h
    · right
      simp only [coordinateChange,scalarCoordinateChange]
      split_ifs <;> simpa using h
  · rcases hz.2 with h|h
    · exact Or.inl h
    · right
      simp only [coordinateChange,scalarCoordinateChange]
      split_ifs <;> simpa using h

lemma coordinateChange_compact_bound (i j : StandardChart) {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∃ C : ℝ, 0≤C ∧ Measure.map (coordinateChange i j) (volume.restrict K) ≤ ENNReal.ofReal C • volume := by
  let : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
    inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
  exact compact_involution_map_bound (coordinateChange_measurable i j)
    (coordinateChange_involutive i j) (coordinateOverlap_open i j)
    (coordinateChange_contDiffOn i j) hK hKU (coordinateChange_mapsTo_overlap i j)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory
open scoped ENNReal
noncomputable section

lemma L2_norm_tendsto_zero_of_bounded_ae {α : Type u11} {E : Type u12} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} [IsFiniteMeasure μ]
    (f : ℕ → Lp E 2 μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖≤C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ f k x) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖f k‖) atTop (𝓝 0) := by
  have hn (k : ℕ) : (∫ x, ‖f k x‖^2 ∂μ)=‖f k‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    exact (real_inner_self_eq_norm_sq (f k x)).symm
  have hh := tendsto_integral_of_dominated_convergence
    (F := fun k x ↦ ‖f k x‖^2) (f := fun _ ↦ (0:ℝ)) (fun _ : α ↦ C^2)
    (fun k ↦ ((Lp.aestronglyMeasurable (f k)).norm.pow 2))
    (integrable_const (C^2))
    (fun k ↦ (hb k).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f k x‖)] using
        pow_le_pow_left₀ (norm_nonneg _) hx 2)
    (hlim.mono fun x hx ↦ by simpa using hx.norm.pow 2)
  simp only [integral_zero,hn] at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh.sqrt

section Weak
variable {E : Type u13} {F : Type u14} {G : Type u15} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [InnerProductSpace ℂ G] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
local instance instInnerProductSpaceReal_solutions_2_r467536_1 : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
local instance instInnerProductSpaceReal_solutions_3_r467536_1 : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F
local instance instInnerProductSpaceReal_solutions_4 : InnerProductSpace ℝ G := InnerProductSpace.rclikeToReal ℂ G
lemma real_weakLimit_two_maps (A : E →L[ℝ] G) (B : F →L[ℝ] G)
    {u : ℕ → E} {v : ℕ → F} {w : E} {z : F}
    (hw : ∀ e, Tendsto (fun k ↦ inner ℂ (u k) e) atTop (𝓝 (inner ℂ w e)))
    (hz : ∀ f, Tendsto (fun k ↦ inner ℂ (v k) f) atTop (𝓝 (inner ℂ z f)))
    (herr : Tendsto (fun k ↦ ‖B (v k)-A (u k)‖) atTop (𝓝 0)) : B z=A w := by
  have he := tendsto_zero_iff_norm_tendsto_zero.mpr herr
  have hweak (g : G) := (real_weakLimit_map B (complex_weak_implies_real hz) g).sub
    (real_weakLimit_map A (complex_weak_implies_real hw) g)
  have hzero (g : G) : Tendsto (fun k ↦ inner ℝ (B (v k)-A (u k)) g) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using he.inner tendsto_const_nhds
  have heq (g : G) : inner ℝ (B z-A w) g=0 := by
    apply tendsto_nhds_unique _ (hzero g)
    simpa only [inner_sub_left] using hweak g
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (heq (B z-A w)))
end Weak
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Gluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma matrix_coefficients_inverse (c : MatrixCoefficients) :
    matrixToCoefficients (coefficientsToMatrix c)=c := by ext p; rfl

lemma traceScalar_tendsto {ex : ℕ → ℕ} (hex : Tendsto ex atTop atTop)
    (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    Tendsto (fun k ↦ traceScalar (ex k) i j z) atTop (𝓝 1) := by
  have hn : ‖polarizationTransition i j (affineQuadric i z)‖≠0 := by
    rw [norm_ne_zero_iff,polarizationTransition_affine]
    exact mul_ne_zero (firstFactor_ne_zero hz) (secondFactor_ne_zero hz)
  simpa only [traceScalar,Real.rpow_zero,Function.comp_def] using
    (Real.continuousAt_const_rpow (b := 0) hn).tendsto.comp
      ((tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp hex)

def coefficientFrame (D : EqualizerData) (i j : StandardChart) (z : BaseCoordinates) :
    CoefficientSpace →L[ℝ] CoefficientSpace :=
  (congruenceCoefficients (D.coordinateTransition i j z).transpose).restrictScalars ℝ

lemma coefficientFrame_continuousOn (D : EqualizerData) (i j : StandardChart) :
    ContinuousOn (coefficientFrame D i j) (coordinateOverlap i j) :=
  (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn
    (continuous_congruenceCoefficients.comp_continuousOn
      (by
        apply continuousOn_pi.mpr; intro a
        apply continuousOn_pi.mpr; intro b
        exact continuousOn_pi.mp (continuousOn_pi.mp (D.coordinateTransition_continuousOn i j) b) a))

lemma coefficientFrame_bounded (D : EqualizerData) (i j : StandardChart)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∃ C : ℝ, 0≤C ∧ ∀ z∈K, ‖coefficientFrame D i j z‖≤C := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image ((coefficientFrame_continuousOn D i j).mono hKU).norm
  exact ⟨max C 0,le_max_right _ _,fun z hz ↦ (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma coefficients_eq (k : ℕ) (a : TraceIndex) :
    X.f k a =ᵐ[volume] fun x ↦ matrixToCoefficients (cutoffTrace (P k) a x) := by
  filter_upwards [X.coefficients k a] with x hx
  rw [← matrix_coefficients_inverse (X.f k a x),hx]

lemma coefficients_change {a b : TraceIndex} {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap a.1 b.1)
    (hKa : K ⊆ traceSupport a)
    (hKb : MapsTo (coordinateChange a.1 b.1) K (traceSupport b)) (k : ℕ) :
    ∀ᵐ x ∂volume.restrict K,
      X.f k a x=traceScalar (ex k) a.1 b.1 x •
        coefficientFrame D a.1 b.1 x (X.f k b (coordinateChange a.1 b.1 x)) := by
  obtain ⟨C,_,hC⟩ := coordinateChange_compact_bound a.1 b.1 hK hKU
  have hq : Measure.QuasiMeasurePreserving (coordinateChange a.1 b.1) (volume.restrict K) volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hC⟩
  filter_upwards [ae_restrict_of_ae (X.coefficients_eq k a),hq.ae (X.coefficients_eq k b),
    ae_restrict_mem hK.measurableSet] with x ha hb hx
  rw [ha,hb,cutoffTrace_eq _ _ (hKa hx),cutoffTrace_eq _ _ (hKb hx),
    (P k).matrix_compatible a.1 b.1 (hKU hx)]
  change matrixToCoefficients (_ • _) = _
  rfl

lemma weak_coefficients_change (hex : Tendsto ex atTop atTop)
    {a b : TraceIndex} {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap a.1 b.1)
    (hKa : K ⊆ traceSupport a)
    (hKb : MapsTo (coordinateChange a.1 b.1) K (traceSupport b)) :
    ∀ᵐ x ∂volume.restrict K,
      X.w a x=coefficientFrame D a.1 b.1 x (X.w b (coordinateChange a.1 b.1 x)) := by
  let μ := volume.restrict K
  let T := coordinateChange a.1 b.1
  let F := coefficientFrame D a.1 b.1
  have : IsFiniteMeasure μ := ⟨by
    change volume.restrict K univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨J,_,hJ⟩ := coordinateChange_compact_bound a.1 b.1 hK hKU
  have hq : Measure.QuasiMeasurePreserving T μ volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hJ⟩
  obtain ⟨C,hC,hFC⟩ := coefficientFrame_bounded D a.1 b.1 hK hKU
  have hFm : AEStronglyMeasurable F μ :=
    ((coefficientFrame_continuousOn D a.1 b.1).mono hKU).aestronglyMeasurable hK.measurableSet
  have hFb : ∀ᵐ x ∂μ, ‖F x‖≤C := (ae_restrict_mem hK.measurableSet).mono hFC
  let B : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    boundedCompositionLp measurable_id ENNReal.one_ne_top (by
      simpa only [Measure.map_id,one_smul] using (Measure.restrict_le_self (μ := volume) (s := K)))
  let A₀ : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    boundedCompositionLp (coordinateChange_measurable a.1 b.1) ENNReal.ofReal_ne_top hJ
  let A : CoefficientL2 →L[ℝ] Lp CoefficientSpace 2 μ :=
    (boundedMultiplierLp hFm hC hFb).comp A₀
  have hB (f : CoefficientL2) : B f =ᵐ[μ] f := by
    exact boundedCompositionLp_coe measurable_id ENNReal.one_ne_top _ f
  have hA (f : CoefficientL2) : A f =ᵐ[μ] fun x ↦ F x (f (T x)) := by
    filter_upwards [boundedMultiplierLp_coe hFm hC hFb (A₀ f),
      boundedCompositionLp_coe (coordinateChange_measurable a.1 b.1) ENNReal.ofReal_ne_top hJ f]
      with x hx hy
    change boundedMultiplierLp hFm hC hFb (A₀ f) x = _
    rw [hx,hy]
  let u (k : ℕ) := X.f (X.subsequence k) b
  let v (k : ℕ) := X.f (X.subsequence k) a
  let e (k : ℕ) := B (v k)-A (u k)
  have hu (k : ℕ) : ∀ᵐ x ∂μ, ‖F x (u k (T x))‖≤C*(8*traceBound D b) := by
    filter_upwards [hq.ae (X.bound (X.subsequence k) b),hFb] with x hx hy
    exact (F x).le_opNorm _ |>.trans
      (mul_le_mul hy hx.1 (norm_nonneg _) hC)
  have he (k : ℕ) : e k =ᵐ[μ] fun x ↦
      (traceScalar (ex (X.subsequence k)) a.1 b.1 x-1) • F x (u k (T x)) := by
    filter_upwards [Lp.coeFn_sub (B (v k)) (A (u k)),hB (v k),hA (u k),
      X.coefficients_change hK hKU hKa hKb (X.subsequence k)] with x hsub hv hu hc
    change (B (v k)-A (u k)) x = _
    rw [hsub,Pi.sub_apply,hv,hu]
    change X.f (X.subsequence k) a x - _ = _
    rw [hc,sub_smul,one_smul]
  have hb (k : ℕ) : ∀ᵐ x ∂μ, ‖e k x‖≤8*traceBound D a+C*(8*traceBound D b) := by
    filter_upwards [Lp.coeFn_sub (B (v k)) (A (u k)),hB (v k),hA (u k),
      ae_restrict_of_ae (X.bound (X.subsequence k) a),hu k] with x hsub hv hu hvb hub
    change ‖(B (v k)-A (u k)) x‖≤_
    rw [hsub,Pi.sub_apply,hv,hu]
    exact (norm_sub_le _ _).trans (add_le_add hvb.1 hub)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ e k x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr he,ae_all_iff.mpr hu,ae_restrict_mem hK.measurableSet]
      with x hx hb hxK
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hs := (traceScalar_tendsto (hex.comp X.strictMono.tendsto_atTop) a.1 b.1 (hKU hxK)).sub
      (tendsto_const_nhds (x := (1:ℝ)))
    have ht : Tendsto (fun k ↦ ‖traceScalar (ex (X.subsequence k)) a.1 b.1 x-1‖ *
        (C*(8*traceBound D b))) atTop (𝓝 0) := by simpa using hs.norm.mul_const (C*(8*traceBound D b))
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ ht
    intro k
    rw [hx,norm_smul]
    exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _)
  let : InnerProductSpace ℝ CoefficientSpace := InnerProductSpace.rclikeToReal ℂ CoefficientSpace
  have herr : Tendsto (fun k ↦ ‖e k‖) atTop (𝓝 0) :=
    L2_norm_tendsto_zero_of_bounded_ae e
      (add_nonneg (mul_nonneg (by positivity) (traceBound_nonneg D a))
        (mul_nonneg hC (mul_nonneg (by positivity) (traceBound_nonneg D b)))) hb hlim
  have hw : B (X.w a)=A (X.w b) :=
    real_weakLimit_two_maps A B (X.weak b) (X.weak a) herr
  filter_upwards [hB (X.w a),hA (X.w b)] with x hx hy
  rw [← hx,hw,hy]

end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma coordinateChange_differentiableOn (i j : StandardChart) :
    DifferentiableOn ℂ (coordinateChange i j) (coordinateOverlap i j) := by
  apply DifferentiableOn.prodMk
  · by_cases h : i.1=j.1
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact differentiableOn_fst.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).1.resolve_left h)
  · by_cases h : i.2=j.2
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact differentiableOn_snd.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).2.resolve_left h)

lemma coordinateFiberChange_differentiableOn (D : EqualizerData) (i j : StandardChart)
    (v : FiberCoordinates) : DifferentiableOn ℂ
      (fun z ↦ (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v))
      (coordinateOverlap i j) := by
  apply (coordinateChange_differentiableOn i j).prodMk
  apply differentiableOn_pi.mpr
  intro a
  change DifferentiableOn ℂ (fun z ↦ ∑ b : Fin 2, D.coordinateTransition i j z b a * v b) _
  apply DifferentiableOn.fun_sum
  intro b _
  exact (((D.coordinateTransition_regular i j b a).regular.analyticOnNhd
    (coordinateOverlap_open i j)).differentiableOn).mul_const (v b)

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma globalValue_representative_ae (i : StandardChart) (n : ℕ)
    {K : Set BaseCoordinates} (hKn : K ⊆ traceInterior (i,n)) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=quadraticValue (coefficientsToMatrix (X.w (i,n) x)) v := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hKn (X.representative (i,n)),
    ae_restrict_mem (μ := volume) (s := traceInterior (i,n)) measurableSet_ball |>
      ae_restrict_of_ae_restrict_of_subset hKn] with x hx hxU
  intro v
  rw [X.globalValue_eq_value i n hxU]
  change quadraticValue (X.matrix (i,n) x) v = _
  rw [hx]

lemma globalValue_composed_representative_ae (i j : StandardChart) (m : ℕ)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j)
    (hmap : MapsTo (coordinateChange i j) K (traceInterior (j,m))) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue j (coordinateChange i j x,v)=
        quadraticValue (coefficientsToMatrix (X.w (j,m) (coordinateChange i j x))) v := by
  obtain ⟨C,_,hC⟩ := coordinateChange_compact_bound i j hK hKU
  have hq : Measure.QuasiMeasurePreserving (coordinateChange i j) (volume.restrict K) volume :=
    ⟨coordinateChange_measurable _ _,Measure.absolutelyContinuous_of_le_smul hC⟩
  have hrb : ∀ᵐ x ∂volume, x∈traceInterior (j,m) →
      X.matrix (j,m) x=coefficientsToMatrix (X.w (j,m) x) :=
    (ae_restrict_iff' measurableSet_ball).mp (X.representative (j,m))
  filter_upwards [hq.ae hrb,ae_restrict_mem hK.measurableSet] with x hb hx
  intro v
  rw [X.globalValue_eq_value j m (hmap hx)]
  change quadraticValue (X.matrix (j,m) (coordinateChange i j x)) v = _
  rw [hb (hmap hx)]

lemma coefficientFrame_quadraticValue (D : EqualizerData) (i j : StandardChart)
    (x : BaseCoordinates) (c : CoefficientSpace) (v : FiberCoordinates) :
    quadraticValue (coefficientsToMatrix (coefficientFrame D i j x c)) v =
      quadraticValue (coefficientsToMatrix c) ((D.coordinateTransition i j x).transpose.mulVec v) :=
  quadraticValue_congruence _ _ _

lemma globalValue_change_ae_indices (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    (n m : ℕ) {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j)
    (hn : K ⊆ traceInterior (i,n))
    (hm : MapsTo (coordinateChange i j) K (traceInterior (j,m))) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=X.globalValue j
        (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  have hKa : K ⊆ traceSupport (i,n) := hn.trans ((traceInterior_subset_domain _).trans (traceDomain_subset_support _))
  have hKb : MapsTo (coordinateChange i j) K (traceSupport (j,m)) :=
    fun x hx ↦ traceDomain_subset_support _ (traceInterior_subset_domain _ (hm hx))
  have he := X.weak_coefficients_change hex (a := (i,n)) (b := (j,m)) hK hKU hKa hKb
  filter_upwards [he,X.globalValue_representative_ae i n hn,
    X.globalValue_composed_representative_ae i j m hK hKU hm] with x he ha hb
  intro v
  calc
    X.globalValue i (x,v) = quadraticValue (coefficientsToMatrix (X.w (i,n) x)) v := ha v
    _ = quadraticValue (coefficientsToMatrix (coefficientFrame D i j x
        (X.w (j,m) (coordinateChange i j x)))) v := congrArg (fun c ↦ quadraticValue (coefficientsToMatrix c) v) he
    _ = quadraticValue (coefficientsToMatrix (X.w (j,m) (coordinateChange i j x)))
        ((D.coordinateTransition i j x).transpose.mulVec v) := coefficientFrame_quadraticValue D i j x _ v
    _ = _ := (hb _).symm

lemma globalValue_change_ae (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    {K : Set BaseCoordinates} (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∀ᵐ x ∂volume.restrict K, ∀ v : FiberCoordinates,
      X.globalValue i (x,v)=X.globalValue j
        (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  obtain ⟨n,hn⟩ := exists_traceInterior_of_compact i hK
  have hTK := hK.image_of_continuousOn ((coordinateChange_differentiableOn i j).continuousOn.mono hKU)
  obtain ⟨m,hm⟩ := exists_traceInterior_of_compact j hTK
  exact X.globalValue_change_ae_indices hex i j n m hK hKU hn
    (fun x hx ↦ hm (mem_image_of_mem _ hx))

lemma globalValue_change (hex : Tendsto ex atTop atTop) (i j : StandardChart)
    {x : BaseCoordinates} (hx : x∈coordinateOverlap i j) (v : FiberCoordinates) :
    X.globalValue i (x,v)=X.globalValue j
      (coordinateChange i j x,(D.coordinateTransition i j x).transpose.mulVec v) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (coordinateOverlap_open i j) x hx
  let ρ := r/2
  have hρ : 0<ρ := by dsimp [ρ]; linarith
  have hcb : closedBall x ρ ⊆ coordinateOverlap i j := by
    intro y hy
    exact hball (lt_of_le_of_lt hy (by change r/2 < r; linarith))
  have hb : ball x ρ ⊆ coordinateOverlap i j := ball_subset_closedBall.trans hcb
  let q (z : BaseCoordinates) := X.globalValue i (z,v)
  let s (z : BaseCoordinates) := X.globalValue j
    (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v)
  have hq : DiskPshOn (ball x ρ) q := (X.globalValue_psh i).comp (by fun_prop) (mapsTo_univ _ _)
  have hs : DiskPshOn (ball x ρ) s := (X.globalValue_psh j).comp
    ((coordinateFiberChange_differentiableOn D i j v).mono hb) (mapsTo_univ _ _)
  have he : q =ᵐ[volume.restrict (ball x ρ)] s :=
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall
      (X.globalValue_change_ae hex i j (isCompact_closedBall x ρ) hcb)).mono fun z hz ↦ hz v
  exact hq.eqOn_of_ae isOpen_ball hs
    (fun z _ ↦ X.globalValue_nonneg i (z,v)) (fun z _ ↦ X.globalValue_nonneg j _) he (mem_ball_self hρ)
end ExtractedTrace
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample
open Matrix
lemma source_A_det : source_A.det = 1 := by
  simp [source_A, Matrix.det_fin_two, source_a_mul_inv]

lemma source_B_det : source_B.det = 1 := by
  simp [source_B, Matrix.det_fin_two, source_s_mul_complement]

end QuadricCounterexample

namespace QuadricCounterexample
open Matrix OnePoint Filter Topology MeasureTheory

noncomputable def source_A_gl : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero source_A (by rw [source_A_det]; exact one_ne_zero)
noncomputable def source_B_gl : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero source_B (by rw [source_B_det]; exact one_ne_zero)

@[simp] lemma source_A_gl_val : (source_A_gl : Matrix (Fin 2) (Fin 2) ℂ) = source_A := rfl
@[simp] lemma source_B_gl_val : (source_B_gl : Matrix (Fin 2) (Fin 2) ℂ) = source_B := rfl

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.DualForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric
noncomputable section

@[simp] lemma affineP1_one (i : Fin 2) : affineP1 i 1 = (1 : ℂ) := by
  fin_cases i <;> simp [affineP1, reciprocalP1]

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
open scoped ComplexOrder

structure EqualizerData.PshDualForm (D : EqualizerData) where
  value : StandardChart → BaseCoordinates × FiberCoordinates → ℝ
  quadratic : ∀ i z, ∃ H : TwoMatrix, H.PosSemidef ∧ ∀ v,
    value i (z,v)=(star v ⬝ᵥ H.mulVec v).re
  psh : ∀ i, DiskPshOn Set.univ (value i)
  compatible : ∀ i j z, z ∈ coordinateOverlap i j → ∀ v,
    value i (z,v)=value j (coordinateChange i j z,(D.coordinateTransition i j z).transpose.mulVec v)

namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

def firstNorm (i : StandardChart) (p : BaseCoordinates × ℂ) : ℝ :=
  Q.value i (p.1,![p.2,0])
def secondNorm (i : StandardChart) (p : BaseCoordinates × ℂ) : ℝ :=
  Q.value i (p.1,![baseEval (D.lift i) p.1*p.2,baseEval (D.divisor i) p.1*p.2])

lemma firstNorm_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) (c : ℂ) :
    Q.firstNorm i (z,c)=Q.firstNorm j (coordinateChange i j z,topFactor i j z*c) := by
  have h := Q.compatible i j z hz ![c,0]
  simpa [firstNorm,EqualizerData.coordinateTransition,Matrix.transpose_apply,
    Matrix.mulVec, dotProduct,Fin.sum_univ_two] using h

lemma secondNorm_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) (c : ℂ) :
    Q.secondNorm i (z,c)=Q.secondNorm j
      (coordinateChange i j z,EqualizerData.quotientFactor i j z*c) := by
  have h := Q.compatible i j z hz
    ![baseEval (D.lift i) z*c,baseEval (D.divisor i) z*c]
  unfold secondNorm
  rw [h]
  congr 2
  have h1 := D.low_spec i j hz
  have h2 := D.divisor_factor i j hz
  ext k
  fin_cases k <;> norm_num [EqualizerData.coordinateTransition,Matrix.transpose_apply,
    Matrix.mulVec, dotProduct,Fin.sum_univ_two]
  · unfold EqualizerData.numerator at h1
    linear_combination c*h1
  · linear_combination c*h2

lemma nonneg (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) :
    0 ≤ Q.value i (z,v) := by
  obtain ⟨H,hH,h⟩ := Q.quadratic i z
  rw [h]
  exact (hH.dotProduct_mulVec_nonneg v).1

lemma scalar (i : StandardChart) (z : BaseCoordinates) (c : ℂ) (v : FiberCoordinates) :
    Q.value i (z,c • v)=‖c‖^2*Q.value i (z,v) := by
  obtain ⟨H,_,h⟩ := Q.quadratic i z
  rw [h,h]
  simp only [star_smul,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ← mul_assoc,Complex.star_def]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma firstNorm_psh (i : StandardChart) : DiskPshOn Set.univ (Q.firstNorm i) := by
  apply (Q.psh i).comp _ (mapsTo_univ _ _)
  apply DifferentiableOn.prodMk (by fun_prop)
  apply differentiableOn_pi.mpr
  intro k
  fin_cases k <;> dsimp <;> fun_prop

lemma secondNorm_psh (i : StandardChart) : DiskPshOn Set.univ (Q.secondNorm i) := by
  have hh : Differentiable ℂ (baseEval (D.lift i)) :=
    fun z ↦ (analytic_baseEval _ z (mem_univ _)).differentiableAt
  have hd : Differentiable ℂ (baseEval (D.divisor i)) :=
    fun z ↦ (analytic_baseEval _ z (mem_univ _)).differentiableAt
  apply (Q.psh i).comp _ (mapsTo_univ _ _)
  apply DifferentiableOn.prodMk (by fun_prop)
  apply differentiableOn_pi.mpr
  intro k
  fin_cases k <;> dsimp <;> fun_prop

end EqualizerData.PshDualForm

structure PshLine24 where
  value : Fin 2 → ℂ × ℂ → ℝ
  nonneg : ∀ i z c, 0 ≤ value i (z,c)
  scalar : ∀ i z c d, value i (z,c*d)=‖c‖^2*value i (z,d)
  psh : ∀ i, DiskPshOn Set.univ (value i)
  change : ∀ i j z, i=j ∨ z≠0 → ∀ c,
    value i (z,c)=value j (scalarCoordinateChange i j z,scalarFactor i j z^24*c)

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

lemma firstNorm_scalar (i : StandardChart) (z : BaseCoordinates) (c d : ℂ) :
    Q.firstNorm i (z,c*d)=‖c‖^2*Q.firstNorm i (z,d) := by
  unfold firstNorm
  rw [← Q.scalar]
  congr 2
  ext k
  fin_cases k <;> simp [Pi.smul_apply,smul_eq_mul]

lemma secondNorm_scalar (i : StandardChart) (z : BaseCoordinates) (c d : ℂ) :
    Q.secondNorm i (z,c*d)=‖c‖^2*Q.secondNorm i (z,d) := by
  unfold secondNorm
  rw [← Q.scalar]
  congr 2
  ext k
  fin_cases k <;> simp [Pi.smul_apply,smul_eq_mul,mul_left_comm]

def firstLine : PshLine24 where
  value i p := Q.firstNorm (i,0) ((p.1,0),p.2)
  nonneg i z c := Q.nonneg _ _ _
  scalar i z c d := Q.firstNorm_scalar _ _ c d
  psh i := (Q.firstNorm_psh (i,0)).comp (by fun_prop) (mapsTo_univ _ _)
  change i j z hz c := by
    have ho : (z,0) ∈ coordinateOverlap (i,0) (j,0) :=
      (coordinateOverlap_iff _ _ _).mpr ⟨hz,Or.inl rfl⟩
    simpa [EqualizerData.topFactor,firstFactor,coordinateChange,scalarCoordinateChange] using
      Q.firstNorm_change (i,0) (j,0) ho c

def secondLine : PshLine24 where
  value i p := Q.secondNorm (0,i) ((0,p.1),p.2)
  nonneg i z c := Q.nonneg _ _ _
  scalar i z c d := Q.secondNorm_scalar _ _ c d
  psh i := (Q.secondNorm_psh (0,i)).comp (by fun_prop) (mapsTo_univ _ _)
  change i j z hz c := by
    have ho : (0,z) ∈ coordinateOverlap (0,i) (0,j) :=
      (coordinateOverlap_iff _ _ _).mpr ⟨Or.inl rfl,hz⟩
    simpa [EqualizerData.quotientFactor,secondFactor,coordinateChange,scalarCoordinateChange] using
      Q.secondNorm_change (0,i) (0,j) ho c

end EqualizerData.PshDualForm

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section

@[simp] lemma source_matrices_zero : sourceGraphScalars.matrices 0=1 := rfl
@[simp] lemma source_matrices_one : sourceGraphScalars.matrices 1=source_A := rfl
@[simp] lemma source_matrices_two : sourceGraphScalars.matrices 2=source_B := rfl

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Noncollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def ExtractedTrace.pshDualForm {D : EqualizerData} {ex : ℕ → ℕ}
    {P : ∀ k, TwistedPshForm D (ex k)} (X : ExtractedTrace ex P)
    (hex : Tendsto ex atTop atTop) : D.PshDualForm where
  value := X.globalValue
  quadratic i z := ⟨X.globalMatrix i z,X.globalMatrix_positive i z,fun _ ↦ rfl⟩
  psh := X.globalValue_psh
  compatible i j _ hz v := X.globalValue_change hex i j hz v

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.BinaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Finsupp
open scoped BigOperators
noncomputable section
variable {R : Type u1} [CommRing R]

abbrev Form (n : ℕ) := Fin (n+1) → R
abbrev Poly := MvPolynomial (Fin 2) R

def exponent (n : ℕ) (k : Fin (n+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 k.val+Finsupp.single 1 (n-k.val)
@[simp] lemma exponent_zero (n : ℕ) (k : Fin (n+1)) : exponent n k 0=k.val := by
  simp [exponent]
@[simp] lemma exponent_one (n : ℕ) (k : Fin (n+1)) : exponent n k 1=n-k.val := by
  simp [exponent]
lemma exponent_injective (n : ℕ) : Function.Injective (exponent n) := by
  intro a b h
  apply Fin.ext
  simpa using congrArg (fun e ↦ e 0) h
lemma degree_binary (e : Fin 2 →₀ ℕ) : e.degree=e 0+e 1 := by
  simp [Finsupp.degree_eq_sum,Fin.sum_univ_two]
lemma exponent_degree (n : ℕ) (k : Fin (n+1)) : (exponent n k).degree=n := by
  rw [degree_binary,exponent_zero,exponent_one]
  omega
lemma exponent_of_degree (e : Fin 2 →₀ ℕ) {n : ℕ} (he : e.degree=n) :
    ∃ k : Fin (n+1),exponent n k=e := by
  rw [degree_binary] at he
  refine ⟨⟨e 0,by omega⟩,?_⟩
  ext i
  fin_cases i
  · simp
  · simp
    omega

def polynomial (n : ℕ) (a : Form (R := R) n) : Poly (R := R) :=
  ∑ k : Fin (n+1), monomial (exponent n k) (a k)
def coefficients (n : ℕ) (p : Poly (R := R)) : Form (R := R) n :=
  fun k ↦ p.coeff (exponent n k)

lemma polynomial_homogeneous (n : ℕ) (a : Form (R := R) n) :
    (polynomial n a).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro k _
  exact isHomogeneous_monomial _ (exponent_degree n k)
@[simp] lemma coefficients_polynomial (n : ℕ) (a : Form (R := R) n) :
    coefficients n (polynomial n a)=a := by
  ext k
  simp only [coefficients,polynomial,coeff_sum,coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [show exponent n j≠exponent n k from fun h ↦ hj (exponent_injective n h)]
  · simp
lemma polynomial_coefficients {n : ℕ} {p : Poly (R := R)} (hp : p.IsHomogeneous n) :
    polynomial n (coefficients n p)=p := by
  ext e
  by_cases he : e.degree=n
  · obtain ⟨k,rfl⟩ := exponent_of_degree e he
    exact congrFun (coefficients_polynomial n (coefficients n p)) k
  · rw [IsHomogeneous.coeff_eq_zero (polynomial_homogeneous n _) he,hp.coeff_eq_zero he]
lemma polynomial_injective (n : ℕ) : Function.Injective (polynomial (R := R) n) := by
  intro a b h
  simpa using congrArg (coefficients n) h
lemma polynomial_add (n : ℕ) (a b : Form (R := R) n) :
    polynomial n (a+b)=polynomial n a+polynomial n b := by
  simp [polynomial,Finset.sum_add_distrib]
lemma polynomial_smul (n : ℕ) (c : R) (a : Form (R := R) n) :
    polynomial n (c • a)=c • polynomial n a := by
  simp [polynomial,Finset.smul_sum,smul_monomial]
@[simp] lemma polynomial_zero (n : ℕ) : polynomial (R := R) n 0=0 := by simp [polynomial]
lemma coefficients_smul (n : ℕ) (c : R) (p : Poly (R := R)) :
    coefficients n (c • p)=c • coefficients n p := by ext; simp [coefficients]

def equivHomogeneous (n : ℕ) : Form (R := R) n ≃ₗ[R] homogeneousSubmodule (Fin 2) R n where
  toFun a := ⟨polynomial n a,polynomial_homogeneous n a⟩
  invFun p := coefficients n p
  left_inv := coefficients_polynomial n
  right_inv p := Subtype.ext (polynomial_coefficients p.property)
  map_add' a b := Subtype.ext (polynomial_add n a b)
  map_smul' c a := Subtype.ext (polynomial_smul n c a)

lemma eval_polynomial (n : ℕ) (a : Form (R := R) n) (v : Fin 2 → R) :
    MvPolynomial.eval v (polynomial n a)=∑ k : Fin (n+1), a k*v 0^k.val*v 1^(n-k.val) := by
  simp only [polynomial,eval_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]; ring
  · simp

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def kernelForm (h d : ℂ) : Poly (R := ℂ) := C d*X 0-C h*X 1
def liftForm (u v : ℂ) : Poly (R := ℂ) := C u*X 0+C v*X 1
lemma kernelForm_homogeneous (h d : ℂ) : (kernelForm h d).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X d 0).sub (isHomogeneous_C_mul_X h 1)
lemma liftForm_homogeneous (u v : ℂ) : (liftForm u v).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X u 0).add (isHomogeneous_C_mul_X v 1)
@[simp] lemma eval_kernelForm (h d : ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (kernelForm h d)=d*x 0-h*x 1 := by simp [kernelForm]
@[simp] lemma eval_liftForm (u v : ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (liftForm u v)=u*x 0+v*x 1 := by simp [liftForm]
lemma kernelForm_ne_zero (h d u v : ℂ) (hu : u*h+v*d=1) : kernelForm h d≠0 := by
  intro hh
  have h1 := congrArg (MvPolynomial.eval ![1,0]) hh
  have h2 := congrArg (MvPolynomial.eval ![0,1]) hh
  simp only [eval_kernelForm,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    mul_one,mul_zero,sub_zero,zero_sub] at h1 h2
  have h3 : h=0 := neg_eq_zero.mp h2
  simp [h1,h3] at hu

def adaptedPolynomials (h d u v : ℂ) : (t : ℕ) → Fin (2*t+1) → Poly (R := ℂ)
  | 0 => fun _ ↦ 1
  | t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (fun k ↦ kernelForm h d*X 1*adaptedPolynomials h d u v t k)
      (kernelForm h d*X 0^(2*t+1))) (liftForm u v^(2*(t+1)))
lemma adaptedPolynomials_homogeneous (h d u v : ℂ) (t : ℕ) (k : Fin (2*t+1)) :
    (adaptedPolynomials h d u v t k).IsHomogeneous (2*t) := by
  induction t with
  | zero => exact isHomogeneous_one (Fin 2) ℂ
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun k ↦ ?_) k
    · simpa only [adaptedPolynomials,Fin.snoc_last,one_mul] using (liftForm_homogeneous u v).pow (2*(t+1))
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun k ↦ ?_) k
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last,show 1+(2*t+1)=2*(t+1) by omega] using
          (kernelForm_homogeneous h d).mul (isHomogeneous_X_pow 0 (2*t+1))
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,show 1+1+2*t=2*(t+1) by omega] using
          ((kernelForm_homogeneous h d).mul (isHomogeneous_X ℂ 1)).mul (ih k)

lemma sum_snoc_two {n : ℕ} (a : Fin (n+2) → ℂ) (f : Fin n → Poly (R := ℂ))
    (p q : Poly (R := ℂ)) :
    (∑ k, a k • Fin.snoc (Fin.snoc f p) q k)=
      (∑ k : Fin n, a k.castSucc.castSucc • f k)+
        a (Fin.last n).castSucc • p+a (Fin.last (n+1)) • q := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma polynomial_sum_smul {ι : Type u2} [Fintype ι] (a : ι → ℂ)
    (p : Poly (R := ℂ)) (f : ι → Poly (R := ℂ)) :
    (∑ i,a i • (p*f i))=p*(∑ i,a i • f i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

lemma adaptedPolynomials_independent (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    LinearIndependent ℂ (adaptedPolynomials h d u v t) := by
  rw [Fintype.linearIndependent_iff]
  induction t with
  | zero =>
    intro c hc k
    have hk : k=0 := Fin.ext (by omega)
    subst k
    have hx := congrArg (MvPolynomial.eval ![0,0]) hc
    simpa [adaptedPolynomials,Fin.sum_univ_one] using hx
  | succ t ih =>
    intro c hc k
    simp only [adaptedPolynomials] at hc
    have hs := sum_snoc_two (n:=2*t+1) c
      (fun k ↦ kernelForm h d*X 1*adaptedPolynomials h d u v t k)
      (kernelForm h d*X 0^(2*t+1)) (liftForm u v^(2*(t+1)))
    have hc2 := hs.symm.trans hc
    let c₀ : Fin (2*t+1) → ℂ := fun k ↦ c k.castSucc.castSucc
    let p : Poly (R := ℂ) := ∑ k,c₀ k • adaptedPolynomials h d u v t k
    have hc' : kernelForm h d*X 1*p+
        c (Fin.last (2*t+1)).castSucc • (kernelForm h d*X 0^(2*t+1))+
        c (Fin.last (2*t+2)) • liftForm u v^(2*(t+1))=0 := by
      simpa only [polynomial_sum_smul,c₀,p] using hc2
    have hlast : c (Fin.last (2*t+2))=0 := by
      have he := congrArg (MvPolynomial.eval ![h,d]) hc'
      simpa [MvPolynomial.smul_eq_C_mul,hu,mul_comm d h] using he
    have hrem : kernelForm h d*(X 1*p+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1))=0 := by
      rw [hlast,zero_smul,add_zero] at hc'
      simp only [MvPolynomial.smul_eq_C_mul] at hc'
      linear_combination hc'
    have hrem' : X (R := ℂ) 1*p+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1)=0 :=
      (mul_eq_zero.mp hrem).resolve_left (kernelForm_ne_zero h d u v hu)
    have hpen : c (Fin.last (2*t+1)).castSucc=0 := by
      have he := congrArg (MvPolynomial.eval ![1,0]) hrem'
      simpa using he
    have hp : p=0 := by
      rw [hpen,map_zero,zero_mul,add_zero] at hrem'
      exact (mul_eq_zero.mp hrem').resolve_left (X_ne_zero 1)
    have hold : ∀ k,c₀ k=0 := ih c₀ hp
    refine Fin.lastCases hlast (fun j ↦ ?_) k
    exact Fin.lastCases hpen (fun l ↦ hold l) j

def adaptedMatrix (h d u v : ℂ) (t : ℕ) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  fun a b ↦ coefficients (2*t) (adaptedPolynomials h d u v t b) a
lemma adaptedMatrix_columns (h d u v : ℂ) (t : ℕ) (k : Fin (2*t+1)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).col k)=adaptedPolynomials h d u v t k :=
  polynomial_coefficients (adaptedPolynomials_homogeneous h d u v t k)
lemma adaptedMatrix_independent (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    LinearIndependent ℂ (adaptedMatrix h d u v t).col := by
  let f : Form (R := ℂ) (2*t) →ₗ[ℂ] Poly (R := ℂ) :=
    (homogeneousSubmodule (Fin 2) ℂ (2*t)).subtype.comp (equivHomogeneous (R := ℂ) (2*t)).toLinearMap
  have he : (fun k ↦ f ((adaptedMatrix h d u v t).col k))=adaptedPolynomials h d u v t :=
    funext (adaptedMatrix_columns h d u v t)
  apply LinearIndependent.of_comp f
  change LinearIndependent ℂ (fun k ↦ f ((adaptedMatrix h d u v t).col k))
  rw [he]
  exact adaptedPolynomials_independent h d u v hu t
lemma adaptedMatrix_isUnit (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    IsUnit (adaptedMatrix h d u v t) := by
  rw [← Matrix.mulVec_injective_iff_isUnit,Matrix.mulVec_injective_iff]
  exact adaptedMatrix_independent h d u v hu t

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def substitute (T : Matrix (Fin 2) (Fin 2) ℂ) : Poly (R := ℂ) →ₐ[ℂ] Poly (R := ℂ) :=
  MvPolynomial.aeval (fun b ↦ ∑ a : Fin 2,C (T a b)*X a)
@[simp] lemma substitute_X (T : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 2) :
    substitute T (X b)=∑ a : Fin 2,C (T a b)*X a := by simp [substitute]
@[simp] lemma substitute_C (T : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    substitute T (C c)=C c := by simp [substitute]
lemma substitute_comp (T U : Matrix (Fin 2) (Fin 2) ℂ) (p : Poly (R := ℂ)) :
    substitute T (substitute U p)=substitute (T*U) p := by
  have he : (substitute T).comp (substitute U)=substitute (T*U) := by
    apply MvPolynomial.algHom_ext
    intro b
    simp only [AlgHom.comp_apply,substitute_X,map_sum,map_mul,substitute_C,
      Matrix.mul_apply,map_sum,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  exact DFunLike.congr_fun he p
@[simp] lemma substitute_one (p : Poly (R := ℂ)) : substitute 1 p=p := by
  have he : substitute 1=AlgHom.id ℂ (Poly (R := ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro b
    simp [Matrix.one_apply]
  exact DFunLike.congr_fun he p
lemma substitute_homogeneous (T : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous n) : (substitute T p).IsHomogeneous n := by
  rw [← polynomial_coefficients hp]
  unfold polynomial
  rw [map_sum]
  apply IsHomogeneous.sum
  intro k _
  have hh : ∀ b : Fin 2,(substitute T (X b)).IsHomogeneous 1 := by
    intro b
    rw [substitute_X]
    apply IsHomogeneous.sum
    intro a _
    exact isHomogeneous_C_mul_X (T a b) a
  have hm : monomial (exponent n k) (coefficients n p k)=
      C (coefficients n p k)*X 0^k.val*X 1^(n-k.val) := by
    unfold exponent
    rw [monomial_add_single,← C_mul_X_pow_eq_monomial]
  rw [hm,map_mul,map_mul,map_pow,map_pow,substitute_C]
  convert ((isHomogeneous_C _ _).mul ((hh 0).pow k.val)).mul ((hh 1).pow (n-k.val)) using 1;
    simp only [one_mul,zero_add,Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)]

lemma polynomial_linearCombination {ι : Type u4} [Fintype ι] (n : ℕ)
    (c : ι → ℂ) (a : ι → Form (R := ℂ) n) :
    polynomial n (∑ i,c i • a i)=∑ i,c i • polynomial n (a i) := by
  change ((equivHomogeneous (R := ℂ) n) (∑ i,c i • a i)).val=_
  rw [map_sum]
  simp only [AddSubmonoidClass.coe_finsetSum,map_smul,SetLike.val_smul]
  rfl

lemma polynomial_mulVec (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (a : Form (R := ℂ) n) :
    polynomial n (T.mulVec a)=∑ k,a k • polynomial n (T.col k) := by
  rw [← polynomial_linearCombination]
  congr 1
  ext j
  simp only [mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,col,transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

def symmetricMatrix (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun a b ↦ coefficients n (substitute T (monomial (exponent n b) 1)) a
lemma polynomial_symmetricMatrix_col (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin (n+1)) :
    polynomial n ((symmetricMatrix n T).col b)=substitute T (monomial (exponent n b) 1) := by
  exact polynomial_coefficients (substitute_homogeneous T (isHomogeneous_monomial _ (exponent_degree n b)))
lemma polynomial_symmetricMatrix (n : ℕ) (T : Matrix (Fin 2) (Fin 2) ℂ) (a : Form (R := ℂ) n) :
    polynomial n ((symmetricMatrix n T).mulVec a)=substitute T (polynomial n a) := by
  rw [polynomial_mulVec]
  simp_rw [polynomial_symmetricMatrix_col]
  unfold polynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← map_smul]
  simp only [smul_monomial,smul_eq_mul,mul_one]
lemma symmetricMatrix_mul (n : ℕ) (T U : Matrix (Fin 2) (Fin 2) ℂ) :
    symmetricMatrix n (T*U)=symmetricMatrix n T*symmetricMatrix n U := by
  apply Matrix.ext_of_mulVec_single
  intro b
  apply polynomial_injective n
  rw [← mulVec_mulVec,polynomial_symmetricMatrix,polynomial_symmetricMatrix,polynomial_symmetricMatrix,
    substitute_comp]
@[simp] lemma symmetricMatrix_one (n : ℕ) : symmetricMatrix n (1 : Matrix (Fin 2) (Fin 2) ℂ)=1 := by
  apply Matrix.ext_of_mulVec_single
  intro b
  apply polynomial_injective n
  simp only [polynomial_symmetricMatrix,substitute_one,one_mulVec]
lemma eval_substitute (T : Matrix (Fin 2) (Fin 2) ℂ) (p : Poly (R := ℂ)) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (substitute T p)=MvPolynomial.eval (T.transpose.mulVec v) p := by
  change (MvPolynomial.eval v).comp (substitute T).toRingHom p=_
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro b; fin_cases b <;> simp
end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

lemma adaptedMatrix_det_unit (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ) :
    IsUnit (adaptedMatrix h d u v t).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (adaptedMatrix_isUnit h d u v hu t)

lemma polynomial_adapted_mulVec (h d u v : ℂ) (t : ℕ) (c : Form (R := ℂ) (2*t)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).mulVec c)=
      ∑ k,c k • adaptedPolynomials h d u v t k := by
  rw [polynomial_mulVec]
  simp_rw [adaptedMatrix_columns]

lemma adapted_combination_succ (h d u v : ℂ) (t : ℕ) (c : Form (R := ℂ) (2*(t+1))) :
    polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=
      kernelForm h d*X 1*polynomial (2*t) ((adaptedMatrix h d u v t).mulVec
        (fun k ↦ c k.castSucc.castSucc))+
      c (Fin.last (2*t+1)).castSucc • (kernelForm h d*X 0^(2*t+1))+
      c (Fin.last (2*t+2)) • liftForm u v^(2*(t+1)) := by
  rw [polynomial_adapted_mulVec,polynomial_adapted_mulVec]
  simp only [adaptedPolynomials]
  exact (sum_snoc_two (n:=2*t+1) c _ _ _).trans (by rw [polynomial_sum_smul])

lemma eval_adapted_combination (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    (c : Form (R := ℂ) (2*(t+1))) :
    MvPolynomial.eval ![h,d] (polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c))=
      c (Fin.last (2*t+2)) := by
  rw [adapted_combination_succ]
  simp [MvPolynomial.smul_eq_C_mul,hu,mul_comm d h]

def adaptedCoordinates (h d u v : ℂ) (t : ℕ) (p : Poly (R := ℂ)) : Form (R := ℂ) (2*t) :=
  (adaptedMatrix h d u v t)⁻¹.mulVec (coefficients (2*t) p)
lemma adaptedCoordinates_smul (h d u v : ℂ) (t : ℕ) (c : ℂ) (p : Poly (R := ℂ)) :
    adaptedCoordinates h d u v t (c • p)=c • adaptedCoordinates h d u v t p := by
  unfold adaptedCoordinates
  rw [coefficients_smul,Matrix.mulVec_smul]

lemma polynomial_adaptedCoordinates (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t)) :
    polynomial (2*t) ((adaptedMatrix h d u v t).mulVec (adaptedCoordinates h d u v t p))=p := by
  rw [adaptedCoordinates,mulVec_mulVec,Matrix.mul_nonsing_inv _ (adaptedMatrix_det_unit h d u v hu t),one_mulVec]
  exact polynomial_coefficients hp
lemma adaptedCoordinates_combination (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    (c : Form (R := ℂ) (2*t)) :
    adaptedCoordinates h d u v t (polynomial (2*t) ((adaptedMatrix h d u v t).mulVec c))=c := by
  rw [adaptedCoordinates,coefficients_polynomial,mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (adaptedMatrix_det_unit h d u v hu t),one_mulVec]
lemma adaptedCoordinates_last (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*(t+1))) :
    adaptedCoordinates h d u v (t+1) p (Fin.last (2*t+2))=MvPolynomial.eval ![h,d] p := by
  rw [← polynomial_adaptedCoordinates h d u v hu (t+1) hp,
    eval_adapted_combination h d u v hu t,adaptedCoordinates_combination h d u v hu]

lemma adaptedCoordinates_residual (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t)) :
    adaptedCoordinates h d u v (t+1) (kernelForm h d*X 1*p)=
      Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) (adaptedCoordinates h d u v t p) 0) 0 := by
  let c : Form (R := ℂ) (2*(t+1)) := Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) (adaptedCoordinates h d u v t p) 0) (0 : ℂ)
  have he : polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=kernelForm h d*X 1*p := by
    rw [adapted_combination_succ]
    simp only [c,Fin.snoc_last,Fin.snoc_castSucc,zero_smul,add_zero]
    rw [polynomial_adaptedCoordinates h d u v hu t hp]
  rw [← he,adaptedCoordinates_combination h d u v hu]

lemma adaptedCoordinates_penultimate (h d u v : ℂ) (hu : u*h+v*d=1) (t : ℕ)
    {p : Poly (R := ℂ)} (hp : p.IsHomogeneous (2*t+1)) :
    adaptedCoordinates h d u v (t+1) (kernelForm h d*p) (Fin.last (2*t+1)).castSucc=
      MvPolynomial.eval ![1,0] p := by
  have hhp : (kernelForm h d*p).IsHomogeneous (2*(t+1)) := by
    convert (kernelForm_homogeneous h d).mul hp using 1; omega
  let c := adaptedCoordinates h d u v (t+1) (kernelForm h d*p)
  have hc0 : c (Fin.last (2*t+2))=0 := by
    change adaptedCoordinates h d u v (t+1) (kernelForm h d*p) (Fin.last (2*t+2))=0
    rw [adaptedCoordinates_last h d u v hu t hhp]
    simp [mul_comm d h]
  have he := polynomial_adaptedCoordinates h d u v hu (t+1) hhp
  change polynomial (2*(t+1)) ((adaptedMatrix h d u v (t+1)).mulVec c)=kernelForm h d*p at he
  rw [adapted_combination_succ,hc0,zero_smul,add_zero,MvPolynomial.smul_eq_C_mul] at he
  have he' : kernelForm h d*(X 1*polynomial (2*t) ((adaptedMatrix h d u v t).mulVec
      (fun k ↦ c k.castSucc.castSucc))+C (c (Fin.last (2*t+1)).castSucc)*X 0^(2*t+1))=
        kernelForm h d*p := by linear_combination he
  have he'' := mul_left_cancel₀ (kernelForm_ne_zero h d u v hu) he'
  have hev := congrArg (MvPolynomial.eval ![1,0]) he''
  simpa using hev
end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section
structure FlagFrame where
  h : ℂ
  d : ℂ
  u : ℂ
  v : ℂ
  bezout : u*h+v*d=1
namespace FlagFrame
def matrix (F : FlagFrame) (t : ℕ) := adaptedMatrix F.h F.d F.u F.v t
def column (F : FlagFrame) (t : ℕ) := adaptedPolynomials F.h F.d F.u F.v t
def coords (F : FlagFrame) (t : ℕ) := adaptedCoordinates F.h F.d F.u F.v t
lemma det_unit (F : FlagFrame) (t : ℕ) : IsUnit (F.matrix t).det :=
  adaptedMatrix_det_unit F.h F.d F.u F.v F.bezout t
end FlagFrame

structure FlagChange (F G : FlagFrame) where
  T : Matrix (Fin 2) (Fin 2) ℂ
  kernel : ℂ
  bottom : ℂ
  top : ℂ
  quotient : ℂ
  kernel_change : substitute T (kernelForm G.h G.d)=C kernel*kernelForm F.h F.d
  bottom_change : substitute T (X 1)=C bottom*X 1
  top_projection : MvPolynomial.eval ![1,0] (substitute T (X 0))=top
  lift_quotient : MvPolynomial.eval ![F.h,F.d] (substitute T (liftForm G.u G.v))=quotient
namespace FlagChange
variable {F G : FlagFrame} (H : FlagChange F G)
def matrix (t : ℕ) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  (F.matrix t)⁻¹*symmetricMatrix (2*t) H.T*G.matrix t
lemma matrix_col (t : ℕ) (b : Fin (2*t+1)) :
    (H.matrix t).col b=F.coords t (substitute H.T (G.column t b)) := by
  have hcol {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
      (A*B).col b=A.mulVec (B.col b) := rfl
  unfold matrix FlagFrame.coords adaptedCoordinates
  rw [hcol,← mulVec_mulVec]
  congr 1
  have hh := congrArg (coefficients (2*t))
    (polynomial_symmetricMatrix (2*t) H.T ((G.matrix t).col b))
  rw [coefficients_polynomial] at hh
  exact hh.trans (congrArg (coefficients (2*t) ∘ substitute H.T)
    (adaptedMatrix_columns G.h G.d G.u G.v t b))
lemma matrix_entry (t : ℕ) (a b : Fin (2*t+1)) :
    H.matrix t a b=F.coords t (substitute H.T (G.column t b)) a :=
  congrFun (H.matrix_col t b) a
lemma matrix_column_residual (t : ℕ) (b : Fin (2*t+1)) :
    (H.matrix (t+1)).col b.castSucc.castSucc=
      (H.kernel*H.bottom) • Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1) ((H.matrix t).col b) 0) 0 := by
  rw [H.matrix_col]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc]
  rw [map_mul,map_mul,H.kernel_change,H.bottom_change]
  have he : C H.kernel*kernelForm F.h F.d*(C H.bottom*X 1)*substitute H.T (G.column t b)=
      (H.kernel*H.bottom) • (kernelForm F.h F.d*X 1*substitute H.T (G.column t b)) := by
    rw [MvPolynomial.smul_eq_C_mul,map_mul]; ring
  dsimp only [FlagFrame.column] at he
  rw [he,FlagFrame.coords,adaptedCoordinates_smul,
    adaptedCoordinates_residual F.h F.d F.u F.v F.bezout t
      (substitute_homogeneous H.T (adaptedPolynomials_homogeneous G.h G.d G.u G.v t b))]
  rw [H.matrix_col]
  rfl

lemma matrix_pen_last (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+2)) (Fin.last (2*t+1)).castSucc=0 := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last]
  change adaptedCoordinates F.h F.d F.u F.v (t+1)
    (substitute H.T (kernelForm G.h G.d*X 0^(2*t+1))) _=0
  have hp : (kernelForm G.h G.d*X 0^(2*t+1)).IsHomogeneous (2*(t+1)) := by
    convert (kernelForm_homogeneous G.h G.d).mul (isHomogeneous_X_pow (R:=ℂ) 0 (2*t+1)) using 1; omega
  rw [adaptedCoordinates_last F.h F.d F.u F.v F.bezout t (substitute_homogeneous H.T hp)]
  rw [map_mul,H.kernel_change]
  simp [mul_comm F.d F.h]
lemma matrix_pen_diag (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+1)).castSucc (Fin.last (2*t+1)).castSucc=
      H.kernel*H.top^(2*t+1) := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last]
  rw [map_mul,H.kernel_change,map_pow]
  have he : C H.kernel*kernelForm F.h F.d*(substitute H.T (X 0))^(2*t+1)=
      kernelForm F.h F.d*(C H.kernel*(substitute H.T (X 0))^(2*t+1)) := by ring
  rw [he,FlagFrame.coords,adaptedCoordinates_penultimate F.h F.d F.u F.v F.bezout t]
  · simp only [map_mul,eval_C,map_pow,H.top_projection]
  · have hh := substitute_homogeneous H.T (isHomogeneous_X_pow (R:=ℂ) 0 (2*t+1))
    simpa only [map_pow] using hh.C_mul H.kernel
lemma matrix_last_diag (t : ℕ) :
    H.matrix (t+1) (Fin.last (2*t+2)) (Fin.last (2*t+2))=H.quotient^(2*(t+1)) := by
  rw [H.matrix_entry]
  simp only [FlagFrame.column,adaptedPolynomials,Fin.snoc_last]
  rw [FlagFrame.coords,adaptedCoordinates_last F.h F.d F.u F.v F.bezout t
    (substitute_homogeneous H.T (by simpa only [one_mul] using
      (liftForm_homogeneous G.u G.v).pow (2*(t+1))))]
  rw [map_pow,map_pow,H.lift_quotient]

def graded : (t : ℕ) → Fin (2*t+1) → ℂ
  | 0 => fun _ ↦ 1
  | t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (fun k ↦ (H.kernel*H.bottom)*graded t k) (H.kernel*H.top^(2*t+1))) (H.quotient^(2*(t+1)))
lemma matrix_zero : H.matrix 0=1 := by
  ext a b
  have ha : a=0 := Fin.ext (by omega)
  have hb : b=0 := Fin.ext (by omega)
  subst a; subst b
  rw [H.matrix_entry]
  change adaptedCoordinates F.h F.d F.u F.v 0 (substitute H.T 1) 0=1
  simp only [map_one]
  have he : (1 : Poly (R := ℂ))=polynomial 0 ((adaptedMatrix F.h F.d F.u F.v 0).mulVec (fun _ ↦ 1)) := by
    rw [polynomial_adapted_mulVec F.h F.d F.u F.v 0 (fun _ ↦ 1)]
    simp [adaptedPolynomials]
  rw [he,adaptedCoordinates_combination F.h F.d F.u F.v F.bezout]
lemma triangular_diagonal (t : ℕ) :
    (∀ a b : Fin (2*t+1),b<a → H.matrix t a b=0) ∧
    (∀ a : Fin (2*t+1),H.matrix t a a=H.graded t a) := by
  induction t with
  | zero =>
    constructor
    · intro a b h; have := a.isLt; have := b.isLt; omega
    · intro a; rw [H.matrix_zero]; simp [graded]
  | succ t ih =>
    have he (a : Fin (2*(t+1)+1)) (b : Fin (2*t+1)) := congrFun (H.matrix_column_residual t b) a
    constructor
    · intro a b hb
      revert hb
      refine Fin.lastCases (n:=2*t+2) (fun hb ↦ ?_) (fun b hb ↦ ?_) b
      · exact False.elim (by have := a.isLt; simp only [Fin.lt_def,Fin.val_last] at hb; omega)
      · revert hb
        refine Fin.lastCases (n:=2*t+1) (fun hb ↦ ?_) (fun b hb ↦ ?_) b
        · have ha : a=Fin.last (2*t+2) := Fin.ext (by
            have := a.isLt
            simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_last] at hb ⊢
            omega)
          subst a
          exact H.matrix_pen_last t
        · revert hb
          refine Fin.lastCases (n:=2*t+2) (fun _ ↦ ?_) (fun a hb ↦ ?_) a
          · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_last,mul_zero] using he (Fin.last (2*t+2)) b
          · revert hb
            refine Fin.lastCases (n:=2*t+1) (fun _ ↦ ?_) (fun a hb ↦ ?_) a
            · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,Fin.snoc_last,mul_zero]
                using he (Fin.last (2*t+1)).castSucc b
            · have hab : b<a := by exact hb
              simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,ih.1 a b hab,mul_zero]
                using he a.castSucc.castSucc b
    · intro a
      refine Fin.lastCases (n:=2*t+2) ?_ (fun a ↦ ?_) a
      · simpa only [graded,Fin.snoc_last] using H.matrix_last_diag t
      · refine Fin.lastCases (n:=2*t+1) ?_ (fun a ↦ ?_) a
        · simpa only [graded,Fin.snoc_castSucc,Fin.snoc_last] using H.matrix_pen_diag t
        · simpa only [Matrix.col_apply,Pi.smul_apply,smul_eq_mul,Fin.snoc_castSucc,graded,ih.2 a]
            using he a.castSucc.castSucc a
end FlagChange
end
end QuadricCounterexample.BinaryForms

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.LaurentCech
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample.LaurentCech
open Finset
open scoped Classical
noncomputable section
abbrev Chart := Fin 2 × Fin 2
abbrev Exponent := ℤ × ℤ
abbrev LaurentCoefficients := Exponent →₀ ℂ

def ScalarAllows (d : ℕ) (i : Fin 2) (e : ℤ) : Prop :=
  if i=0 then e≤d else 0≤e

def ChartAllows (d : ℕ × ℕ) (i : Chart) (e : Exponent) : Prop :=
  ScalarAllows d.1 i.1 e.1 ∧ ScalarAllows d.2 i.2 e.2

def OverlapAllows (d : ℕ × ℕ) (i j : Chart) (e : Exponent) : Prop :=
  (i.1=j.1 → ScalarAllows d.1 i.1 e.1) ∧
  (i.2=j.2 → ScalarAllows d.2 i.2 e.2)

lemma scalar_bad_unique (d : ℕ) {i j : Fin 2} {e : ℤ}
    (hi : ¬ScalarAllows d i e) (hj : ¬ScalarAllows d j e) : i=j := by
  fin_cases i <;> fin_cases j <;> simp_all [ScalarAllows] <;> omega

lemma forbidden_coefficient_zero (d : ℕ × ℕ) (p : Chart → Chart → LaurentCoefficients)
    (hc : ∀ i j k, p i j+p j k=p i k)
    (hs : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0)
    (i j : Chart) (e : Exponent) (hi : ¬ChartAllows d i e) (hj : ¬ChartAllows d j e) :
    p i j e=0 := by
  rcases not_and_or.mp hi with hi | hi <;> rcases not_and_or.mp hj with hj | hj
  · have he := scalar_bad_unique d.1 hi hj
    exact hs i j e (fun h ↦ hi (h.1 he))
  · let k : Chart := (i.1,j.2)
    have h1 : p i k e=0 := hs i k e (fun h ↦ hi (h.1 rfl))
    have h2 : p k j e=0 := hs k j e (fun h ↦ hj (h.2 rfl))
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc i k j)
    simpa only [Finsupp.add_apply,h1,h2,zero_add] using he.symm
  · let k : Chart := (j.1,i.2)
    have h1 : p i k e=0 := hs i k e (fun h ↦ hi (h.2 rfl))
    have h2 : p k j e=0 := hs k j e (fun h ↦ hj (h.1 rfl))
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc i k j)
    simpa only [Finsupp.add_apply,h1,h2,zero_add] using he.symm
  · have he := scalar_bad_unique d.2 hi hj
    exact hs i j e (fun h ↦ hi (h.2 he))

def badChart (d : ℕ × ℕ) (e : Exponent) : Chart :=
  if h : ∃ i, ¬ChartAllows d i e then h.choose else (0,0)

lemma badChart_bad (d : ℕ × ℕ) (e : Exponent) (h : ∃ i, ¬ChartAllows d i e) :
    ¬ChartAllows d (badChart d e) e := by
  simpa only [badChart,dite_eq_left h] using h.choose_spec

def correction (d : ℕ × ℕ) (q : Chart → LaurentCoefficients) : LaurentCoefficients :=
  ∑ i : Chart, (q i).filter (fun e ↦ badChart d e=i)

lemma correction_apply (d : ℕ × ℕ) (q : Chart → LaurentCoefficients) (e : Exponent) :
    correction d q e=q (badChart d e) e := by
  simp only [correction,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.filter_apply]
  rw [Finset.sum_eq_single (badChart d e)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem split_cocycle (d : ℕ × ℕ) (p : Chart → Chart → LaurentCoefficients)
    (hc : ∀ i j k, p i j+p j k=p i k)
    (hs : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0) :
    ∃ q : Chart → LaurentCoefficients,
      (∀ i e, ¬ChartAllows d i e → q i e=0) ∧
      ∀ i j, p i j=q j-q i := by
  let q₀ : Chart → LaurentCoefficients := fun i ↦ p (0,0) i
  let c := correction d q₀
  refine ⟨fun i ↦ q₀ i-c,?_,?_⟩
  · intro i e hi
    have hb := badChart_bad d e ⟨i,hi⟩
    have hij := forbidden_coefficient_zero d p hc hs (badChart d e) i e hb hi
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc (0,0) (badChart d e) i)
    simp only [Finsupp.add_apply,hij,add_zero] at he
    simp only [Finsupp.sub_apply,c,correction_apply,q₀]
    exact sub_eq_zero.mpr he.symm
  · intro i j
    have h := hc (0,0) i j
    dsimp only [q₀]
    rw [← h]
    abel

end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set MvPolynomial Finsupp
open scoped BigOperators
noncomputable section

def eval (p : LaurentCoefficients) (z : BaseCoordinates) : ℂ :=
  p.sum fun e c ↦ c * z.1^e.1 * z.2^e.2
lemma eval_add (p q : LaurentCoefficients) (z : BaseCoordinates) :
    eval (p+q) z=eval p z+eval q z := by
  apply Finsupp.sum_add_index <;> intros <;> ring
lemma eval_sub (p q : LaurentCoefficients) (z : BaseCoordinates) :
    eval (p-q) z=eval p z-eval q z := by
  have h := eval_add (p-q) q z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
lemma eval_single (e : Exponent) (c : ℂ) (z : BaseCoordinates) :
    eval (Finsupp.single e c) z=c*z.1^e.1*z.2^e.2 := by simp [eval]

def exponent (d : Fin 2 →₀ ℕ) : Exponent := (d 0,d 1)
def ofPolynomial (p : BasePolynomial) : LaurentCoefficients :=
  Finsupp.mapDomain exponent (AddMonoidAlgebra.coeff p)
lemma ofPolynomial_add (p q : BasePolynomial) : ofPolynomial (p+q)=ofPolynomial p+ofPolynomial q :=
  by simp [ofPolynomial,AddMonoidAlgebra.coeff_add,Finsupp.mapDomain_add]
lemma ofPolynomial_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    ofPolynomial (MvPolynomial.monomial d c)=Finsupp.single (exponent d) c :=
  by simp [ofPolynomial, MvPolynomial.monomial,AddMonoidAlgebra.lsingle_apply]
lemma eval_ofPolynomial (p : BasePolynomial) (z : BaseCoordinates) :
    eval (ofPolynomial p) z=baseEval p z := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [ofPolynomial_add,eval_add,baseEval_add,hp,hq]
  | monomial d c =>
    rw [ofPolynomial_monomial,eval_single]
    simp only [baseEval,MvPolynomial.eval_monomial,exponent,zpow_natCast]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]; ring
    · intro i; simp

def shift (e : Exponent) (p : LaurentCoefficients) : LaurentCoefficients :=
  Finsupp.mapDomain (fun a ↦ e+a) p
lemma shift_injective (e : Exponent) : Function.Injective (shift e) :=
  Finsupp.mapDomain_injective (fun _ _ h ↦ add_left_cancel h)
lemma eval_shift (e : Exponent) (p : LaurentCoefficients) {z : BaseCoordinates}
    (hz : z.1≠0 ∧ z.2≠0) :
    eval (shift e p) z=z.1^e.1*z.2^e.2*eval p z := by
  unfold eval shift
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro a c
  simp only [Prod.fst_add,Prod.snd_add,zpow_add₀ hz.1,zpow_add₀ hz.2]
  ring

lemma exists_shift_nonneg (p : LaurentCoefficients) :
    ∃ e : Exponent, ∀ a∈(shift e p).support, 0≤a.1 ∧ 0≤a.2 := by
  have h (a : Exponent) : ∃ n : ℕ, -a.1≤n ∧ -a.2≤n := by
    obtain ⟨n,hn⟩ := exists_nat_ge (max (-a.1) (-a.2))
    exact ⟨n,le_trans (le_max_left _ _) hn,le_trans (le_max_right _ _) hn⟩
  choose n hn using h
  let N : ℕ := ∑ a∈p.support, n a
  refine ⟨(N,N),?_⟩
  intro a ha
  have hs : a∈Finset.image (fun a : Exponent ↦ ((N : ℤ),(N : ℤ))+a) p.support :=
    Finsupp.mapDomain_support ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
  have hn' : (n b : ℤ)≤N := by exact_mod_cast Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hb
  simp only [Prod.fst_add,Prod.snd_add]
  constructor <;> linarith [(hn b).1,(hn b).2]

def naturalExponent (a : Exponent) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.1.toNat,a.2.toNat]
def toPolynomial (p : LaurentCoefficients) : BasePolynomial :=
  p.sum fun a c ↦ MvPolynomial.monomial (naturalExponent a) c
lemma ofPolynomial_toPolynomial (p : LaurentCoefficients)
    (hp : ∀ a∈p.support, 0≤a.1 ∧ 0≤a.2) :
    ofPolynomial (toPolynomial p)=p := by
  have hm : ofPolynomial (toPolynomial p)=p.sum (fun a c ↦ Finsupp.single (exponent (naturalExponent a)) c) := by
    unfold toPolynomial
    unfold Finsupp.sum
    induction p.support using Finset.induction_on with
    | empty => simp [ofPolynomial]
    | @insert a t hat ih => simp only [Finset.sum_insert hat,ofPolynomial_add,ofPolynomial_monomial,ih]
  rw [hm]
  conv_rhs => rw [← Finsupp.sum_single p]
  apply Finsupp.sum_congr
  intro a ha
  congr 1
  ext <;> simp [exponent,naturalExponent,Int.toNat_of_nonneg (hp a ha).1,
    Int.toNat_of_nonneg (hp a ha).2]

end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set
noncomputable section
lemma baseEval_on_torus_injective {p q : BasePolynomial}
    (he : ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 → baseEval p z=baseEval q z) : p=q := by
  have hd : Dense ({(0 : ℂ)}ᶜ ×ˢ {(0 : ℂ)}ᶜ) :=
    (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))
  have hc (r : BasePolynomial) : Continuous (baseEval r) :=
    continuousOn_univ.mp (analytic_baseEval r).continuousOn
  have hfun : baseEval p=baseEval q := Continuous.ext_on hd (hc p) (hc q) (fun z hz ↦ he z hz)
  apply MvPolynomial.funext
  intro x
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  exact congrFun hfun (x 0,x 1)

lemma eval_injective_on_torus {p q : LaurentCoefficients}
    (he : ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 → eval p z=eval q z) : p=q := by
  obtain ⟨e,hs⟩ := exists_shift_nonneg (p-q)
  let r := toPolynomial (shift e (p-q))
  have hr : ofPolynomial r=shift e (p-q) := ofPolynomial_toPolynomial _ hs
  have hr0 : r=0 := by
    apply baseEval_on_torus_injective
    intro z hz
    rw [← eval_ofPolynomial,hr,eval_shift e (p-q) hz,eval_sub]
    rw [he z hz]
    simp
  apply sub_eq_zero.mp
  apply shift_injective e
  rw [← hr,hr0]
  simp [ofPolynomial,shift]
end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set Finsupp
open scoped BigOperators
noncomputable section

def transformExponent (d : ℕ × ℕ) (i : Chart) (a : Exponent) : Exponent :=
  (if i.1=0 then (d.1 : ℤ)-a.1 else a.1,
   if i.2=0 then (d.2 : ℤ)-a.2 else a.2)
lemma transformExponent_involutive (d : ℕ × ℕ) (i : Chart) :
    Function.Involutive (transformExponent d i) := by
  intro a
  ext <;> simp [transformExponent] <;> split_ifs <;> simp_all

def transform (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients) : LaurentCoefficients :=
  Finsupp.mapDomain (transformExponent d i) p
lemma transform_involutive (d : ℕ × ℕ) (i : Chart) : Function.Involutive (transform d i) := by
  intro p
  unfold transform
  rw [← Finsupp.mapDomain_comp]
  have h : transformExponent d i ∘ transformExponent d i=id := funext (transformExponent_involutive d i)
  rw [h,Finsupp.mapDomain_id]

lemma exponent_nonneg (a : Fin 2 →₀ ℕ) : 0≤(exponent a).1 ∧ 0≤(exponent a).2 := by
  exact ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩
lemma ofPolynomial_nonneg (p : BasePolynomial) {a : Exponent} (ha : a∈(ofPolynomial p).support) :
    0≤a.1 ∧ 0≤a.2 := by
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact exponent_nonneg b
lemma chartAllows_transform_iff (d : ℕ × ℕ) (i : Chart) (a : Exponent) :
    ChartAllows d i (transformExponent d i a) ↔ 0≤a.1 ∧ 0≤a.2 := by
  simp only [ChartAllows, ScalarAllows,transformExponent]
  split_ifs <;> constructor <;> intro h <;> constructor <;> omega
lemma transform_nonneg_iff (d : ℕ × ℕ) (i : Chart) (a : Exponent) :
    0≤(transformExponent d i a).1 ∧ 0≤(transformExponent d i a).2 ↔ ChartAllows d i a := by
  have h := (chartAllows_transform_iff d i (transformExponent d i a)).symm
  rw [transformExponent_involutive d i a] at h
  exact h
lemma exists_polynomial_of_chartAllows (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients)
    (hp : ∀ a∈p.support, ChartAllows d i a) :
    ∃ q : BasePolynomial, transform d i (ofPolynomial q)=p := by
  have hnon : ∀ a∈(transform d i p).support, 0≤a.1 ∧ 0≤a.2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact (transform_nonneg_iff d i b).mpr (hp b hb)
  refine ⟨toPolynomial (transform d i p),?_⟩
  rw [ofPolynomial_toPolynomial _ hnon]
  exact transform_involutive d i p

def masterCoordinates (i : Chart) (z : BaseCoordinates) : BaseCoordinates :=
  (if i.1=0 then z.1⁻¹ else z.1, if i.2=0 then z.2⁻¹ else z.2)
def masterFrame (d : ℕ × ℕ) (i : Chart) (z : BaseCoordinates) : ℂ :=
  (if i.1=0 then z.1^d.1 else 1) * (if i.2=0 then z.2^d.2 else 1)
lemma masterCoordinates_nonzero (i : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    (masterCoordinates i z).1≠0 ∧ (masterCoordinates i z).2≠0 := by
  dsimp [masterCoordinates]
  split_ifs <;> exact ⟨by simpa using hz.1,by simpa using hz.2⟩
lemma masterCoordinates_involutive (i : Chart) : Function.Involutive (masterCoordinates i) := by
  intro z
  ext <;> simp [masterCoordinates] <;> split_ifs <;> simp_all

lemma scalar_transform_eval (d : ℕ) (i : Fin 2) (a : ℤ) {z : ℂ} (hz : z≠0) :
    z^(if i=0 then (d : ℤ)-a else a)=
      (if i=0 then z^d else 1)*(if i=0 then z⁻¹ else z)^a := by
  by_cases hi : i=0
  · simp only [hi,ite_true,zpow_sub₀ hz,zpow_natCast, inv_zpow,div_eq_mul_inv]
  · simp [hi]
lemma eval_transform (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients)
    {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    eval (transform d i p) z=masterFrame d i z*eval p (masterCoordinates i z) := by
  unfold eval transform
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro a ha
  simp only [transformExponent,masterFrame,masterCoordinates,
    scalar_transform_eval _ _ _ hz.1,scalar_transform_eval _ _ _ hz.2]
  ring
lemma eval_transform_polynomial (d : ℕ × ℕ) (i : Chart) (p : BasePolynomial)
    {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    eval (transform d i (ofPolynomial p)) z=masterFrame d i z*baseEval p (masterCoordinates i z) := by
  rw [eval_transform d i _ hz,eval_ofPolynomial]
end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample
open MvPolynomial Set
noncomputable section

lemma denominator_dvd_power (q r : BasePolynomial)
    (hq : ∀ z : BaseCoordinates, baseEval r z ≠ 0 → baseEval q z ≠ 0) :
    ∃ n : ℕ, q ∣ r^n := by
  let J : Ideal BasePolynomial := Ideal.span {q}
  have hv : r ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    have he : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
    have hqz : MvPolynomial.eval z q=0 := by
      rw [MvPolynomial.zeroLocus_span] at hz
      simpa only [aeval_eq_eval] using hz q (Set.mem_singleton q)
    by_contra hr
    apply hq (z 0,z 1)
    · simpa only [baseEval,← he,aeval_eq_eval] using hr
    · simpa only [baseEval,← he] using hqz
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n,hn⟩ := hv
  exact ⟨n,Ideal.mem_span_singleton.mp hn⟩

lemma UniformlyRegularOn.exists_power_denominator (r : BasePolynomial)
    {f : BaseCoordinates → ℂ} (hf : UniformlyRegularOn {z | baseEval r z ≠ 0} f) :
    ∃ n : ℕ, ∃ p : BasePolynomial, ∀ z, baseEval r z ≠ 0 →
      f z=baseEval p z/(baseEval r z)^n := by
  obtain ⟨p,q,hq,hf⟩ := hf
  obtain ⟨n,t,ht⟩ := denominator_dvd_power q r hq
  refine ⟨n,p*t,?_⟩
  intro z hz
  have hqe := hq z hz
  have he := congrArg (fun a : BasePolynomial ↦ baseEval a z) ht
  change baseEval (r^n) z=baseEval (q*t) z at he
  have hpw : baseEval (r^n) z=(baseEval r z)^n := by simp [baseEval]
  rw [hpw,baseEval_mul] at he
  rw [hf z hz,baseEval_mul]
  field_simp
  linear_combination baseEval p z * he

lemma UniformlyRegularOn.exists_polynomial {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn Set.univ f) : ∃ p : BasePolynomial, f=baseEval p := by
  have hr : {z : BaseCoordinates | baseEval (1 : BasePolynomial) z ≠ 0}=Set.univ := by ext; simp
  obtain ⟨n,p,hp⟩ := UniformlyRegularOn.exists_power_denominator 1 (by simpa only [hr] using hf)
  refine ⟨p,funext fun z ↦ ?_⟩
  simpa using hp z (by simp)

end
end QuadricCounterexample

namespace QuadricCounterexample.LaurentCech
open Set MvPolynomial Finsupp
open scoped BigOperators
noncomputable section

def inverseExponent (n : ℕ) (i j : Chart) : Exponent :=
  (if i.1=j.1 then 0 else -(n : ℤ),if i.2=j.2 then 0 else -(n : ℤ))
lemma eval_inverseExponent (n : ℕ) (i j : Chart) (z : BaseCoordinates) :
    z.1^(inverseExponent n i j).1*z.2^(inverseExponent n i j).2=
      ((baseEval (overlapPolynomial i j) z)^n)⁻¹ := by
  simp only [inverseExponent,overlapPolynomial,baseEval_mul]
  split_ifs <;> simp [baseEval,mul_pow,mul_comm]
lemma torus_mem_overlap (i j : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    z ∈ coordinateOverlap i j := (coordinateOverlap_iff i j z).mpr ⟨Or.inr hz.1,Or.inr hz.2⟩

lemma transform_overlap_support (d : ℕ × ℕ) (n : ℕ) (i j : Chart) (p : BasePolynomial)
    {a : Exponent} (ha : a∈(transform d i (shift (inverseExponent n i j) (ofPolynomial p))).support) :
    OverlapAllows d i j a := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hb)
  have hn := ofPolynomial_nonneg p hc
  constructor
  · intro hij
    dsimp [ScalarAllows,transformExponent,inverseExponent]
    simp only [hij,ite_true,zero_add]
    split_ifs <;> omega
  · intro hij
    dsimp [ScalarAllows,transformExponent,inverseExponent]
    simp only [hij,ite_true,zero_add]
    split_ifs <;> omega

lemma exists_overlap_laurent (d : ℕ × ℕ) (i j : Chart) (f : BaseCoordinates → ℂ)
    (hf : UniformlyRegularOn (coordinateOverlap i j) f) :
    ∃ p : LaurentCoefficients, (∀ a∈p.support,OverlapAllows d i j a) ∧
      ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 →
        eval p z=masterFrame d i z*f (masterCoordinates i z) := by
  obtain ⟨n,q,hq⟩ := UniformlyRegularOn.exists_power_denominator (overlapPolynomial i j) hf
  refine ⟨transform d i (shift (inverseExponent n i j) (ofPolynomial q)),
    fun _ ha ↦ transform_overlap_support d n i j q ha,?_⟩
  intro z hz
  have hw := masterCoordinates_nonzero i hz
  rw [eval_transform d i _ hz,eval_shift _ _ hw,eval_ofPolynomial,
    hq _ (torus_mem_overlap i j hw),eval_inverseExponent]
  ring

def lineFactor (d : ℕ × ℕ) (i j : Chart) (z : BaseCoordinates) : ℂ :=
  firstFactor i j z^d.1*secondFactor i j z^d.2
lemma lineFactor_regular (d : ℕ × ℕ) (i j : Chart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (lineFactor d i j) :=
  ((firstFactor_regular i j U).pow d.1).mul ((secondFactor_regular i j U).pow d.2)
lemma masterFrame_ne_zero (d : ℕ × ℕ) (i : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    masterFrame d i z≠0 := by
  dsimp [masterFrame]
  split_ifs <;> simp_all
lemma masterCoordinates_change (i j : Chart) (z : BaseCoordinates) :
    coordinateChange i j (masterCoordinates i z)=masterCoordinates j z := by
  rcases i with ⟨i1,i2⟩; rcases j with ⟨j1,j2⟩
  ext <;> simp only [coordinateChange,scalarCoordinateChange,masterCoordinates]
  · fin_cases i1 <;> fin_cases j1 <;> simp
  · fin_cases i2 <;> fin_cases j2 <;> simp
lemma masterFrame_change (d : ℕ × ℕ) (i j : Chart) {z : BaseCoordinates}
    (hz : z.1≠0 ∧ z.2≠0) :
    masterFrame d i z*lineFactor d i j (masterCoordinates i z)=masterFrame d j z := by
  have hs (n : ℕ) (a b : Fin 2) (w : ℂ) (hw : w≠0) :
      (if a=0 then w^n else 1)*
        (scalarFactor a b (if a=0 then w⁻¹ else w))^n=(if b=0 then w^n else 1) := by
    fin_cases a <;> fin_cases b <;> simp [scalarFactor,hw]
  dsimp only [masterFrame,lineFactor,firstFactor,secondFactor,masterCoordinates]
  calc
    _ = ((if i.1=0 then z.1^d.1 else 1)*
       (scalarFactor i.1 j.1 (if i.1=0 then z.1⁻¹ else z.1))^d.1)*
       ((if i.2=0 then z.2^d.2 else 1)*
       (scalarFactor i.2 j.2 (if i.2=0 then z.2⁻¹ else z.2))^d.2) := by ring
    _ = _ := by rw [hs d.1 i.1 j.1 z.1 hz.1,hs d.2 i.2 j.2 z.2 hz.2]

lemma uniformlyRegular_eq_of_torus {i j : Chart} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn (coordinateOverlap i j) f)
    (hg : UniformlyRegularOn (coordinateOverlap i j) g)
    (he : ∀ z : BaseCoordinates,z.1≠0 ∧ z.2≠0 → f z=g z) :
    EqOn f g (coordinateOverlap i j) := by
  let r : BasePolynomial := X 0*X 1
  have hr : r≠0 := mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)
  apply continuous_cancel_polynomial (coordinateOverlap_open i j)
    (hf.regular.analyticOnNhd (coordinateOverlap_open i j)).continuousOn
    (hg.regular.analyticOnNhd (coordinateOverlap_open i j)).continuousOn hr
  intro z _
  by_cases h : z.1≠0 ∧ z.2≠0
  · rw [he z h]
  · have ht : baseEval r z=0 := by simpa [r,baseEval,mul_eq_zero,not_and_or] using not_and_or.mp h
    simp [ht]

theorem split_regular_line_cocycle (d : ℕ × ℕ) (f : Chart → Chart → BaseCoordinates → ℂ)
    (hf : ∀ i j, UniformlyRegularOn (coordinateOverlap i j) (f i j))
    (hc : ∀ i j k z, z∈coordinateOverlap i j → z∈coordinateOverlap i k →
      f i j z+lineFactor d i j z*f j k (coordinateChange i j z)=f i k z) :
    ∃ q : Chart → BasePolynomial, ∀ i j z, z∈coordinateOverlap i j →
      f i j z=lineFactor d i j z*baseEval (q j) (coordinateChange i j z)-baseEval (q i) z := by
  choose p hp he using fun i j ↦ exists_overlap_laurent d i j (f i j) (hf i j)
  have pc : ∀ i j k,p i j+p j k=p i k := by
    intro i j k
    apply eval_injective_on_torus
    intro z hz
    rw [eval_add,he i j z hz,he j k z hz,he i k z hz]
    rw [← masterFrame_change d i j hz,mul_assoc,← mul_add]
    rw [← masterCoordinates_change i j z,hc i j k _
      (torus_mem_overlap i j (masterCoordinates_nonzero i hz))
      (torus_mem_overlap i k (masterCoordinates_nonzero i hz))]
  have ps : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0 := by
    intro i j e h
    by_contra hn
    exact h (hp i j e (Finsupp.mem_support_iff.mpr hn))
  obtain ⟨a,ha,hae⟩ := split_cocycle d p pc ps
  have ha' : ∀ i e,e∈(a i).support → ChartAllows d i e := by
    intro i e he
    by_contra h
    exact Finsupp.mem_support_iff.mp he (ha i e h)
  choose q hq using fun i ↦ exists_polynomial_of_chartAllows d i (a i) (ha' i)
  refine ⟨q,?_⟩
  intro i j
  apply uniformlyRegular_eq_of_torus (hf i j)
  · exact ((lineFactor_regular d i j _).mul ((uniformlyRegular_polynomial univ (q j)).comp
      (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j)
      (fun _ _ ↦ mem_univ _))).sub (uniformlyRegular_polynomial _ (q i))
  · intro z hz
    let w := masterCoordinates i z
    have hw := masterCoordinates_nonzero i hz
    have hm : masterCoordinates i w=z := masterCoordinates_involutive i z
    have ht := congrArg (fun s ↦ eval s w) (hae i j)
    rw [eval_sub,he i j w hw,← hq i,← hq j,
      eval_transform_polynomial d j _ hw,eval_transform_polynomial d i _ hw] at ht
    rw [← masterFrame_change d i j hw,← masterCoordinates_change i j w,hm] at ht
    apply (mul_left_cancel₀ (masterFrame_ne_zero d i hw))
    linear_combination ht
end
end QuadricCounterexample.LaurentCech

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TriangularSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

lemma UniformlyRegularOn.finset_sum {ι : Type u1} (s : Finset ι)
    {U : Set BaseCoordinates} {f : ι → BaseCoordinates → ℂ}
    (hf : ∀ i∈s,UniformlyRegularOn U (f i)) :
    UniformlyRegularOn U (fun z ↦ ∑ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using uniformlyRegular_const U 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))
lemma UniformlyRegularOn.fintype_sum {ι : Type u2} [Fintype ι]
    {U : Set BaseCoordinates} {f : ι → BaseCoordinates → ℂ}
    (hf : ∀ i,UniformlyRegularOn U (f i)) :
    UniformlyRegularOn U (fun z ↦ ∑ i,f i z) :=
  UniformlyRegularOn.finset_sum Finset.univ (fun i _ ↦ hf i)

namespace LaurentCech
lemma scalarFactor_mul_one_overlap (i j k : Fin 2) {z : ℂ} (hz : i=j ∨ z≠0) :
    scalarFactor i j z*scalarFactor j k (scalarCoordinateChange i j z)=scalarFactor i k z := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [scalarFactor,scalarCoordinateChange]
lemma lineFactor_mul_one_overlap (d : ℕ × ℕ) (i j k : Chart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor d i j z*lineFactor d j k (coordinateChange i j z)=lineFactor d i k z := by
  have h1 := scalarFactor_mul_one_overlap i.1 j.1 k.1 ((coordinateOverlap_iff i j z).mp hz).1
  have h2 := scalarFactor_mul_one_overlap i.2 j.2 k.2 ((coordinateOverlap_iff i j z).mp hz).2
  unfold lineFactor firstFactor secondFactor coordinateChange
  calc
    _ = (scalarFactor i.1 j.1 z.1*scalarFactor j.1 k.1 (scalarCoordinateChange i.1 j.1 z.1))^d.1*
      (scalarFactor i.2 j.2 z.2*scalarFactor j.2 k.2 (scalarCoordinateChange i.2 j.2 z.2))^d.2 := by
        simp only [mul_pow]; ring
    _ = _ := by rw [h1,h2]
@[simp] lemma lineFactor_self (d : ℕ × ℕ) (i : Chart) (z : BaseCoordinates) :
    lineFactor d i i z=1 := by simp [lineFactor,firstFactor,secondFactor,scalarFactor]

def lineGenerator (d : ℕ × ℕ) (anchor i : Chart) : BasePolynomial :=
  (if i.1=anchor.1 then 1 else X 0^d.1)*(if i.2=anchor.2 then 1 else X 1^d.2)
lemma eval_lineGenerator (d : ℕ × ℕ) (anchor i : Chart) (z : BaseCoordinates) :
    baseEval (lineGenerator d anchor i) z=lineFactor d i anchor z := by
  simp only [lineGenerator,lineFactor,firstFactor,secondFactor,scalarFactor,baseEval_mul]
  split_ifs <;> simp [baseEval]
lemma lineGenerator_compatible (d : ℕ × ℕ) (anchor i j : Chart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor d i j z*baseEval (lineGenerator d anchor j) (coordinateChange i j z)=
      baseEval (lineGenerator d anchor i) z := by
  simp only [eval_lineGenerator]
  exact lineFactor_mul_one_overlap d i j anchor hz
end LaurentCech

open LaurentCech

structure TriangularCechBundle (r : ℕ) where
  degree : Fin r → ℕ × ℕ
  matrix : Chart → Chart → BaseCoordinates → Matrix (Fin r) (Fin r) ℂ
  regular : ∀ i j a b,UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ matrix i j z a b)
  self : ∀ i z,matrix i i z=1
  cocycle : ∀ i j k z,z∈coordinateOverlap i j → z∈coordinateOverlap i k →
    matrix i j z*matrix j k (coordinateChange i j z)=matrix i k z
  triangular : ∀ i j z,z∈coordinateOverlap i j → ∀ a b,b<a → matrix i j z a b=0
  diagonal : ∀ i j z,z∈coordinateOverlap i j → ∀ a,matrix i j z a a=lineFactor (degree a) i j z

namespace TriangularCechBundle
variable {r : ℕ} (B : TriangularCechBundle r)
def polynomialValue (q : Chart → Fin r → BasePolynomial) (i : Chart) (z : BaseCoordinates) : Fin r → ℂ :=
  fun k ↦ baseEval (q i k) z

def delta (q : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) : Fin r → ℂ :=
  (B.matrix i j z).mulVec (polynomialValue q j (coordinateChange i j z))-polynomialValue q i z
lemma delta_regular (q : Chart → Fin r → BasePolynomial) (i j : Chart) (a : Fin r) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ B.delta q i j z a) := by
  apply UniformlyRegularOn.sub _ (uniformlyRegular_polynomial _ (q i a))
  change UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ ∑ b, B.matrix i j z a b*baseEval (q j b) (coordinateChange i j z))
  apply UniformlyRegularOn.fintype_sum
  intro b
  exact (B.regular i j a b).mul ((uniformlyRegular_polynomial univ (q j b)).comp
    (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j) (fun _ _ ↦ mem_univ _))
lemma delta_cocycle (q : Chart → Fin r → BasePolynomial) (i j k : Chart) {z : BaseCoordinates}
    (hj : z∈coordinateOverlap i j) (hk : z∈coordinateOverlap i k) :
    B.delta q i j z+(B.matrix i j z).mulVec (B.delta q j k (coordinateChange i j z))=B.delta q i k z := by
  unfold delta
  rw [mulVec_sub, mulVec_mulVec, B.cocycle i j k z hj hk,coordinateChange_comp i j k hj]
  abel
lemma delta_add (q p : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) :
    B.delta (q+p) i j z=B.delta q i j z+B.delta p i j z := by
  have hq (a : Chart) (w : BaseCoordinates) :
      polynomialValue (q+p) a w=polynomialValue q a w+polynomialValue p a w := by
    ext b; simp [polynomialValue]
  simp only [delta,hq,mulVec_add]
  abel
lemma delta_zero (i j : Chart) (z : BaseCoordinates) : B.delta 0 i j z=0 := by
  have h (i : Chart) (z : BaseCoordinates) : polynomialValue (0 : Chart → Fin r → BasePolynomial) i z=0 := by
    ext a; simp [polynomialValue]
  simp only [delta,h,mulVec_zero,sub_self]
lemma row_of_high_zero (i j : Chart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j)
    (k : Fin r) (v : Fin r → ℂ) (hv : ∀ a,k<a → v a=0) :
    (B.matrix i j z).mulVec v k=lineFactor (B.degree k) i j z*v k := by
  change (∑ a : Fin r, B.matrix i j z k a*v a)=_
  rw [Finset.sum_eq_single k]
  · rw [B.diagonal i j z hz k]
  · intro a _ ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · rw [B.triangular i j z hz k a ha,zero_mul]
    · rw [hv a ha,mul_zero]
  · simp

structure Cocycle where
  value : Chart → Chart → BaseCoordinates → Fin r → ℂ
  regular : ∀ i j a,UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ value i j z a)
  compatible : ∀ i j k z,z∈coordinateOverlap i j → z∈coordinateOverlap i k →
    value i j z+(B.matrix i j z).mulVec (value j k (coordinateChange i j z))=value i k z

def coboundary (q : Chart → Fin r → BasePolynomial) : B.Cocycle where
  value := B.delta q
  regular := B.delta_regular q
  compatible := fun _ _ _ _ hj hk ↦ B.delta_cocycle q _ _ _ hj hk

def Cocycle.sub (f g : B.Cocycle) : B.Cocycle where
  value i j z := f.value i j z-g.value i j z
  regular i j a := (f.regular i j a).sub (g.regular i j a)
  compatible i j k z hj hk := by
    rw [mulVec_sub]
    have hf := f.compatible i j k z hj hk
    have hg := g.compatible i j k z hj hk
    linear_combination hf-hg

theorem solve_upTo (b : ℕ) (hb : b≤r) (f : B.Cocycle)
    (hf : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,b≤a.val → f.value i j z a=0) :
    ∃ q : Chart → Fin r → BasePolynomial,
      (∀ i a,b≤a.val → q i a=0) ∧
      ∀ i j z,z∈coordinateOverlap i j → f.value i j z=B.delta q i j z := by
  induction b generalizing f with
  | zero =>
    refine ⟨0,fun _ _ _ ↦ rfl,?_⟩
    intro i j z hz
    rw [B.delta_zero]
    ext a
    exact hf i j z hz a (Nat.zero_le _)
  | succ b ih =>
    let k : Fin r := ⟨b,by omega⟩
    have hc : ∀ i j l z,z∈coordinateOverlap i j → z∈coordinateOverlap i l →
        f.value i j z k+lineFactor (B.degree k) i j z*f.value j l (coordinateChange i j z) k=
          f.value i l z k := by
      intro i j l z hj hl
      have h := congrFun (f.compatible i j l z hj hl) k
      dsimp only [Pi.add_apply] at h
      rw [B.row_of_high_zero i j hj k _ (fun a ha ↦
        hf j l _ (coordinateOverlap_third i j l hj hl) a (by exact ha))] at h
      exact h
    obtain ⟨p,hp⟩ := split_regular_line_cocycle (B.degree k) (fun i j z ↦ f.value i j z k)
      (fun i j ↦ f.regular i j k) hc
    let q₀ : Chart → Fin r → BasePolynomial := fun i a ↦ if a=k then p i else 0
    have hq (i : Chart) (z : BaseCoordinates) (a : Fin r) :
        polynomialValue q₀ i z a=if a=k then baseEval (p i) z else 0 := by
      simp only [polynomialValue,q₀]; split_ifs <;> simp
    have hδ (i j : Chart) (z : BaseCoordinates) (hz : z∈coordinateOverlap i j) (a : Fin r)
        (ha : k≤a) :
        B.delta q₀ i j z a=if a=k then f.value i j z k else 0 := by
      unfold delta
      simp only [Pi.sub_apply]
      rw [B.row_of_high_zero i j hz a _ (fun c hc ↦ by rw [hq]; simp [ne_of_gt (lt_of_le_of_lt ha hc)])]
      rw [hq,hq]
      by_cases h : a=k
      · subst a; simp only [ite_true]; exact (hp i j z hz).symm
      · simp [h]
    let g := Cocycle.sub B f (B.coboundary q₀)
    have hg : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,b≤a.val → g.value i j z a=0 := by
      intro i j z hz a ha
      change f.value i j z a-B.delta q₀ i j z a=0
      rw [hδ i j z hz a ha]
      by_cases h : a=k
      · simp [h]
      · have hlt : b+1≤a.val := by have hne : a.val≠b := fun he ↦ h (Fin.ext he); omega
        simp [h,hf i j z hz a hlt]
    obtain ⟨q,hq0,hqe⟩ := ih (by omega) g hg
    refine ⟨q+q₀,?_,?_⟩
    · intro i a ha
      have hak : a≠k := by intro h; subst a; dsimp [k] at ha; omega
      simp [hq0 i a (by omega),q₀,hak]
    · intro i j z hz
      rw [B.delta_add]
      have h := hqe i j z hz
      change f.value i j z-B.delta q₀ i j z=B.delta q i j z at h
      exact sub_eq_iff_eq_add.mp h

end TriangularCechBundle
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech
open scoped BigOperators
noncomputable section
namespace TriangularCechBundle
variable {r : ℕ} (B : TriangularCechBundle r)

structure Section where
  polynomial : Chart → Fin r → BasePolynomial
  compatible : ∀ i j z,z∈coordinateOverlap i j →
    (B.matrix i j z).mulVec (polynomialValue polynomial j (coordinateChange i j z))=
      polynomialValue polynomial i z

lemma delta_sub (q p : Chart → Fin r → BasePolynomial) (i j : Chart) (z : BaseCoordinates) :
    B.delta (q-p) i j z=B.delta q i j z-B.delta p i j z := by
  have h (a : Chart) (w : BaseCoordinates) :
      polynomialValue (q-p) a w=polynomialValue q a w-polynomialValue p a w := by
    ext b; simp [polynomialValue]
  simp only [delta,h,mulVec_sub]
  abel

theorem exists_generator (anchor : Chart) (k : Fin r) :
    ∃ s : B.Section,
      (∀ i a,k<a → s.polynomial i a=0) ∧
      (∀ i,s.polynomial i k=lineGenerator (B.degree k) anchor i) := by
  let l : Chart → Fin r → BasePolynomial := fun i a ↦
    if a=k then lineGenerator (B.degree k) anchor i else 0
  have hl (i : Chart) (z : BaseCoordinates) (a : Fin r) :
      polynomialValue l i z a=if a=k then baseEval (lineGenerator (B.degree k) anchor i) z else 0 := by
    simp only [polynomialValue,l]; split_ifs <;> simp
  have hd : ∀ i j z,z∈coordinateOverlap i j → ∀ a : Fin r,k.val≤a.val → B.delta l i j z a=0 := by
    intro i j z hz a ha
    unfold delta
    simp only [Pi.sub_apply]
    rw [B.row_of_high_zero i j hz a _ (fun b hb ↦ by
      rw [hl]
      have hbk : b≠k := fun he ↦ by subst b; exact (not_lt_of_ge ha) hb
      simp [hbk])]
    rw [hl,hl]
    by_cases h : a=k
    · subst a
      simp only [ite_true]
      exact sub_eq_zero.mpr (lineGenerator_compatible (B.degree k) anchor i j hz)
    · simp [h]
  obtain ⟨q,hq,hqe⟩ := B.solve_upTo k.val (Nat.le_of_lt k.isLt) (B.coboundary l) hd
  have hcomp : ∀ i j z,z∈coordinateOverlap i j → B.delta (l-q) i j z=0 := by
    intro i j z hz
    rw [B.delta_sub]
    exact sub_eq_zero.mpr (hqe i j z hz)
  refine ⟨⟨l-q,fun i j z hz ↦ sub_eq_zero.mp (hcomp i j z hz)⟩,?_,?_⟩
  · intro i a ha
    change l i a-q i a=0
    simp [l,ne_of_gt ha,hq i a (Nat.le_of_lt ha)]
  · intro i
    change l i k-q i k=_
    simp [l,hq i k le_rfl]

def generator (anchor : Chart) (k : Fin r) : B.Section := (B.exists_generator anchor k).choose
lemma generator_high (anchor i : Chart) (k a : Fin r) (ha : k<a) :
    (B.generator anchor k).polynomial i a=0 := (B.exists_generator anchor k).choose_spec.1 i a ha
lemma generator_diagonal (anchor i : Chart) (k : Fin r) :
    (B.generator anchor k).polynomial i k=lineGenerator (B.degree k) anchor i :=
  (B.exists_generator anchor k).choose_spec.2 i

end TriangularCechBundle
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.RegularMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def regularFunctionRing (U : Set BaseCoordinates) : Subring (BaseCoordinates → ℂ) where
  carrier := {f | UniformlyRegularOn U f}
  zero_mem' := uniformlyRegular_const U 0
  one_mem' := uniformlyRegular_const U 1
  add_mem' := UniformlyRegularOn.add
  mul_mem' := UniformlyRegularOn.mul
  neg_mem' := UniformlyRegularOn.neg

def regularEval (U : Set BaseCoordinates) (z : BaseCoordinates) : regularFunctionRing U →+* ℂ where
  toFun f := f.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma UniformlyRegularOn.matrix_det {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b)) :
    UniformlyRegularOn U (fun z ↦ (A z).det) := by
  let B : Matrix (Fin r) (Fin r) (regularFunctionRing U) := fun a b ↦ ⟨fun z ↦ A z a b,h a b⟩
  have hb := B.det.property
  apply hb.congr
  intro z _
  exact (regularEval U z).map_det B
lemma UniformlyRegularOn.matrix_adjugate {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b)) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z).adjugate a b) := by
  let B : Matrix (Fin r) (Fin r) (regularFunctionRing U) := fun a b ↦ ⟨fun z ↦ A z a b,h a b⟩
  have hb := (B.adjugate a b).property
  apply hb.congr
  intro z _
  exact congrFun (congrFun ((regularEval U z).map_adjugate B) a) b
lemma UniformlyRegularOn.matrix_inv {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b))
    (hu : ∀ z∈U,IsUnit (A z).det) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z)⁻¹ a b) := by
  apply (((UniformlyRegularOn.matrix_det h).inv (fun z hz ↦ (hu z hz).ne_zero)).mul (UniformlyRegularOn.matrix_adjugate h a b)).congr
  intro z _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
lemma UniformlyRegularOn.matrix_mul {r : ℕ} {U : Set BaseCoordinates}
    {A B : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b))
    (hB : ∀ a b,UniformlyRegularOn U (fun z ↦ B z a b)) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z*B z) a b) := by
  exact UniformlyRegularOn.fintype_sum (fun c ↦ (hA a c).mul (hB c b))

namespace BinaryForms

def RegularFamily (U : Set BaseCoordinates) (p : BaseCoordinates → Poly (R := ℂ)) : Prop :=
  ∀ a,UniformlyRegularOn U (fun z ↦ (p z).coeff a)
lemma RegularFamily.const (U : Set BaseCoordinates) (p : Poly (R := ℂ)) : RegularFamily U (fun _ ↦ p) :=
  fun _ ↦ uniformlyRegular_const U _
lemma RegularFamily.C {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) : RegularFamily U (fun z ↦ C (f z)) := by
  intro a
  by_cases ha : 0=a
  · simpa only [coeff_C,ite_eq_left ha] using hf
  · simpa only [coeff_C,ite_eq_right ha] using uniformlyRegular_const U 0
lemma RegularFamily.add {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z+q z) := by
  intro a
  exact (hp a).add (hq a)
lemma RegularFamily.sub {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z-q z) := by
  intro a
  simpa only [coeff_sub] using (hp a).sub (hq a)
lemma RegularFamily.mul {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z*q z) := by
  intro a
  simp only [coeff_mul]
  exact UniformlyRegularOn.finset_sum _ (fun b _ ↦ (hp b.1).mul (hq b.2))
lemma RegularFamily.pow {U : Set BaseCoordinates} {p : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (n : ℕ) : RegularFamily U (fun z ↦ p z^n) := by
  induction n with
  | zero => simpa only [pow_zero] using RegularFamily.const U 1
  | succ n ih => simpa only [pow_succ] using ih.mul hp
lemma RegularFamily.fintype_sum {ι : Type u1} [Fintype ι] {U : Set BaseCoordinates}
    {p : ι → BaseCoordinates → Poly (R := ℂ)} (hp : ∀ i,RegularFamily U (p i)) :
    RegularFamily U (fun z ↦ ∑ i,p i z) := by
  intro a
  simpa only [coeff_sum] using UniformlyRegularOn.fintype_sum (fun i ↦ hp i a)
lemma substitute_regular {U : Set BaseCoordinates} {T : BaseCoordinates → Matrix (Fin 2) (Fin 2) ℂ}
    (hT : ∀ a b,UniformlyRegularOn U (fun z ↦ T z a b)) (p : Poly (R := ℂ)) :
    RegularFamily U (fun z ↦ substitute (T z) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [substitute_C] using RegularFamily.const U (C c)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p b hp =>
    simp only [map_mul,substitute_X]
    exact hp.mul (RegularFamily.fintype_sum (fun a ↦ (RegularFamily.C (hT a b)).mul (RegularFamily.const U (X a))))
lemma symmetricMatrix_regular {U : Set BaseCoordinates} {T : BaseCoordinates → Matrix (Fin 2) (Fin 2) ℂ}
    (hT : ∀ a b,UniformlyRegularOn U (fun z ↦ T z a b)) (n : ℕ) (a b : Fin (n+1)) :
    UniformlyRegularOn U (fun z ↦ symmetricMatrix n (T z) a b) :=
  substitute_regular hT _ _
lemma adaptedPolynomials_regular {U : Set BaseCoordinates} {h d u v : BaseCoordinates → ℂ}
    (hh : UniformlyRegularOn U h) (hd : UniformlyRegularOn U d)
    (hu : UniformlyRegularOn U u) (hv : UniformlyRegularOn U v) (t : ℕ) (k : Fin (2*t+1)) :
    RegularFamily U (fun z ↦ adaptedPolynomials (h z) (d z) (u z) (v z) t k) := by
  have hk : RegularFamily U (fun z ↦ kernelForm (h z) (d z)) :=
    ((RegularFamily.C hd).mul (RegularFamily.const U (X 0))).sub ((RegularFamily.C hh).mul (RegularFamily.const U (X 1)))
  have hl : RegularFamily U (fun z ↦ liftForm (u z) (v z)) :=
    ((RegularFamily.C hu).mul (RegularFamily.const U (X 0))).add ((RegularFamily.C hv).mul (RegularFamily.const U (X 1)))
  induction t with
  | zero => exact RegularFamily.const U 1
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun k ↦ ?_) k
    · simpa only [adaptedPolynomials,Fin.snoc_last] using hl.pow (2*(t+1))
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun k ↦ ?_) k
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last] using
          hk.mul (RegularFamily.const U (X 0^(2*t+1)))
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc] using
          (hk.mul (RegularFamily.const U (X 1))).mul (ih k)
lemma adaptedMatrix_regular {U : Set BaseCoordinates} {h d u v : BaseCoordinates → ℂ}
    (hh : UniformlyRegularOn U h) (hd : UniformlyRegularOn U d)
    (hu : UniformlyRegularOn U u) (hv : UniformlyRegularOn U v) (t : ℕ) (a b : Fin (2*t+1)) :
    UniformlyRegularOn U (fun z ↦ adaptedMatrix (h z) (d z) (u z) (v z) t a b) :=
  adaptedPolynomials_regular hh hd hu hv t b _
end BinaryForms
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
noncomputable section
lemma polynomial_bezout (h d : BasePolynomial)
    (hu : ∀ z : BaseCoordinates,baseEval d z=0 → baseEval h z≠0) :
    ∃ u v : BasePolynomial,u*h+v*d=1 := by
  let J : Ideal BasePolynomial := Ideal.span {h,d}
  have hv : (1 : BasePolynomial)∈MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.zeroLocus_span] at hz
    have hh := hz h (Set.mem_insert h {d})
    have hd := hz d (Set.mem_insert_of_mem h (Set.mem_singleton d))
    have he : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
    have hdz : baseEval d (z 0,z 1)=0 := by simpa only [baseEval,← he,aeval_eq_eval] using hd
    exact False.elim (hu (z 0,z 1) hdz (by simpa only [baseEval,← he,aeval_eq_eval] using hh))
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n,hn⟩ := hv
  apply Ideal.mem_span_pair.mp
  simpa only [one_pow] using hn

namespace EqualizerData
variable (D : EqualizerData)
def bezoutU (i : StandardChart) : BasePolynomial := (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose
def bezoutV (i : StandardChart) : BasePolynomial :=
  (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose_spec.choose
lemma bezout_spec (i : StandardChart) : D.bezoutU i*D.lift i+D.bezoutV i*D.divisor i=1 :=
  (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose_spec.choose_spec
lemma bezout_eval (i : StandardChart) (z : BaseCoordinates) :
    baseEval (D.bezoutU i) z*baseEval (D.lift i) z+
      baseEval (D.bezoutV i) z*baseEval (D.divisor i) z=1 := by
  have h := congrArg (fun p ↦ baseEval p z) (D.bezout_spec i)
  simpa using h
end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open BinaryForms
noncomputable section
namespace EqualizerData
variable (D : EqualizerData)
def kernelFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  firstFactor i j z^21*(secondFactor i j z)⁻¹^3
lemma kernelFactor_divisor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    kernelFactor i j z*(firstFactor i j z*secondFactor i j z)^3=topFactor i j z := by
  have hs := secondFactor_ne_zero hz
  unfold kernelFactor topFactor
  field_simp
lemma bottomFactor_divisor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    bottomFactor i j z*(firstFactor i j z*secondFactor i j z)^3=quotientFactor i j z := by
  have hf := firstFactor_ne_zero hz
  unfold bottomFactor quotientFactor
  field_simp
lemma kernelFactor_bottomFactor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    kernelFactor i j z*bottomFactor i j z=(firstFactor i j z*secondFactor i j z)^18 := by
  have hf := firstFactor_ne_zero hz
  have hs := secondFactor_ne_zero hz
  unfold kernelFactor bottomFactor
  field_simp
lemma kernel_coordinates (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    baseEval (D.divisor j) (coordinateChange i j z)*topFactor i j z=
      kernelFactor i j z*baseEval (D.divisor i) z ∧
    baseEval (D.divisor j) (coordinateChange i j z)*D.low i j z-
      baseEval (D.lift j) (coordinateChange i j z)*bottomFactor i j z=
        -kernelFactor i j z*baseEval (D.lift i) z := by
  let δ := (firstFactor i j z*secondFactor i j z)^3
  have hδ : δ≠0 := pow_ne_zero _ (mul_ne_zero (firstFactor_ne_zero hz) (secondFactor_ne_zero hz))
  have hk := kernelFactor_divisor i j hz
  have hb := bottomFactor_divisor i j hz
  have hd := D.divisor_change i j z hz
  have hl := D.low_spec i j hz
  change baseEval (D.divisor i) z=δ*baseEval (D.divisor j) (coordinateChange i j z) at hd
  change kernelFactor i j z*δ=topFactor i j z at hk
  change bottomFactor i j z*δ=quotientFactor i j z at hb
  unfold numerator at hl
  constructor
  · rw [hd,← hk]; ring
  · apply mul_left_cancel₀ hδ
    linear_combination hl-(D.low i j z)*hd-
      (baseEval (D.lift j) (coordinateChange i j z))*hb+(baseEval (D.lift i) z)*hk

lemma substitute_kernel (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    substitute (D.coordinateTransition i j z)
      (kernelForm (baseEval (D.lift j) (coordinateChange i j z))
        (baseEval (D.divisor j) (coordinateChange i j z)))=
      C (kernelFactor i j z)*kernelForm (baseEval (D.lift i) z) (baseEval (D.divisor i) z) := by
  obtain ⟨h0,h1⟩ := D.kernel_coordinates i j hz
  apply MvPolynomial.funext
  intro x
  rw [eval_substitute]
  simp only [eval_kernelForm,map_mul,eval_C]
  simp only [coordinateTransition,Matrix.transpose_apply,Matrix.mulVec, dotProduct,Fin.sum_univ_two,
    Matrix.of_apply,cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul]
  linear_combination (x 0)*h0+(x 1)*h1
lemma substitute_f (i j : StandardChart) (z : BaseCoordinates) :
    substitute (D.coordinateTransition i j z) (X 1)=C (bottomFactor i j z)*X 1 := by
  rw [substitute_X]
  simp [coordinateTransition,Fin.sum_univ_two]
lemma substitute_e_projection (i j : StandardChart) (z : BaseCoordinates) :
    MvPolynomial.eval ![1,0] (substitute (D.coordinateTransition i j z) (X 0))=topFactor i j z := by
  rw [substitute_X]
  simp [coordinateTransition,Fin.sum_univ_two]
lemma quotient_covector (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (x : Fin 2 → ℂ) :
    baseEval (D.lift i) z*((D.coordinateTransition i j z).mulVec x 0)+
      baseEval (D.divisor i) z*((D.coordinateTransition i j z).mulVec x 1)=
    quotientFactor i j z*(baseEval (D.lift j) (coordinateChange i j z)*x 0+
      baseEval (D.divisor j) (coordinateChange i j z)*x 1) := by
  have hl := D.low_spec i j hz
  have hd := D.divisor_factor i j hz
  unfold numerator at hl
  simp only [coordinateTransition,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul]
  linear_combination (x 0)*hl+(x 1)*hd
lemma substitute_lift_quotient (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    MvPolynomial.eval ![baseEval (D.lift i) z,baseEval (D.divisor i) z]
      (substitute (D.coordinateTransition i j z)
        (liftForm (baseEval (D.bezoutU j) (coordinateChange i j z))
          (baseEval (D.bezoutV j) (coordinateChange i j z))))=quotientFactor i j z := by
  rw [eval_substitute,eval_liftForm]
  have h := D.quotient_covector i j hz
    ![baseEval (D.bezoutU j) (coordinateChange i j z),baseEval (D.bezoutV j) (coordinateChange i j z)]
  simp only [coordinateTransition,Matrix.transpose_apply,Matrix.mulVec, dotProduct,Fin.sum_univ_two,
    Matrix.of_apply,cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul] at h ⊢
  have hu := D.bezout_eval j (coordinateChange i j z)
  linear_combination h+(quotientFactor i j z)*hu
end EqualizerData
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.SymmetricFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech
open scoped BigOperators
noncomputable section

def powerCoordinates (m : ℕ) (z : BaseCoordinates) : BaseCoordinates := (z.1^m,z.2^m)
lemma powerCoordinates_change (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    powerCoordinates m (coordinateChange i j z)=coordinateChange i j (powerCoordinates m z) := by
  ext <;> simp only [powerCoordinates,coordinateChange,scalarCoordinateChange] <;>
    split_ifs <;> simp [inv_pow]
lemma powerCoordinates_overlap (m : ℕ) {i j : StandardChart} {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) : powerCoordinates m z∈coordinateOverlap i j := by
  rw [coordinateOverlap_iff] at hz ⊢
  exact ⟨hz.1.imp_right (fun h ↦ pow_ne_zero _ h),hz.2.imp_right (fun h ↦ pow_ne_zero _ h)⟩
lemma UniformlyRegularOn.comp_power {U V : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn V f) (m : ℕ) (hm : ∀ z∈U,powerCoordinates m z∈V) :
    UniformlyRegularOn U (fun z ↦ f (powerCoordinates m z)) := by
  apply hf.comp _ _ hm
  · simpa [powerCoordinates,baseEval] using (uniformlyRegular_polynomial U (X 0)).pow m
  · simpa [powerCoordinates,baseEval] using (uniformlyRegular_polynomial U (X 1)).pow m
lemma firstFactor_power (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    firstFactor i j (powerCoordinates m z)=firstFactor i j z^m := by
  simp only [firstFactor,powerCoordinates,scalarFactor]; split_ifs <;> simp
lemma secondFactor_power (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    secondFactor i j (powerCoordinates m z)=secondFactor i j z^m := by
  simp only [secondFactor,powerCoordinates,scalarFactor]; split_ifs <;> simp

namespace EqualizerData
variable (D : EqualizerData)
def flagFrame (m : ℕ) (i : StandardChart) (z : BaseCoordinates) : FlagFrame where
  h := baseEval (D.lift i) (powerCoordinates m z)
  d := baseEval (D.divisor i) (powerCoordinates m z)
  u := baseEval (D.bezoutU i) (powerCoordinates m z)
  v := baseEval (D.bezoutV i) (powerCoordinates m z)
  bezout := D.bezout_eval i _
def flagChange (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) (hz : z∈coordinateOverlap i j) :
    FlagChange (D.flagFrame m i z) (D.flagFrame m j (coordinateChange i j z)) where
  T := D.coordinateTransition i j (powerCoordinates m z)
  kernel := kernelFactor i j (powerCoordinates m z)
  bottom := bottomFactor i j (powerCoordinates m z)
  top := topFactor i j (powerCoordinates m z)
  quotient := quotientFactor i j (powerCoordinates m z)
  kernel_change := by simpa only [flagFrame,powerCoordinates_change] using D.substitute_kernel i j (powerCoordinates_overlap m hz)
  bottom_change := D.substitute_f i j _
  top_projection := D.substitute_e_projection i j _
  lift_quotient := by simpa only [flagFrame,powerCoordinates_change] using D.substitute_lift_quotient i j (powerCoordinates_overlap m hz)

def flagBasis (m t : ℕ) (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  (D.flagFrame m i z).matrix t
lemma flagBasis_det_unit (m t : ℕ) (i : StandardChart) (z : BaseCoordinates) :
    IsUnit (D.flagBasis m t i z).det := (D.flagFrame m i z).det_unit t
lemma flagBasis_regular (m t : ℕ) (i : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn univ (fun z ↦ D.flagBasis m t i z a b) := by
  apply adaptedMatrix_regular
  all_goals exact (uniformlyRegular_polynomial univ _).comp_power m (fun _ _ ↦ mem_univ _)

def flagMatrix (m e t : ℕ) (i j : StandardChart) (z : BaseCoordinates) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  lineFactor (e,e) i j z • ((D.flagBasis m t i z)⁻¹*
    symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))*
    D.flagBasis m t j (coordinateChange i j z))
lemma flagMatrix_change (m e t : ℕ) (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    D.flagMatrix m e t i j z=lineFactor (e,e) i j z • (D.flagChange m i j z hz).matrix t := rfl
lemma flagMatrix_regular (m e t : ℕ) (i j : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ D.flagMatrix m e t i j z a b) := by
  apply (lineFactor_regular (e,e) i j _).mul
  apply UniformlyRegularOn.matrix_mul _ _ a b
  · apply UniformlyRegularOn.matrix_mul
    · exact UniformlyRegularOn.matrix_inv (fun a b ↦ (D.flagBasis_regular m t i a b).mono (subset_univ _))
        (fun z _ ↦ D.flagBasis_det_unit m t i z)
    · exact symmetricMatrix_regular (fun a b ↦ (D.coordinateTransition_regular i j a b).comp_power m
        (fun _ hz ↦ powerCoordinates_overlap m hz)) (2*t)
  · intro a b
    exact (D.flagBasis_regular m t j a b).comp (coordinateChange_fst_regular i j)
      (coordinateChange_snd_regular i j) (fun _ _ ↦ mem_univ _)
lemma flagMatrix_self (m e t : ℕ) (i : StandardChart) (z : BaseCoordinates) :
    D.flagMatrix m e t i i z=1 := by
  simp only [flagMatrix,lineFactor_self,coordinateChange_self,D.coordinateTransition_self,
    symmetricMatrix_one,Matrix.mul_one,one_smul]
  exact Matrix.nonsing_inv_mul _ (D.flagBasis_det_unit m t i z)
lemma flagMatrix_cocycle (m e t : ℕ) (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z∈coordinateOverlap i j) (hk : z∈coordinateOverlap i k) :
    D.flagMatrix m e t i j z*D.flagMatrix m e t j k (coordinateChange i j z)=D.flagMatrix m e t i k z := by
  simp only [flagMatrix,smul_mul,Matrix.mul_smul,smul_smul,
    coordinateChange_comp i j k hj]
  rw [mul_comm (lineFactor (e,e) j k (coordinateChange i j z)),lineFactor_mul_one_overlap (e,e) i j k hj]
  congr 1
  rw [Matrix.mul_assoc,Matrix.mul_assoc,← Matrix.mul_assoc (D.flagBasis m t j (coordinateChange i j z)),
    ← Matrix.mul_assoc (D.flagBasis m t j (coordinateChange i j z)),
    Matrix.mul_nonsing_inv _ (D.flagBasis_det_unit m t j _),Matrix.one_mul,
    ← Matrix.mul_assoc (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))),
    ← symmetricMatrix_mul,powerCoordinates_change,
    D.coordinateTransition_mul i j k (powerCoordinates_overlap m hj) (powerCoordinates_overlap m hk),
    ← Matrix.mul_assoc]
lemma flagMatrix_triangular (m e t : ℕ) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (a b : Fin (2*t+1)) (hab : b<a) :
    D.flagMatrix m e t i j z a b=0 := by
  rw [D.flagMatrix_change m e t i j hz,Matrix.smul_apply,
    (D.flagChange m i j z hz).triangular_diagonal t |>.1 a b hab,smul_zero]
end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech EqualizerData
open scoped BigOperators
noncomputable section

def flagDegree (m : ℕ) : (e t : ℕ) → Fin (2*t+1) → ℕ × ℕ
  | e,0 => fun _ ↦ (e,e)
  | e,t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (flagDegree m (e+18*m) t) (e-3*m+24*m*(2*t+2),e-3*m)) (e,e+24*m*(2*t+2))

lemma power_mul_inv_power (x : ℂ) (hx : x≠0) (a b : ℕ) (hb : b≤a) :
    x^a*(x⁻¹)^b=x^(a-b) := by
  calc
    _ = x^(a-b)*x^b*(x⁻¹)^b := by rw [← pow_add,Nat.sub_add_cancel hb]
    _ = x^(a-b) := by rw [mul_assoc,← mul_pow,mul_inv_cancel₀ hx,one_pow,mul_one]
lemma flag_pen_scalar (m e t : ℕ) (he : 3*m≤e) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor (e,e) i j z*(EqualizerData.kernelFactor i j (powerCoordinates m z)*
      topFactor i j (powerCoordinates m z)^(2*t+1))=
    lineFactor (e-3*m+24*m*(2*t+2),e-3*m) i j z := by
  simp only [lineFactor,EqualizerData.kernelFactor,topFactor,firstFactor_power,secondFactor_power,
    ← inv_pow,← pow_mul]
  have hexp : e+(m*21+(m*24)*(2*t+1))=e-3*m+24*m*(2*t+2) := by
    have hh := Nat.sub_add_cancel he
    nlinarith
  have hs := power_mul_inv_power (secondFactor i j z) (secondFactor_ne_zero hz) e (m*3) (by omega)
  calc
    _ = firstFactor i j z^(e+(m*21+(m*24)*(2*t+1)))*
        (secondFactor i j z^e*(secondFactor i j z)⁻¹^(m*3)) := by
      simp only [pow_add]; ring
    _ = _ := by rw [hexp,hs,show m*3=3*m by omega]
lemma flag_residual_scalar (m e : ℕ) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor (e,e) i j z*(EqualizerData.kernelFactor i j (powerCoordinates m z)*
      bottomFactor i j (powerCoordinates m z))=lineFactor (e+18*m,e+18*m) i j z := by
  rw [EqualizerData.kernelFactor_bottomFactor i j (powerCoordinates_overlap m hz)]
  simp only [firstFactor_power,secondFactor_power,lineFactor,mul_pow,← pow_mul,pow_add]
  rw [show m*18=18*m by omega]
  ring
lemma flag_last_scalar (m e t : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (e,e) i j z*quotientFactor i j (powerCoordinates m z)^(2*(t+1))=
    lineFactor (e,e+24*m*(2*t+2)) i j z := by
  simp only [lineFactor,quotientFactor,secondFactor_power,← pow_mul,pow_add]
  rw [show m*24*(2*(t+1))=24*m*(2*t+2) by ring]
  ring
namespace EqualizerData
variable (D : EqualizerData)
lemma flagChange_graded (m e t : ℕ) (he : 3*m≤e) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (a : Fin (2*t+1)) :
    lineFactor (e,e) i j z*(D.flagChange m i j z hz).graded t a=
      lineFactor (flagDegree m e t a) i j z := by
  induction t generalizing e with
  | zero => simp only [FlagChange.graded,flagDegree,mul_one]
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun a ↦ ?_) a
    · simpa only [FlagChange.graded,flagDegree,Fin.snoc_last,flagChange] using flag_last_scalar m e t i j z
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun a ↦ ?_) a
      · simpa only [FlagChange.graded,flagDegree,Fin.snoc_castSucc,Fin.snoc_last,flagChange] using
          flag_pen_scalar m e t he i j hz
      · simp only [FlagChange.graded,flagDegree,Fin.snoc_castSucc]
        rw [← mul_assoc (lineFactor (e,e) i j z)]
        rw [show (D.flagChange m i j z hz).kernel*(D.flagChange m i j z hz).bottom=
          kernelFactor i j (powerCoordinates m z)*bottomFactor i j (powerCoordinates m z) from rfl,
          flag_residual_scalar m e i j hz,ih (e+18*m) (by omega)]

def symmetricFlag (m e t : ℕ) (he : 3*m≤e) : TriangularCechBundle (2*t+1) where
  degree := flagDegree m e t
  matrix := D.flagMatrix m e t
  regular := D.flagMatrix_regular m e t
  self := D.flagMatrix_self m e t
  cocycle := fun i j k z hj hk ↦ D.flagMatrix_cocycle m e t i j k hj hk
  triangular := fun i j z hz a b hab ↦ D.flagMatrix_triangular m e t i j hz a b hab
  diagonal := by
    intro i j z hz a
    rw [D.flagMatrix_change m e t i j hz,Matrix.smul_apply,smul_eq_mul,
      (D.flagChange m i j z hz).triangular_diagonal t |>.2 a]
    exact D.flagChange_graded m e t he i j hz a
end EqualizerData
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.PolynomialGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

structure PolynomialGeneration (n : ℕ) (ι : Type u1) [Fintype ι] where
  coefficient : StandardChart → Fin (n+1) → ι → BasePolynomial
  recovery : StandardChart → Fin (n+1) → ι → BasePolynomial
  leftInverse : ∀ i z (w : Fin (n+1) → ℂ),
    Matrix.mulVec (fun a q ↦ baseEval (recovery i a q) z)
      (Matrix.mulVec (Matrix.transpose (fun a q ↦ baseEval (coefficient i a q) z)) w)=w
namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u2} [Fintype ι] (B : PolynomialGeneration n ι)
def matrix (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.coefficient i a q) z
def recover (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (n+1)) ι ℂ :=
  fun a q ↦ baseEval (B.recovery i a q) z
end PolynomialGeneration
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech
open scoped BigOperators
noncomputable section

namespace EqualizerData
variable (D : EqualizerData) (m e t : ℕ) (he : 3*m≤e)
abbrev SymmetricGeneratorIndex := StandardChart × Fin (2*t+1)
def symmetricGeneratorValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ ((D.flagBasis m t i z).mulVec
    (TriangularCechBundle.polynomialValue ((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i z)) a
lemma symmetricGeneratorValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.symmetricGeneratorValue m e t he i z a q) := by
  change UniformlyRegularOn univ (fun z ↦ ∑ b, D.flagBasis m t i z a b *
    baseEval (((D.symmetricFlag m e t he).generator q.1 q.2).polynomial i b) z)
  apply UniformlyRegularOn.fintype_sum
  intro b
  exact (D.flagBasis_regular m t i a b).mul (uniformlyRegular_polynomial univ _)

def localGeneratorMatrix (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  fun a b ↦ D.symmetricGeneratorValue m e t he i z a (i,b)
lemma localGeneratorMatrix_det_unit (i : StandardChart) (z : BaseCoordinates) :
    IsUnit (D.localGeneratorMatrix m e t he i z).det := by
  let B := D.symmetricFlag m e t he
  let Q : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ := fun a b ↦
    baseEval ((B.generator i b).polynomial i a) z
  have hQ : Q.det=1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a b hab ↦ by
      dsimp [Q]; rw [B.generator_high i i b a hab]; simp)]
    apply Finset.prod_eq_one
    intro b _
    dsimp [Q]
    rw [B.generator_diagonal]
    simp [lineGenerator]
  have hmat : D.localGeneratorMatrix m e t he i z=D.flagBasis m t i z*Q := rfl
  rw [hmat,Matrix.det_mul,hQ,mul_one]
  exact D.flagBasis_det_unit m t i z
lemma localGeneratorMatrix_regular (i : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn univ (fun z ↦ D.localGeneratorMatrix m e t he i z a b) :=
  D.symmetricGeneratorValue_regular m e t he i a (i,b)

def generatorRecoveryValue (i : StandardChart) (z : BaseCoordinates) :
    Matrix (Fin (2*t+1)) (SymmetricGeneratorIndex t) ℂ :=
  fun a q ↦ if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0
lemma generatorRecoveryValue_regular (i : StandardChart) (a : Fin (2*t+1))
    (q : SymmetricGeneratorIndex t) :
    UniformlyRegularOn univ (fun z ↦ D.generatorRecoveryValue m e t he i z a q) := by
  by_cases h : q.1=i
  · simp only [generatorRecoveryValue,ite_eq_left h]
    apply UniformlyRegularOn.matrix_inv
    · intro a b
      exact D.localGeneratorMatrix_regular m e t he i b a
    · intro z _
      simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z
  · simpa only [generatorRecoveryValue,ite_eq_right h] using uniformlyRegular_const univ (0 : ℂ)
lemma generatorRecoveryValue_leftInverse (i : StandardChart) (z : BaseCoordinates)
    (w : Fin (2*t+1) → ℂ) :
    (D.generatorRecoveryValue m e t he i z).mulVec
      ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w)=w := by
  have hh := Matrix.nonsing_inv_mul ((D.localGeneratorMatrix m e t he i z).transpose)
    (by simpa only [Matrix.det_transpose] using D.localGeneratorMatrix_det_unit m e t he i z)
  have hv := congrArg (fun A : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ ↦ A.mulVec w) hh
  rw [← Matrix.mulVec_mulVec,Matrix.one_mulVec] at hv
  calc
    _ = (((D.localGeneratorMatrix m e t he i z).transpose)⁻¹).mulVec
        ((D.localGeneratorMatrix m e t he i z).transpose.mulVec w) := by
      ext a
      change (∑ q : StandardChart × Fin (2*t+1),
        (if q.1=i then ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a q.2 else 0)*
          ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) q)=_
      rw [Fintype.sum_prod_type]
      simp only [ite_mul,zero_mul]
      have hi (j : StandardChart) :
          (∑ b : Fin (2*t+1),if j=i then
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0)=
          if j=i then ∑ b : Fin (2*t+1),
            ((D.localGeneratorMatrix m e t he i z).transpose)⁻¹ a b*
              ((D.symmetricGeneratorValue m e t he i z).transpose.mulVec w) (j,b) else 0 := by
        split_ifs <;> simp
      simp_rw [hi]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    _ = w := hv

def symmetricGeneration : PolynomialGeneration (2*t) (SymmetricGeneratorIndex t) where
  coefficient := fun i a q ↦ (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose
  recovery := fun i a q ↦ (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose
  leftInverse := by
    intro i z w
    have hQ : (fun a q ↦ baseEval ((D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.symmetricGeneratorValue m e t he i z := by
      funext a q
      exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    have hR : (fun a q ↦ baseEval ((D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose) z)=
        D.generatorRecoveryValue m e t he i z := by
      funext a q
      exact (congrFun (D.generatorRecoveryValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
    rw [hQ,hR]
    exact D.generatorRecoveryValue_leftInverse m e t he i z w
lemma symmetricGeneration_matrix (i : StandardChart) (z : BaseCoordinates) :
    (D.symmetricGeneration m e t he).matrix i z=D.symmetricGeneratorValue m e t he i z := by
  funext a q
  exact (congrFun (D.symmetricGeneratorValue_regular m e t he i a q).exists_polynomial.choose_spec z).symm
lemma symmetricGeneratorValue_compatible (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (q : SymmetricGeneratorIndex t) :
    (D.symmetricGeneratorValue m e t he i z).col q=
      lineFactor (e,e) i j z • (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))).mulVec
        ((D.symmetricGeneratorValue m e t he j (coordinateChange i j z)).col q) := by
  let B := D.symmetricFlag m e t he
  have hc := (B.generator q.1 q.2).compatible i j z hz
  change (D.flagBasis m t i z).mulVec (TriangularCechBundle.polynomialValue (B.generator q.1 q.2).polynomial i z)=_
  rw [← hc]
  change (D.flagBasis m t i z).mulVec ((D.flagMatrix m e t i j z).mulVec _)=_
  rw [flagMatrix,Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc,← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (D.flagBasis_det_unit m t i z),Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec]
  rfl
end EqualizerData
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.ProjectiveEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def veronese (n : ℕ) (v : Fin 2 → ℂ) : Fin (n+1) → ℂ := fun k ↦ v 0^k.val*v 1^(n-k.val)
@[simp] lemma veronese_zero (n : ℕ) (v : Fin 2 → ℂ) : veronese n v 0=v 1^n := by simp [veronese]
@[simp] lemma veronese_last (n : ℕ) (v : Fin 2 → ℂ) : veronese n v (Fin.last n)=v 0^n := by simp [veronese]

def veroneseOne (n : ℕ) (hn : 0<n) : Fin (n+1) := ⟨1,by omega⟩

def VeroneseRelations (n : ℕ) (hn : 0<n) (w : Fin (n+1) → ℂ) : Prop :=
  (∀ k,w k^n=w (Fin.last n)^k.val*w 0^(n-k.val)) ∧
  ∀ k : Fin n,w k.succ*w 0=w k.castSucc*w (veroneseOne n hn)

def veroneseEndpoint (n : ℕ) (b : Fin 2) : Fin (n+1) := if b=0 then Fin.last n else 0
def veroneseAdjacent (n : ℕ) (hn : 0<n) (b : Fin 2) : Fin (n+1) :=
  if b=0 then ⟨n-1,by omega⟩ else veroneseOne n hn

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section

def flipFirst (i : StandardChart) : StandardChart := (1-i.1,i.2)
def flipSecond (i : StandardChart) : StandardChart := (i.1,1-i.2)
def segreFactor (a i : StandardChart) (z : BaseCoordinates) : ℂ :=
  baseEval (lineGenerator (1,1) a i) z
@[simp] lemma segreFactor_self (i : StandardChart) (z : BaseCoordinates) : segreFactor i i z=1 := by
  rw [segreFactor,eval_lineGenerator,lineFactor_self]
@[simp] lemma segreFactor_flipFirst (i : StandardChart) (z : BaseCoordinates) :
    segreFactor (flipFirst i) i z=z.1 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [segreFactor,eval_lineGenerator,lineFactor,flipFirst,firstFactor,secondFactor,scalarFactor]
@[simp] lemma segreFactor_flipSecond (i : StandardChart) (z : BaseCoordinates) :
    segreFactor (flipSecond i) i z=z.2 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [segreFactor,eval_lineGenerator,lineFactor,flipSecond,firstFactor,secondFactor,scalarFactor]

namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u1} [Fintype ι] (B : PolynomialGeneration n ι)
abbrev ProjectiveIndex (ι : Type u2) [Fintype ι] := Fin (Fintype.card (StandardChart × ι))
def index : (StandardChart × ι) ≃ ProjectiveIndex ι := Fintype.equivFin _
def label (j : ProjectiveIndex ι) : StandardChart × ι := (index (ι:=ι)).symm j
@[simp] lemma label_index (a : StandardChart) (q : ι) : label (index (a,q))=(a,q) := Equiv.symm_apply_apply _ _
@[simp] lemma index_label (j : ProjectiveIndex ι) : index (label j)=j := Equiv.apply_symm_apply _ _

def stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) : ProjectiveIndex ι → ℂ :=
  fun j ↦ segreFactor (label j).1 i z*((B.matrix i z).transpose.mulVec w) (label j).2
def value (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) : ProjectiveIndex ι → ℂ :=
  B.stencil i z (veronese n v)
@[simp] lemma stencil_index (i a : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι) :
    B.stencil i z w (index (a,q))=segreFactor a i z*((B.matrix i z).transpose.mulVec w) q := by
  simp [stencil]
@[simp] lemma stencil_self (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι) :
    B.stencil i z w (index (i,q))=((B.matrix i z).transpose.mulVec w) q := by
  simp
end PolynomialGeneration
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section

structure StandardBundleCover (V : AlgebraicRankTwoBundle) : Prop where
  domain : ∀ i x,x∈V.domain i ↔ i<4 ∧ x∈range (affineQuadric (V.chart i))
  surj : ∀ a : StandardChart,∃ i : ℕ,i<4 ∧ V.chart i=a

namespace StandardBundleCover
variable {V : AlgebraicRankTwoBundle} (H : StandardBundleCover V)
def chartIndex (a : StandardChart) : ℕ := (H.surj a).choose
end StandardBundleCover

structure SegreSectionSystem (V : AlgebraicRankTwoBundle) (n : ℕ) (ι : Type u1) [Fintype ι] where
  cover : StandardBundleCover V
  generation : PolynomialGeneration n ι
  sections : ProjectiveIndex ι → SymmetricSection V n
  value_eq : ∀ i x,x∈V.domain i → ∀ v : FiberCoordinates,
    sectionVector sections i x v=generation.value (V.chart i) (coordQuadric (V.chart i) x) v

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section

lemma lineFactor_add (a b : ℕ × ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (a.1+b.1,a.2+b.2) i j z=lineFactor a i j z*lineFactor b i j z := by
  simp only [lineFactor,pow_add]
  ring
lemma lineFactor_diagonal (n : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (n,n) i j z=(firstFactor i j z*secondFactor i j z)^n := by simp only [lineFactor,mul_pow]
lemma eval_polynomial_smul_vector (n : ℕ) (p : Form (R:=ℂ) n) (c : ℂ) (v : FiberCoordinates) :
    MvPolynomial.eval (c • v) (polynomial n p)=c^n*MvPolynomial.eval v (polynomial n p) := by
  simp only [eval_polynomial,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val+(n-k.val)=n := by omega
  calc
    _ = (c^k.val*c^(n-k.val))*(p k*v 0^k.val*v 1^(n-k.val)) := by ring
    _ = _ := by rw [← pow_add,hk]
lemma eval_polynomial_smul_coeff (n : ℕ) (p : Form (R:=ℂ) n) (c : ℂ) (v : FiberCoordinates) :
    MvPolynomial.eval v (polynomial n (c • p))=c*MvPolynomial.eval v (polynomial n p) := by
  simp only [eval_polynomial,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma polynomial_eval_dot (n : ℕ) (p : Form (R:=ℂ) n) (v : FiberCoordinates) :
    MvPolynomial.eval v (polynomial n p)=dotProduct p (veronese n v) := by
  rw [eval_polynomial]
  unfold dotProduct veronese
  apply Finset.sum_congr rfl
  intro k _
  ring

namespace EqualizerData
variable (D : EqualizerData)
lemma powerTwist_cover (m : ℕ) (hm : 0 < m) : StandardBundleCover (powerPullbackTwist D.bundle m hm) where
  domain i x := by
    change x∈principalChart (standardChartNat i) (pullbackPolynomial m (standardEquationNat i)) ↔ _
    by_cases hi : i<4
    · simp only [standardEquationNat,ite_eq_left hi,pullbackPolynomial,map_one,principalChart_one]
      exact ⟨fun h ↦ ⟨hi,h⟩,fun h ↦ h.2⟩
    · simp [standardEquationNat,hi,pullbackPolynomial,principalChart,baseEval]
  surj := standardChartNat_surj

def fullSymmetricCoefficient (m e t : ℕ) (he : 3*m≤e)
    (a i : StandardChart) (q : SymmetricGeneratorIndex t) : Fin (2*t+1) → BasePolynomial :=
  fun k ↦ lineGenerator (1,1) a i*(D.symmetricGeneration m e t he).coefficient i k q
lemma fullSymmetricCoefficient_value (m e t : ℕ) (he : 3*m≤e)
    (a i : StandardChart) (q : SymmetricGeneratorIndex t) (z : BaseCoordinates) :
    (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a i q k) z)=
      segreFactor a i z • (D.symmetricGeneratorValue m e t he i z).col q := by
  ext k
  simp only [fullSymmetricCoefficient,baseEval_mul,Pi.smul_apply,smul_eq_mul]
  change segreFactor a i z*(D.symmetricGeneration m e t he).matrix i z k q=_
  rw [D.symmetricGeneration_matrix]
  rfl
lemma fullSymmetricCoefficient_compatible (m e t : ℕ) (he : 3*m≤e)
    (a i j : StandardChart) (q : SymmetricGeneratorIndex t) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a i q k) z)=
      lineFactor (e+1,e+1) i j z • (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))).mulVec
        (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a j q k) (coordinateChange i j z)) := by
  rw [D.fullSymmetricCoefficient_value,D.fullSymmetricCoefficient_value,D.symmetricGeneratorValue_compatible m e t he i j hz q,
    Matrix.mulVec_smul,smul_smul,smul_smul]
  congr 1
  have h := lineGenerator_compatible (1,1) a i j hz
  change lineFactor (1,1) i j z*segreFactor a j (coordinateChange i j z)=segreFactor a i z at h
  rw [← h,show (e+1,e+1)=(e+1,e+1) from rfl,lineFactor_add (e,e) (1,1)]
  ring

lemma powerTwist_transition (m : ℕ) (hm : 0 < m) (i j : ℕ) (x : QuadricSurface)
    (hx : x∈(powerPullbackTwist D.bundle m hm).domain i) :
    (powerPullbackTwist D.bundle m hm).transition i j x=
      (firstFactor (standardChartNat i) (standardChartNat j) (coordQuadric (standardChartNat i) x)*
       secondFactor (standardChartNat i) (standardChartNat j) (coordQuadric (standardChartNat i) x)) •
      D.coordinateTransition (standardChartNat i) (standardChartNat j)
        (powerCoordinates m (coordQuadric (standardChartNat i) x)) := by
  have hr := ((D.powerTwist_cover m hm).domain i x).mp hx |>.2
  have he := affineQuadric_coord hr
  conv_lhs => rw [← he]
  simp only [powerPullbackTwist,bundle,globalTransition,powerQuadric_affine hm,coordQuadric_affine]
  congr 1
  rw [firstFactor_transition,secondFactor_transition]
  rfl

def ampleSection (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t)
    (a : StandardChart) (q : SymmetricGeneratorIndex t) : SymmetricSection (powerPullbackTwist D.bundle m hm) (2*t) where
  coefficient := fun i k z ↦ baseEval (D.fullSymmetricCoefficient m e t he a (standardChartNat i) q k) z
  regular := fun i k ↦ algebraicallyRegular_polynomial _ _
  compatible := by
    intro i j x hi hj v
    let E := powerPullbackTwist D.bundle m hm
    let ci := standardChartNat i
    let cj := standardChartNat j
    let z := coordQuadric cj x
    have hjr : x∈range (affineQuadric cj) := ((D.powerTwist_cover m hm).domain j x).mp hj |>.2
    have hir : x∈range (affineQuadric ci) := ((D.powerTwist_cover m hm).domain i x).mp hi |>.2
    have hz : z∈coordinateOverlap cj ci := coord_mem_overlap cj ci hjr hir
    have hchange : coordinateChange cj ci z=coordQuadric ci x := by
      rw [← coordinateChange_coord]
      change coordQuadric ci (affineQuadric cj (coordQuadric cj x))=_
      rw [affineQuadric_coord hjr]
    have hQ := D.fullSymmetricCoefficient_compatible m e t he a cj ci q hz
    rw [hchange,hen] at hQ
    let p : Form (R:=ℂ) (2*t) := fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a ci q k) (coordQuadric ci x)
    let T := D.coordinateTransition cj ci (powerCoordinates m z)
    let l := firstFactor cj ci z*secondFactor cj ci z
    have hdual : E.dualTransition i j x=l • T.transpose := by
      unfold AlgebraicRankTwoBundle.dualTransition
      rw [D.powerTwist_transition m hm j i x hj,Matrix.transpose_smul]
    change (∑ k : Fin (2*t+1),p k*((E.dualTransition i j x).mulVec v 0)^k.val*
      ((E.dualTransition i j x).mulVec v 1)^(2*t-k.val))=_
    rw [← eval_polynomial,hdual,Matrix.smul_mulVec,eval_polynomial_smul_vector]
    rw [← eval_polynomial]
    change _=MvPolynomial.eval v (polynomial (2*t) (fun k ↦ baseEval (D.fullSymmetricCoefficient m e t he a cj q k) z))
    rw [hQ,lineFactor_diagonal,eval_polynomial_smul_coeff,polynomial_symmetricMatrix,eval_substitute]

lemma ampleSection_value (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t)
    (a : StandardChart) (q : SymmetricGeneratorIndex t) (i : ℕ) (x : QuadricSurface) (v : FiberCoordinates) :
    (D.ampleSection m hm e t he hen a q).value i x v=
      (D.symmetricGeneration m e t he).value (standardChartNat i) (coordQuadric (standardChartNat i) x) v (index (a,q)) := by
  change (∑ k : Fin (2*t+1),baseEval (D.fullSymmetricCoefficient m e t he a (standardChartNat i) q k)
    (coordQuadric (standardChartNat i) x)*v 0^k.val*v 1^(2*t-k.val))=_
  rw [← eval_polynomial,D.fullSymmetricCoefficient_value,eval_polynomial_smul_coeff,polynomial_eval_dot]
  rw [PolynomialGeneration.value,PolynomialGeneration.stencil_index,D.symmetricGeneration_matrix]
  rfl

def ampleSystem (m : ℕ) (hm : 0 < m) (e t : ℕ) (he : 3*m≤e) (hen : e+1=2*t) :
    SegreSectionSystem (powerPullbackTwist D.bundle m hm) (2*t) (SymmetricGeneratorIndex t) where
  cover := D.powerTwist_cover m hm
  generation := D.symmetricGeneration m e t he
  sections := fun j ↦ D.ampleSection m hm e t he hen (label j).1 (label j).2
  value_eq := by
    intro i x _ v
    ext j
    change (D.ampleSection m hm e t he hen (label j).1 (label j).2).value i x v=_
    rw [D.ampleSection_value,index_label]
    rfl
end EqualizerData
end
end QuadricCounterexample

end

end OAI
end


