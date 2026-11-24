-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:09.36556+00:00
-- url     : https://prove2.me/theorems/793b16d5-f641-4f9d-8d38-63ec9f1341c5
-- title:
--   Smooth Lev Zero
-- statement:
--   Definitions and structural lemmas for Smooth Lev Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SmoothLevZero.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section test
variable {k r : ℕ} {i : Fin (r + 1)}
theorem smoothLev_zero : SmoothLev k r i Set.univ (0 : Mx k r → ℂ) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => (0 : ℂ), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
theorem smoothLev_add {f h : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) (hh : SmoothLev k r i Set.univ h) :
    SmoothLev k r i Set.univ (f + h) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hhG⟩ := hh g₀ hg₀
  refine ⟨U ∩ V, fun x => F x + G x, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono fun _ hx => hx.1).add (hG.mono fun _ hx => hx.2), fun g hg hgl => ?_⟩
  show f g + h g = F g + G g
  rw [hfF g hg.1 hgl, hhG g hg.2 hgl]
theorem smoothLev_smul (c : ℂ) {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) :
    SmoothLev k r i Set.univ (c • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, fun g hg hgl => ?_⟩
  show c • f g = c * F g
  rw [hfF g hg hgl, smul_eq_mul]
theorem cptOn_zero : CptOn k r i (0 : Mx k r → ℂ) :=
  ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩
theorem cptOn_add {f h : Mx k r → ℂ} (hf : CptOn k r i f) (hh : CptOn k r i h) : CptOn k r i (f + h) := by
  obtain ⟨K, hK, hfK⟩ := hf
  obtain ⟨L, hL, hhL⟩ := hh
  refine ⟨K ∪ L, hK.union hL, fun g hg hn => ?_⟩
  have h1 : g ∉ K := fun hk => hn (Or.inl hk)
  have h2 : g ∉ L := fun hl => hn (Or.inr hl)
  show f g + h g = 0
  rw [hfK g hg h1, hhL g hg h2, add_zero]
theorem cptOn_smul (c : ℂ) {f : Mx k r → ℂ} (hf : CptOn k r i f) : CptOn k r i (c • f) := by
  obtain ⟨K, hK, hfK⟩ := hf
  refine ⟨K, hK, fun g hg hn => ?_⟩
  show c • f g = 0
  rw [hfK g hg hn, smul_zero]
def testSub (k r : ℕ) (i : Fin (r + 1)) : Submodule ℂ (Mx k r → ℂ) where
  carrier := {f | TestF k r i f}
  zero_mem' := ⟨smoothLev_zero, cptOn_zero⟩
  add_mem' hf hh := ⟨smoothLev_add hf.1 hh.1, cptOn_add hf.2 hh.2⟩
  smul_mem' c _ hf := ⟨smoothLev_smul c hf.1, cptOn_smul c hf.2⟩
end test
structure Hyp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (μ : Measure (Mt k r)) : Prop where
  hμ : Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r i) μ
  hz : inWb k r z
  hz' : inWb k r z'
  ET : EabTest
  EA : EabAdj
  MT : MulTest
  TI : TestInt
  Yb : YbRel
  Xb : XbRel
  HF : HmFacts
  EP : EabPres
  Gl : EabGlLev
  YL : YLeibniz
section main
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
abbrev ιo (k r : ℕ) : Mt k r → Mx k r := fun x => Matrix.of x
theorem hI (H : Hyp k r z z' i μ) : IntOn μ (ιo k r) (testSub k r i) :=
  fun f hf h hh => H.TI k r i μ H.hμ f h hf hh
theorem hG (H : Hyp k r z z' i μ) : ∀ᵐ x ∂μ, ιo k r x ∈ Glev k r i := by
  first
    | exact ae_iff.mpr H.hμ.conc
    | (rw [ae_iff]; exact H.hμ.conc)
def EOp (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  EH k r (posL k r i a) (posL k r i b)
def EOp' (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  fun f g => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g
def MOp {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => φ g * f g
def MOp' {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => star (φ g) * f g
theorem EOp'_eq (a b : Fin (mdim k r i)) (f : Mx k r → ℂ) :
    EOp' k r i a b f = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f := by
  funext g
  simp only [EOp', EOp, Finset.sum_apply, Pi.smul_apply]
theorem adjOp_E (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (EOp k r i a b) (EOp' k r i a b) where
  mem f hf := H.ET k r i a b f hf
  mem' f hf := by
    rw [EOp'_eq]
    exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ (H.ET k r i c d f hf)
  lin f hf h hh c g hg := by
    have := (H.EP ℂ k r z i Set.univ a b f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simpa only [EOp, smul_eq_mul] using this
  lin' f hf h hh c g hg := by
    simp only [EOp']
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c' _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    have := (H.EP ℂ k r z i Set.univ c' d f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    ring
  adj f hf h hh := H.EA k r i μ H.hμ a b f h hf hh
theorem adjOp_M (φ : Mx k r → ℂ)
    (hφ : ∀ f, TestF k r i f → TestF k r i (fun g => φ g * f g) ∧ TestF k r i (fun g => star (φ g) * f g)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (MOp φ) (MOp' φ) where
  mem f hf := (hφ f hf).1
  mem' f hf := (hφ f hf).2
  lin f _ h _ c g _ := by simp only [MOp]; ring
  lin' f _ h _ c g _ := by simp only [MOp']; ring
  adj f _ h _ := by
    unfold pr MOp MOp'
    congr 1
    funext x
    simp only [star_mul', star_star]
    ring
theorem yTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => yv k r z i g c * f g) ∧ TestF k r i (fun g => star (yv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).1, (H.MT k r z i c f hf).2.1⟩
theorem ybTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ybv k r z i g c * f g) ∧ TestF k r i (fun g => star (ybv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).2.2.1, (H.MT k r z i c f hf).2.2.2⟩
def EA (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : A (hI H) := toA (hI H) (hG H) (adjOp_E H a b)
def YA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => yv k r z i g c) (yTest H c))
def YbA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => ybv k r z i g c) (ybTest H c))
end main
end PI.QnHermHaar


