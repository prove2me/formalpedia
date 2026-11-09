-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Values
-- name    : MomentAmbiguitySecretary_Secretary_Values
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:58.786022+00:00
-- url     : https://prove2.me/theorems/1c92e822-9112-4eaf-8152-5dd2db91e252
-- title:
--   Worst-case secretary values and exact cutoff maximum
-- statement:
--   For $1\le r\le m$ let
--
--   $$p_m(1)=1/m,\qquad p_m(r)=\frac{r-1}{m}\sum_{t=r}^m\frac1{t-1}\quad(r\ge2),\qquad s_m=\max_{1\le r\le m}p_m(r).$$
--
--   The independent robust value is the supremum over independent-model moment policies of the infimum of their actual success probability over all admissible per-label laws, evaluated at the laws' disclosed moments. The i.i.d. value is defined separately over common laws and common-disclosure policies. All infimum and supremum ranges are inhabited and bounded in $[0,1]$, as proved by the structural range lemmas. Uniform subgrid laws are actual equally weighted Dirac mixtures, allowing repeated independent draws.
--
--   These definitions impose no asserted value or target inequality. Horizon zero is assigned classical value zero only to make the definition total; the goal requires $m\ge1$.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, §2.2 and Lemma 6.1, PDF/printed p.5,15, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Policies

open scoped NNReal

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace MomentAmbiguitySecretary.Secretary

noncomputable section

def cutoffProbability (m r : ℕ) : ℝ :=
  if r = 1 then 1 / (m : ℝ)
  else ((r : ℝ) - 1) / (m : ℝ) *
    ∑ t ∈ Finset.Icc r m, 1 / ((t : ℝ) - 1)

def classicalValue (m : ℕ) : ℝ :=
  if hm : 1 ≤ m then
    (Finset.Icc 1 m).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩ (cutoffProbability m)
  else 0

def independentSuccess {m : ℕ} (π : IndependentPolicy m) (μ : Fin m → Law) : ℝ :=
  success π (fun i => disclose (μ i)) (fun i => (μ i).val)

def iidSuccess {m : ℕ} (π : IIDPolicy m) (μ : Law) : ℝ :=
  success π (disclose μ) (fun _ : Fin m => μ.val)

def independentGuarantee {m : ℕ} (π : IndependentPolicy m) : ℝ :=
  ⨅ μ : Fin m → Law, independentSuccess π μ

def iidGuarantee {m : ℕ} (π : IIDPolicy m) : ℝ :=
  ⨅ μ : Law, iidSuccess π μ

def independentValue (m : ℕ) : ℝ :=
  ⨆ π : IndependentPolicy m, independentGuarantee π

def iidValue (m : ℕ) : ℝ :=
  ⨆ π : IIDPolicy m, iidGuarantee π

/-- Structural bounds justify the real infima; all input law classes are inhabited. -/
theorem independentGuarantee_mem_unit {m : ℕ} (π : IndependentPolicy m) :
    independentGuarantee π ∈ Icc (0 : ℝ) 1 := by
  have hlo : ∀ μ : Fin m → Law, 0 ≤ independentSuccess π μ :=
    fun μ => (success_mem_unit π _ _).1
  have hb : BddBelow (range (independentSuccess π)) := ⟨0, by rintro _ ⟨μ, rfl⟩; exact hlo μ⟩
  constructor
  · exact le_ciInf hlo
  · exact (ciInf_le hb (fun _ => zeroLaw)).trans (success_mem_unit π _ _).2

theorem iidGuarantee_mem_unit {m : ℕ} (π : IIDPolicy m) :
    iidGuarantee π ∈ Icc (0 : ℝ) 1 := by
  have hlo : ∀ μ : Law, 0 ≤ iidSuccess π μ := fun μ => (success_mem_unit π _ _).1
  have hb : BddBelow (range (iidSuccess π)) := ⟨0, by rintro _ ⟨μ, rfl⟩; exact hlo μ⟩
  constructor
  · exact le_ciInf hlo
  · exact (ciInf_le hb zeroLaw).trans (success_mem_unit π _ _).2

/-- The outer supremum ranges are nonempty (always reject) and bounded by one. -/
theorem independentValue_mem_unit (m : ℕ) : independentValue m ∈ Icc (0 : ℝ) 1 := by
  have hb : BddAbove (range (@independentGuarantee m)) :=
    ⟨1, by rintro _ ⟨π, rfl⟩; exact (independentGuarantee_mem_unit π).2⟩
  constructor
  · exact (independentGuarantee_mem_unit (rejectPolicy _ m)).1.trans
      (le_ciSup hb (rejectPolicy _ m))
  · exact ciSup_le fun π => (independentGuarantee_mem_unit π).2

theorem iidValue_mem_unit (m : ℕ) : iidValue m ∈ Icc (0 : ℝ) 1 := by
  have hb : BddAbove (range (@iidGuarantee m)) :=
    ⟨1, by rintro _ ⟨π, rfl⟩; exact (iidGuarantee_mem_unit π).2⟩
  constructor
  · exact (iidGuarantee_mem_unit (rejectPolicy _ m)).1.trans
      (le_ciSup hb (rejectPolicy _ m))
  · exact ciSup_le fun π => (iidGuarantee_mem_unit π).2

/-- Uniform independent grid draws, without conditioning on distinctness. -/
def gridDistribution {N : ℕ} (v : Fin N → ℝ≥0) (H : Finset (Fin N)) : Distribution :=
  if hH : H.Nonempty then
    ⟨∑ i ∈ H, (H.card : ℝ≥0∞)⁻¹ • Measure.dirac (v i), by
      constructor
      simp [Finset.sum_apply]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hH.card_ne_zero) (by simp)⟩
  else zeroLaw.val

end
end MomentAmbiguitySecretary.Secretary


