-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F002
-- name    : LevyStochCalc_Poisson_PoissonSplitting_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:19:49.606509+00:00
-- url     : https://prove2.me/theorems/c8e6a95d-3f0c-40be-a8f4-c4b755f0ac61
-- title:
--   Source declarations: LevyStochCalc.Poisson.PoissonSplitting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PoissonSplitting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F000
import Definitions.Def_SourceProof_1f23144afeff765ffdd0f47d
import Definitions.Def_SourceProof_639c5d56eb5b0b845b7540f2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)

variable {B t}

/-- The exponential series weighted by the Poisson probabilities. -/
lemma tsum_poisson_pow (r : ℝ≥0) (c : ℂ) :
    ∑' m : ℕ, ((Real.exp (-r) * r ^ m / m.factorial : ℝ) : ℂ) * c ^ m = exp (r * (c - 1)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * c)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 := (h.mul_left (exp (-(r : ℂ)))).tsum_eq
  rw [← Complex.exp_add] at h2
  rw [show (r : ℂ) * (c - 1) = -(r : ℂ) + r * c by ring, ← h2]
  refine tsum_congr fun m => ?_
  push_cast
  ring
end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

/-- The joint characteristic function of the counts of a Poisson number of independent marks
on pairwise disjoint sets. -/
theorem charFun_map_markCount (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (t : PiLp 2 (fun _ : Fin n => ℝ)) :
    charFun (P.map (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))) t
      = ∏ i, charFun Po(ℝ, r * (ρ (B i)).toNNReal) (t.ofLp i) := by
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => markCount_measurable_real mK mX (hB i))
  rw [charFun_apply, integral_map hV.aemeasurable (by fun_prop)]
  have hinner : ∀ ω, (inner ℝ (WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) t : ℝ)
      = ∑ i, (markCount K X (B i) ω : ℝ) * t.ofLp i := by
    intro ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.inner_apply _ _
  simp_rw [hinner, exp_sum_markCount B t.ofLp]
  rw [_root_.Prove2MeSourceProof.h_1f23144afeff765ffdd0f47d hB mK hX mX hXi hKX, _root_.Prove2MeSourceProof.h_639c5d56eb5b0b845b7540f2 B t.ofLp hB hdisj]
  have hpmf : ∀ m, P.real (K ⁻¹' {m}) = Real.exp (-r) * r ^ m / m.factorial := by
    intro m
    rw [measureReal_def, ← Measure.map_apply mK (measurableSet_singleton m), hK.map_eq,
      ← measureReal_def]
    exact poissonMeasure_real_singleton r m
  simp_rw [hpmf]
  rw [tsum_poisson_pow]
  simp_rw [charFun_map_cast_poissonMeasure]
  rw [← Complex.exp_sum]
  congr 1
  have hp : ∀ i, (((r * (ρ (B i)).toNNReal : ℝ≥0) : ℝ) : ℂ) = (r : ℂ) * (ρ.real (B i) : ℂ) := by
    intro i
    push_cast
    rfl
  simp_rw [hp]
  have h3 : ∀ i, (r : ℂ) * (ρ.real (B i) : ℂ) * (exp (t.ofLp i * I) - 1)
      = (r : ℂ) * ((ρ.real (B i) : ℂ) * exp (t.ofLp i * I)) - (r : ℂ) * (ρ.real (B i) : ℂ) :=
    fun i => by ring
  simp_rw [h3, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
/-- The joint law of the counts of a Poisson number of independent marks on pairwise disjoint
sets is the product of Poisson laws, as a law on `EuclideanSpace ℝ (Fin n)`. -/
theorem map_markCount_toLp_eq (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    P.map (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))
      = (Measure.pi (fun i => Po(ℝ, r * (ρ (B i)).toNNReal))).map (WithLp.toLp 2) := by
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => markCount_measurable_real mK mX (hB i))
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_markCount hK mK hX mX hXi hKX hB hdisj, charFun_pi]
/-- The joint law of the counts, as a law on `Fin n → ℝ`. -/
theorem map_markCount_eq_pi (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    P.map (fun ω i => (markCount K X (B i) ω : ℝ))
      = Measure.pi (fun i => Po(ℝ, r * (ρ (B i)).toNNReal)) := by
  have h := congrArg (Measure.map (WithLp.ofLp : PiLp 2 (fun _ : Fin n => ℝ) → Fin n → ℝ))
    (map_markCount_toLp_eq hK mK hX mX hXi hKX hB hdisj)
  have hofLp : Measurable (WithLp.ofLp : PiLp 2 (fun _ : Fin n => ℝ) → Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 _).symm.measurable
  have hN : Measurable (fun ω i => (markCount K X (B i) ω : ℝ)) :=
    measurable_pi_lambda _ fun i => markCount_measurable_real mK mX (hB i)
  have hT : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → PiLp 2 (fun _ : Fin n => ℝ)) :=
    (MeasurableEquiv.toLp 2 _).measurable
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    hT.comp hN
  rw [Measure.map_map hofLp hV, Measure.map_map hofLp hT] at h
  have e1 : (WithLp.ofLp ∘ fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))
      = fun ω i => (markCount K X (B i) ω : ℝ) := by
    funext ω
    simp
  have e2 : (WithLp.ofLp ∘ (WithLp.toLp 2 : (Fin n → ℝ) → PiLp 2 (fun _ : Fin n => ℝ))) = id := by
    funext v
    simp
  rw [e1, e2, Measure.map_id] at h
  exact h
/-- Each count is Poisson with mean `r ρ(Bᵢ)`, as a real random variable. -/
theorem hasLaw_markCount_real (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (i : Fin n) :
    HasLaw (fun ω => (markCount K X (B i) ω : ℝ)) Po(ℝ, r * (ρ (B i)).toNNReal) P := by
  refine ⟨(markCount_measurable_real mK mX (hB i)).aemeasurable, ?_⟩
  have hN : Measurable (fun ω i => (markCount K X (B i) ω : ℝ)) :=
    measurable_pi_lambda _ fun i => markCount_measurable_real mK mX (hB i)
  calc P.map (fun ω => (markCount K X (B i) ω : ℝ))
      = (P.map (fun ω i => (markCount K X (B i) ω : ℝ))).map (fun v => v i) :=
        (Measure.map_map (measurable_pi_apply i) hN).symm
    _ = Po(ℝ, r * (ρ (B i)).toNNReal) := by
        rw [map_markCount_eq_pi hK mK hX mX hXi hKX hB hdisj, ← Measure.infinitePi_eq_pi,
          Measure.infinitePi_map_eval]
/-- The counts on pairwise disjoint sets are independent, as real random variables. -/
theorem iIndepFun_markCount_real (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ)) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (markCount_measurable_real mK mX (hB i)).aemeasurable),
    map_markCount_eq_pi hK mK hX mX hXi hKX hB hdisj]
  congr 1
  funext i
  exact (hasLaw_markCount_real hK mK hX mX hXi hKX hB hdisj i).map_eq.symm
/-- Each count is Poisson with mean `r ρ(Bᵢ)`, as an `ℝ≥0∞`-valued random variable. -/
theorem map_markCount_ennreal (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (i : Fin n) :
    P.map (fun ω => (markCount K X (B i) ω : ℝ≥0∞))
      = Po(r * (ρ (B i)).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞)) := by
  have h1 : (fun ω => (markCount K X (B i) ω : ℝ≥0∞))
      = ENNReal.ofReal ∘ (fun ω => (markCount K X (B i) ω : ℝ)) := by
    funext ω
    simp [ENNReal.ofReal_natCast]
  rw [h1, ← Measure.map_map ENNReal.measurable_ofReal (markCount_measurable_real mK mX (hB i)),
    (hasLaw_markCount_real hK mK hX mX hXi hKX hB hdisj i).map_eq,
    Measure.map_map ENNReal.measurable_ofReal Measurable.of_discrete]
  congr 1
  funext k
  simp [ENNReal.ofReal_natCast]
/-- The counts on pairwise disjoint sets are independent, as `ℝ≥0∞`-valued random variables. -/
theorem iIndepFun_markCount_ennreal (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ≥0∞)) P := by
  have h := (iIndepFun_markCount_real hK mK hX mX hXi hKX hB hdisj).comp
    (fun _ => ENNReal.ofReal) (fun _ => ENNReal.measurable_ofReal)
  have e : (fun i ω => (markCount K X (B i) ω : ℝ≥0∞))
      = fun i => ENNReal.ofReal ∘ (fun ω => (markCount K X (B i) ω : ℝ)) := by
    funext i ω
    simp [ENNReal.ofReal_natCast]
  rw [e]
  exact h
/-- The counts on a pairwise disjoint family of sets indexed by an arbitrary type are
independent, as `ℝ≥0∞`-valued random variables. -/
theorem iIndepFun_markCount_ennreal' {ι : Type*} {B : ι → Set 𝓧} (hK : HasLaw K Po(r) P)
    (mK : Measurable K) (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j))
    (hXi : iIndepFun X P) (hKX : IndepFun K (fun ω j => X j ω) P)
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ≥0∞)) P := by
  rw [iIndepFun_iff_finset]
  intro s
  have h := iIndepFun_markCount_ennreal hK mK hX mX hXi hKX
    (B := fun k : Fin s.card => B (s.equivFin.symm k)) (fun k => hB _)
    (fun k l hkl => hdisj fun h => hkl (s.equivFin.symm.injective (Subtype.ext h)))
  have h' := h.precomp s.equivFin.injective
  simp only [Equiv.symm_apply_apply] at h'
  exact h'
end Law

end LevyStochCalc.Poisson


