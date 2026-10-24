-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
-- name    : KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:26:59.118367+00:00
-- url     : https://prove2.me/theorems/973a0b12-3f34-43b6-b6b4-7585cced7c66
-- title:
--   Almost-everywhere bounded multipliers on L²
-- statement:
--   If a scalar multiplier $c$ is a.e. strongly measurable and satisfies $|c|\le M$ almost everywhere, `bddSmulₗ` and `bddSmulL` map a vector-valued $L^2$ class $u$ to the class of $x\mapsto c(x)u(x)$, with norm at most $|M|\|u\|$. If a vector multiplier $\beta$ is a.e. strongly measurable and satisfies $\|\beta\|\le M$ almost everywhere, `bddSmulRightₗ` and `bddSmulRightL` map scalar $L^2$ classes to the vector-valued class $x\mapsto u(x)\beta(x)$, again with norm bound $|M|$. The accompanying `memLp`, pointwise-a.e. representation, and norm lemmas state the required measurability, integrability, and operator estimates.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/BoundedMultiplier.lean#L37-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.BoundedMultiplier`, definition bundle `KLS408915f_FunctionalInequalities_L2_BoundedMultiplier`; the repository is private at upload time).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities
namespace L2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
section BddSmul
variable {c : α → ℝ} {M : ℝ}
/-- An a.e. bounded scalar multiplier preserves `L²`. -/
theorem memLp_bddSmul (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : MemLp (fun x => c x • (u x)) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) (hc.smul (Lp.aestronglyMeasurable u)) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖c x • (u x)‖ = |c x| * ‖u x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → H)) x‖ = |M| * ‖u x‖ := by
    simp [norm_smul, Real.norm_eq_abs]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (norm_nonneg _)
/-- Multiplication by an a.e. bounded scalar multiplier, as a linear map on `L²`. -/
def bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmul hc hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmul hc hM u).toLp _) ((memLp_bddSmul hc hM v).toLp _),
      (memLp_bddSmul hc hM u).coeFn_toLp, (memLp_bddSmul hc hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmul hc hM u).toLp _), (memLp_bddSmul hc hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
    exact smul_comm _ _ _
theorem coeFn_bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulₗ hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  (memLp_bddSmul hc hM u).coeFn_toLp
theorem norm_bddSmulₗ_le (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : ‖bddSmulₗ hc hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulₗ hc hM u‖ ≤ ‖(|M| • u : Lp H 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulₗ hc hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs]
    exact mul_le_mul_of_nonneg_right (h3.trans (le_abs_self M)) (norm_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]
/-- Multiplication by an a.e. bounded scalar multiplier, as a continuous linear map on `L²`. -/
def bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulₗ hc hM) |M| (norm_bddSmulₗ_le hc hM)
@[simp]
theorem bddSmulL_apply (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : bddSmulL hc hM u = bddSmulₗ hc hM u := rfl
end BddSmul
section BddSmulRight
variable {β : α → H} {M : ℝ}
/-- An a.e. bounded vector multiplier sends a scalar `L²` class to a vector `L²` class. -/
theorem memLp_bddSmulRight (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : MemLp (fun x => (u x) • β x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) ((Lp.aestronglyMeasurable u).smul hβ) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖(u x) • β x‖ = |u x| * ‖β x‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → ℝ)) x‖ = |M| * ‖u x‖ := by
    simp [Real.norm_eq_abs]
  rw [h1, h2, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (abs_nonneg _)
/-- Multiplication by an a.e. bounded vector multiplier, as a linear map `L²(ℝ) → L²(H)`. -/
def bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmulRight hβ hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmulRight hβ hM u).toLp _) ((memLp_bddSmulRight hβ hM v).toLp _),
      (memLp_bddSmulRight hβ hM u).coeFn_toLp, (memLp_bddSmulRight hβ hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, add_smul]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmulRight hβ hM u).toLp _), (memLp_bddSmulRight hβ hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_assoc]
theorem coeFn_bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightₗ hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  (memLp_bddSmulRight hβ hM u).coeFn_toLp
theorem norm_bddSmulRightₗ_le (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : ‖bddSmulRightₗ hβ hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulRightₗ hβ hM u‖ ≤ ‖(|M| • u : Lp ℝ 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulRightₗ hβ hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs, mul_comm (|M|)]
    exact mul_le_mul_of_nonneg_left (h3.trans (le_abs_self M)) (abs_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]
/-- Multiplication by an a.e. bounded vector multiplier, as a continuous linear map. -/
def bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulRightₗ hβ hM) |M| (norm_bddSmulRightₗ_le hβ hM)
@[simp]
theorem bddSmulRightL_apply (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : bddSmulRightL hβ hM u = bddSmulRightₗ hβ hM u := rfl
end BddSmulRight
end L2
end FunctionalInequalities


