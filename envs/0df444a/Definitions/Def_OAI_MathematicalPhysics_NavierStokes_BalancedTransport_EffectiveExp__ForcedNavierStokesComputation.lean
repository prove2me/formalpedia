-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:59:53.398258+00:00
-- url     : https://prove2.me/theorems/f400b144-5cd2-4b62-9fb8-f8592bc614a5
-- title:
--   Rational approximations of the exponential
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   For $q\in\mathbb Q$ and a precision $n$, a cutoff $k$ is accurate when
--   $$
--   \frac{|q|}{k+1}\le\frac12\quad\text{and}\quad\frac{2|q|^k}{k!}\le2^{-n}.
--   $$
--   Such $k$ always exist. The cutoff is the least accurate $k$, and the approximation is the Taylor sum $\sum_{j<k}q^j/j!$ up to the cutoff. The module proves the tail estimate $|e^x-\sum_{j<k}x^j/j!|\le2|x|^k/k!$ when $|x|/(k+1)\le\frac12$. Hence the approximation is within $2^{-n}$ of $e^q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveExp.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveExp.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

def expAccurate (q : ℚ) (n k : ℕ) : Prop :=
  |q| / ((k + 1 : ℕ) : ℚ) ≤ 1 / 2 ∧
    |q| ^ k / ((k.factorial : ℕ) : ℚ) * 2 ≤ (1 / 2 : ℚ) ^ n

instance (q : ℚ) (n : ℕ) : DecidablePred (expAccurate q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma exists_expAccurate (q : ℚ) (n : ℕ) : ∃ k, expAccurate q n k := by
  have h₀ : Tendsto (fun k : ℕ => (|q| : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.mpr (tendsto_add_atTop_nat 1))
  have h₁ : Tendsto (fun k : ℕ => (|q| : ℝ) ^ k / (k.factorial : ℝ) * 2)
      atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial (|q| : ℝ)).tendsto_atTop_zero.mul_const 2
  have he : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hh₀ := h₀.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hh₁ := h₁.eventually_lt_const he
  obtain ⟨k, hk₀, hk₁⟩ := (hh₀.and hh₁).exists
  refine ⟨k, ?_, ?_⟩
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using hk₀.le
  · apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hk₁.le

noncomputable def expCutoff (q : ℚ) (n : ℕ) : ℕ :=
  Nat.find (exists_expAccurate q n)

noncomputable def expApprox (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (expCutoff q n), q ^ k / (k.factorial : ℚ)

lemma real_exp_tail_bound (x : ℝ) (k : ℕ) (h : |x| / (k + 1 : ℕ) ≤ 1 / 2) :
    |Real.exp x - ∑ j ∈ Finset.range k, x ^ j / (j.factorial : ℝ)| ≤
      |x| ^ k / (k.factorial : ℝ) * 2 := by
  have hc : ‖(x : ℂ)‖ / (k + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have hh := @Complex.exp_bound' (x : ℂ) k hc
  rw [← Complex.ofReal_exp] at hh
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

lemma expApprox_spec (q : ℚ) (n : ℕ) :
    |(expApprox q n : ℝ) - Real.exp (q : ℝ)| ≤ error n := by
  have hk := Nat.find_spec (exists_expAccurate q n)
  change expAccurate q n (expCutoff q n) at hk
  have hrat : |(q : ℝ)| / ((expCutoff q n + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.1
    push_cast at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hb := real_exp_tail_bound (q : ℝ) (expCutoff q n) hrat
  have ht : |(q : ℝ)| ^ expCutoff q n / ((expCutoff q n).factorial : ℝ) * 2 ≤ error n := by
    dsimp [error]
    have hh := (Rat.cast_le (K := ℝ)).mpr hk.2
    push_cast at hh
    simpa only [one_div] using hh
  rw [abs_sub_comm]
  simpa only [expApprox, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    using hb.trans ht

end BalancedTransport.Effectivity
end

end OAI


