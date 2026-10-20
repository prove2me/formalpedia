-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:16:33.990464+00:00
-- url     : https://prove2.me/theorems/e60d520f-4c59-410c-90df-09c3d05c77fa
-- title:
--   Rational approximations of logarithms
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   For a rational $q>0$ and a precision $n$, a pair $(r,k)$, with $r$ rational and $k$ a natural number, brackets $\log q$ when
--   $$
--   E_k\bigl(r-2^{-n}\bigr)+2^{-k}<q<E_k\bigl(r+2^{-n}\bigr)-2^{-k},
--   $$
--   where $E_k$ is the rational exponential approximation with error at most $2^{-k}$. A bracketing pair forces $e^{r-2^{-n}}<q<e^{r+2^{-n}}$, so $|\log q-r|<2^{-n}$. Bracketing pairs always exist. The logarithm approximation returns $r$ from the first bracketing pair in a fixed enumeration of pairs, and $0$ when $q\le0$. The module also notes that $2^{-n}\to0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveLog.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveLog.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

noncomputable def logBracket (q : ℚ) (n c : ℕ) : Prop :=
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k < q ∧
    q < expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k

noncomputable instance (q : ℚ) (n : ℕ) : DecidablePred (logBracket q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma cast_error (n : ℕ) : (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) = error n := by
  simp [error, one_div]

lemma error_tendsto : Tendsto error atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma exists_logBracket {q : ℚ} (hq : 0 < q) (n : ℕ) : ∃ c, logBracket q n c := by
  have he : 0 < error n := by unfold error; positivity
  obtain ⟨r, hr₀, hr₁⟩ := exists_rat_btwn
    (show Real.log (q : ℝ) - error n < Real.log (q : ℝ) + error n by linarith)
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ : Real.exp ((r : ℝ) - error n) < (q : ℝ) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have h₁ : (q : ℝ) < Real.exp ((r : ℝ) + error n) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have hd : Tendsto (fun k => 2 * error k) atTop (𝓝 0) := by
    simpa using error_tendsto.const_mul 2
  obtain ⟨k, hk₀, hk₁⟩ := ((hd.eventually_lt_const (sub_pos.mpr h₀)).and
    (hd.eventually_lt_const (sub_pos.mpr h₁))).exists
  refine ⟨Nat.pair (@Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable r) k, ?_⟩
  simp only [logBracket, Nat.unpair_pair, Denumerable.ofNat_encode]
  have hl := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).2
  have hu := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).1
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at hl hu
  constructor
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_add, cast_error]
    linarith
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_sub, cast_error]
    linarith

noncomputable def logSearchPredicate (p : ℚ × ℕ) (c : ℕ) : Prop :=
  if 0 < p.1 then logBracket p.1 p.2 c else True

noncomputable instance : DecidableRel logSearchPredicate := by
  intro p c
  unfold logSearchPredicate
  infer_instance

lemma exists_logSearchPredicate (p : ℚ × ℕ) : ∃ c, logSearchPredicate p c := by
  by_cases hq : 0 < p.1
  · simpa [logSearchPredicate, hq] using exists_logBracket hq p.2
  · exact ⟨0, by simp [logSearchPredicate, hq]⟩

noncomputable def logCutoff (p : ℚ × ℕ) : ℕ := Nat.find (exists_logSearchPredicate p)

noncomputable def logApprox (q : ℚ) (n : ℕ) : ℚ :=
  if 0 < q then Denumerable.ofNat ℚ (logCutoff (q,n)).unpair.1 else 0

end BalancedTransport.Effectivity
end

end OAI


