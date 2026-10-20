-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
-- name    : OAI_Analysis_Cotype_ComplexDualLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:19:41.550984+00:00
-- url     : https://prove2.me/theorems/d1d4c9c1-5411-4d14-b087-f83d2a5f3ada
-- title:
--   Complexified dual lifts of real operators
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $Y$ be a real normed space.
--
--   1. **Complex dual space.** $Y^\sharp=\mathcal L_{\mathbb R}(Y^*,\mathbb C)$, real-linear maps from the dual to $\mathbb C$, a complex normed space.
--   2. **Dual action.** For $T\in\mathcal L(Y)$, $\varphi\mapsto\varphi\circ T$ on $Y^*$, of norm at most $\|T\|$.
--   3. **Complex lift.** $\widehat T f=f\circ(\varphi\mapsto\varphi\circ T)$, a complex-linear operator on $Y^\sharp$ with
--   $$
--   \|\widehat T\|=\|T\| .
--   $$
--   It is additive, multiplicative and real-homogeneous in $T$, and it extends $T$ through the embedding $y\mapsto(\varphi\mapsto\varphi(y))$. This complexification lets complex spectral calculus be applied to real operators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ComplexDualLift.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ComplexDualLift.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype

namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev ComplexDualSpace (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] :=
  (Y →L[ℝ] ℝ) →L[ℝ] ℂ

instance complexDualSpaceNormedAddCommGroup : NormedAddCommGroup (ComplexDualSpace Y) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance complexDualSpaceNormedSpace : NormedSpace ℂ (ComplexDualSpace Y) :=
  ContinuousLinearMap.toNormedSpace

def realDualAction (T : Y →L[ℝ] Y) : (Y →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ) :=
  ({ toFun := fun φ => φ.comp T
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } :
    (Y →L[ℝ] ℝ) →ₗ[ℝ] (Y →L[ℝ] ℝ)).mkContinuous ‖T‖
      (fun φ => (φ.opNorm_comp_le T).trans_eq (mul_comm _ _))

@[simp] theorem realDualAction_apply (T : Y →L[ℝ] Y) (φ : Y →L[ℝ] ℝ) :
    realDualAction T φ = φ.comp T := rfl

theorem realDualAction_norm_le (T : Y →L[ℝ] Y) : ‖realDualAction T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro φ
  exact (φ.opNorm_comp_le T).trans_eq (mul_comm _ _)

def complexDualLift (T : Y →L[ℝ] Y) : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  ({ toFun := fun f => f.comp (realDualAction T)
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } :
    ComplexDualSpace Y →ₗ[ℂ] ComplexDualSpace Y).mkContinuous ‖T‖ (fun f =>
      (f.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
        (realDualAction_norm_le T) (norm_nonneg f)).trans_eq (mul_comm _ _)))

@[simp] theorem complexDualLift_apply (T : Y →L[ℝ] Y)
    (f : ComplexDualSpace Y) (φ : Y →L[ℝ] ℝ) :
    complexDualLift T f φ = f (φ.comp T) := rfl

theorem complexDualLift_norm_le (T : Y →L[ℝ] Y) : ‖complexDualLift T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (f.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
    (realDualAction_norm_le T) (norm_nonneg f)).trans_eq (mul_comm _ _))

def complexDualEmbed (y : Y) : ComplexDualSpace Y :=
  Complex.ofRealCLM.comp (NormedSpace.inclusionInDoubleDual ℝ Y y)

@[simp] theorem complexDualEmbed_apply (y : Y) (φ : Y →L[ℝ] ℝ) :
    complexDualEmbed y φ = (φ y : ℂ) := rfl

@[simp] theorem complexDualEmbed_norm (y : Y) : ‖complexDualEmbed y‖ = ‖y‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
    intro φ
    simpa only [complexDualEmbed_apply, Complex.norm_real, Real.norm_eq_abs,
      mul_comm] using φ.le_opNorm y
  · apply NormedSpace.norm_le_dual_bound ℝ y (norm_nonneg (complexDualEmbed y))
    intro φ
    simpa only [complexDualEmbed_apply, Complex.norm_real, Real.norm_eq_abs] using
      (complexDualEmbed y).le_opNorm φ

@[simp] theorem complexDualLift_embed (T : Y →L[ℝ] Y) (y : Y) :
    complexDualLift T (complexDualEmbed y) = complexDualEmbed (T y) := by
  ext φ
  rfl

theorem complexDualLift_norm (T : Y →L[ℝ] Y) : ‖complexDualLift T‖ = ‖T‖ := by
  apply le_antisymm (complexDualLift_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  simpa only [complexDualLift_embed, complexDualEmbed_norm] using
    (complexDualLift T).le_opNorm (complexDualEmbed y)

@[simp] theorem complexDualLift_one : complexDualLift (1 : Y →L[ℝ] Y) = 1 := by
  ext f φ
  change f (φ.comp (1 : Y →L[ℝ] Y)) = f φ
  congr 1

@[simp] theorem complexDualLift_mul (S T : Y →L[ℝ] Y) :
    complexDualLift (S*T) = complexDualLift S * complexDualLift T := by
  ext f φ
  rfl

@[simp] theorem complexDualLift_add (S T : Y →L[ℝ] Y) :
    complexDualLift (S+T) = complexDualLift S + complexDualLift T := by
  ext f φ
  change f (φ.comp (S+T)) = f (φ.comp S) + f (φ.comp T)
  rw [ContinuousLinearMap.comp_add, map_add]

@[simp] theorem complexDualLift_sub (S T : Y →L[ℝ] Y) :
    complexDualLift (S-T) = complexDualLift S - complexDualLift T := by
  ext f φ
  change f (φ.comp (S-T)) = f (φ.comp S) - f (φ.comp T)
  rw [ContinuousLinearMap.comp_sub, map_sub]

@[simp] theorem complexDualLift_smul (r : ℝ) (T : Y →L[ℝ] Y) :
    complexDualLift (r • T) = r • complexDualLift T := by
  ext f φ
  change f (φ.comp (r • T)) = r • f (φ.comp T)
  rw [ContinuousLinearMap.comp_smul, map_smul]

@[simp] theorem complexDualLift_pow (T : Y →L[ℝ] Y) (n : ℕ) :
    complexDualLift (T^n) = (complexDualLift T)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

end Cotype

end

end OAI


