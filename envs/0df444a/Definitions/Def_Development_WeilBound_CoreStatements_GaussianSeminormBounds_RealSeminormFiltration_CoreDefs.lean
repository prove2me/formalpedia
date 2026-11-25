-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:03.726847+00:00
-- url     : https://prove2.me/theorems/d0af34ec-f304-45ea-97e6-4c8faef34bdb
-- title:
--   Core Defs
-- statement:
--   Definitions and structural lemmas for Core Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDefs.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockHarmSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockJointMult
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockOneDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockWtDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Theorems.Thm_PositivityTheory_KReal_fockAct1_fockAct2_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action
open scoped InnerProductSpace
namespace PositivityTheory.KReal
instance decPosC {p q : ℕ} (a b : Ix p q) : Decidable (posC a b) := by
  cases a <;> cases b <;> simp only [posC] <;> infer_instance
section Abstract
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def IsLie (act : Mat r s →ₗ[ℂ] Module.End ℂ M) : Prop :=
  ∀ X Y, act X * act Y - act Y * act X = act (X * Y - Y * X)
def GlK (ρ : Ix r s → Ix r s → Module.End ℂ M) : Prop :=
  ∀ a b c d, sameBlock a b → sameBlock c d →
    ρ a b * ρ c d - ρ c d * ρ a b = (if b = c then ρ a d else 0) - (if d = a then ρ c b else 0)
def KSt (ρ : Ix r s → Ix r s → Module.End ℂ M) (N : Submodule ℂ M) : Prop :=
  ∀ a b, sameBlock a b → ∀ x ∈ N, ρ a b x ∈ N
def HwK (ρ : Ix r s → Ix r s → Module.End ℂ M) (μ : Ix r s → ℚ) (f : M) : Prop :=
  (∀ a, ρ a a f = ((μ a : ℚ) : ℂ) • f) ∧ ∀ a b, posC a b → ρ a b f = 0
def cycK (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) : Submodule ℂ M :=
  sInf {N | f ∈ N ∧ KSt ρ N}
def genG (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) : Submodule ℂ M :=
  sInf {N | S ≤ N ∧ ∀ W, ∀ x ∈ N, act W x ∈ N}
def casK (ρ : Ix r s → Ix r s → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, if sameBlock a b then ρ a b * ρ b a else 0
def casW (μ : Ix r s → ℚ) : ℚ :=
  ∑ a, μ a ^ 2 + ∑ a, ∑ b, if posC a b then μ a - μ b else 0
def units (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (a b : Ix r s) : Module.End ℂ M := act (Eab a b)
def StarK (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (S : Submodule ℂ M) (c0 : ℝ) : Prop :=
  ∀ t : ℝ, t ≤ c0 + ((r : ℝ) + s) →
    ∀ x ∈ Submodule.span ℂ {y | ∃ a b, ¬ sameBlock a b ∧ ∃ v ∈ S, y = act (Eab a b) v},
      casK (units act) x = (t : ℂ) • x → x = 0
end Abstract
def AdjK {r s : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (ρ : Ix r s → Ix r s → Module.End ℂ A) : Prop :=
  ∀ a b, sameBlock a b → ∀ u v, ⟪ρ a b u, v⟫_ℂ = ⟪u, ρ b a v⟫_ℂ
def epsB {r s : ℕ} (a b : Ix r s) : ℂ := if sameBlock a b then 1 else -1
def AdjG {r s : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ A) : Prop :=
  ∀ a b u v, ⟪act (Eab a b) u, v⟫_ℂ = epsB a b * ⟪u, act (Eab b a) v⟫_ℂ
def Side {r s : ℕ} (La : Ix r s → ℚ) (T : Type) [AddCommGroup T] [Module ℂ T]
    (act : Mat r s →ₗ[ℂ] Module.End ℂ T) : Prop :=
  IsLie act ∧ Nontrivial T ∧
  ∃ (A : Type) (_ : NormedAddCommGroup A) (_ : InnerProductSpace ℂ A) (_ : FiniteDimensional ℂ A)
    (ρ : Ix r s → Ix r s → Module.End ℂ A) (ι : A →ₗ[ℂ] T) (f : A),
    AdjK ρ ∧ GlK ρ ∧ HwK ρ La f ∧
    (∀ a b, sameBlock a b → ∀ u, ι (ρ a b u) = act (Eab a b) (ι u)) ∧
    genG act (Submodule.span ℂ {ι f}) = ⊤ ∧
    StarK act (LinearMap.range ι) ((casW La : ℚ) : ℝ)
instance fockNormed (σ : Type) : NormedAddCommGroup (PI.FHS.FockV σ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (PI.FHS.FockV σ) _ _ _ PI.FHS.fockCore
instance fockInnerSp (σ : Type) : InnerProductSpace ℂ (PI.FHS.FockV σ) :=
  letI _cd : InnerProductSpace.Core ℂ (PI.FHS.FockV σ) := PI.FHS.fockCore
  InnerProductSpace.ofCore (𝕜 := ℂ) (inferInstance : PreInnerProductSpace.Core ℂ (PI.FHS.FockV σ))
abbrev FV (p q r s : ℕ) : Type := PI.FHS.FockV (Ix p q × Ix r s)
def fvAct1 (p q r s : ℕ) : Mat p q →ₗ[ℂ] Module.End ℂ (FV p q r s) := fockAct1 p q r s
def fvAct2 (p q r s : ℕ) : Mat r s →ₗ[ℂ] Module.End ℂ (FV p q r s) := fockAct2 p q r s
def twAct (p q r s : ℕ) (τ : ℂ) : Mat r s →ₗ[ℂ] Module.End ℂ (Pol p q r s) :=
  fockAct2 p q r s + (τ • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight 1
def thAct (p q r s : ℕ) (c τ : ℂ) : Mat r s →ₗ[ℂ] Module.End ℂ (ThC p q r s c) where
  toFun W := ReciprocityTheory.ThetaSummability.Real.coinvOp (Y := act1 p q r s) (chiTr c) (fockAct2 p q r s W) (fun Z => (fockAct1_fockAct2_commute Z W).symm) +
    (τ * W.trace) • 1
  map_add' W W' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change thMkC p q r s c (fockAct2 p q r s (W + W') f) + (τ * (W + W').trace) • thMkC p q r s c f =
      (thMkC p q r s c (fockAct2 p q r s W f) + (τ * W.trace) • thMkC p q r s c f) +
      (thMkC p q r s c (fockAct2 p q r s W' f) + (τ * W'.trace) • thMkC p q r s c f)
    simp only [map_add, LinearMap.add_apply, Matrix.trace_add, mul_add, add_smul]
    abel
  map_smul' a W := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change thMkC p q r s c (fockAct2 p q r s (a • W) f) + (τ * (a • W).trace) • thMkC p q r s c f =
      a • (thMkC p q r s c (fockAct2 p q r s W f) + (τ * W.trace) • thMkC p q r s c f)
    simp only [map_smul, LinearMap.smul_apply, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
    rw [mul_left_comm]
def harm1 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) := Submodule.span ℂ (lowKer p q r s true false)
def Dom {r s : ℕ} (ν : Ix r s → ℚ) : Prop := ∀ a b, posC a b → ν b ≤ ν a
def Supp (p q : ℕ) {r s : ℕ} (ν : Ix r s → ℚ) : Prop :=
  (∀ k : Fin r, p ≤ (k : ℕ) → shiftNu (cPair p q) ν (.inl k) ≤ 0) ∧
  (∀ l : Fin s, q ≤ (l : ℕ) → shiftNu (cPair p q) ν (.inr l) ≤ 0) ∧
  (∀ k : Fin r, (k : ℕ) + q < r → 0 ≤ shiftNu (cPair p q) ν (.inl k)) ∧
  (∀ l : Fin s, (l : ℕ) + p < s → 0 ≤ shiftNu (cPair p q) ν (.inr l))
def RootTo {r s : ℕ} (ν : Ix r s → ℚ) (a b : Ix r s) (La : Ix r s → ℚ) : Prop :=
  ∀ x, ν x + (if x = a then 1 else 0) - (if x = b then 1 else 0) = La x
def CombOK (p q : ℕ) {r s : ℕ} (c0 τ : ℚ) (La : Ix r s → ℚ) : Prop :=
  JointShape p q r s (fun _ => c0) La ∧ (∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) ∧
  ∀ ν a b, ¬ sameBlock a b → RootTo ν a b La → Dom ν → Supp p q ν →
    degW (cPair p q) ν = degW (cPair r s) (fun _ : Ix p q => c0) + 2 →
    casW (fun x => La x + τ) + ((r : ℚ) + s) < casW (fun x => ν x + τ)
def laPos (p q r s n m : ℕ) : Ix r s → ℚ
  | .inl k => (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q
  | .inr l => (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q
def laNeg (p q r s n m : ℕ) : Ix r s → ℚ
  | .inl k => (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q
  | .inr l => (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q
def nD (D : RealData) : ℕ := (D.κ + 2 * D.y - D.d) / 2
def mD (D : RealData) : ℕ := (D.κ + D.d - 2 * D.y) / 2
def PairData (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ (lam : Ix p q → ℂ) (x : Pol p q r 0) (y : Pol p q 0 s) (dx : ℕ),
    x ≠ 0 ∧ y ≠ 0 ∧ x ∈ homog (Ix p q × Ix r 0) dx ∧
    (∀ a b, sameBlock a b → fockAct1 p q r 0 (Eab a b) x = (if a = b then lam a else 0) • x) ∧
    (∀ i j, fockAct1 p q r 0 (Eab (.inr j) (.inl i)) x = 0) ∧
    (∀ a b, sameBlock a b → fockAct1 p q 0 s (Eab a b) y = (if a = b then c - lam a else 0) • y) ∧
    (∀ i j, fockAct1 p q 0 s (Eab (.inl i) (.inr j)) y = 0)
end PositivityTheory.KReal
end


