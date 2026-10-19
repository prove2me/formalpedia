-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Tests
-- name    : OAI_Analysis_C0Absorption_Tests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:04:12.611255+00:00
-- url     : https://prove2.me/theorems/641f2d19-a154-43ad-a510-52fecd47266f
-- title:
--   Cylinder operations, generated representations and the source test classes
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. $c_0$ is the Banach space of real sequences tending to zero with the sup norm, $B$ is its closed unit ball, and for a finite set $I$ of coordinates the cube $[-1,1]^I$ is the image of $B$ under restriction to $I$.
--
--   1. **Cylinder operations.** On the cube $[-1,1]^I$, an operation has a scale $2^{-a}$, a grid centre $q$ at that scale, and a type. It acts by the flattening operator $G_{q,2^{-a}}$ or by the remainder operator $R_{q,2^{-a}}$. A list of operations acts by composition and multiplies Lipschitz constants by at most $4$ per operation.
--   2. **Cylinder bases.** A family indexed by $\Gamma$ provides, for each $\gamma$, a nonempty coordinate set $I_\gamma$, a band $j_\gamma$, and a base function on $[-1,1]^{I_\gamma}$ bounded by $A$ and $L_0$-Lipschitz. It also provides band lengths $\ell_j>0$.
--   3. **Generated representations.** A list of operations with nonincreasing scales whose total is below $\ell_{j_\gamma}/2$ generates the function $\mathrm{value}(s)=(\text{operations applied to the base})(s|_{I_\gamma})$ on the unit ball $B$ of $c_0$.
--   4. **Classes.** $T_h$ consists of values with at most $h$ operations. $V_h$ consists of products of such values with at most $h$ tail factors at scales up to $2^{-h}$, and band at most $h$. The source classes alternate, $L_{2h}=T_{h+1}$ and $L_{2h+1}=V_{h+1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Tests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Tests.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure CylinderOperation (I : Finset ℕ) where
  scaleIndex : ℕ
  center : OperationGrid I scaleIndex
  isG : Bool

namespace CylinderOperation
variable {I : Finset ℕ}
def scale (r : CylinderOperation I) : ℝ := dyadic r.scaleIndex
def point (r : CylinderOperation I) : Cube I := operationGridPoint I r.scaleIndex r.center
def act (r : CylinderOperation I) : (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  localOp r.isG r.point r.scale

theorem scale_pos (r : CylinderOperation I) : 0 < r.scale := dyadic_pos r.scaleIndex

theorem act_lipschitz (r : CylinderOperation I) {K : ℝ≥0} {u : Cube I → ℝ}
    (hu : LipschitzWith K u) : LipschitzWith (4*K) (r.act u) := by
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact (localR_lipschitz r.point r.scale_pos u hu).weaken (by nlinarith)
  · exact localG_lipschitz r.point r.scale_pos u hu

end CylinderOperation

def applyOperations {I : Finset ℕ} (ops : List (CylinderOperation I)) :
    (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  match ops with
  | [] => LinearMap.id
  | r :: rs => (applyOperations rs).comp r.act

@[simp] theorem applyOperations_nil {I : Finset ℕ} (u : Cube I → ℝ) : applyOperations [] u = u := rfl
@[simp] theorem applyOperations_cons {I : Finset ℕ} (r : CylinderOperation I)
    (rs : List (CylinderOperation I)) (u : Cube I → ℝ) :
    applyOperations (r::rs) u = applyOperations rs (r.act u) := rfl

theorem applyOperations_append {I : Finset ℕ} (rs ss : List (CylinderOperation I))
    (u : Cube I → ℝ) : applyOperations (rs++ss) u = applyOperations ss (applyOperations rs u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih => simpa using ih (r.act u)

theorem applyOperations_lipschitz {I : Finset ℕ} (ops : List (CylinderOperation I))
    {K : ℝ≥0} {u : Cube I → ℝ} (hu : LipschitzWith K u) :
    LipschitzWith (4^ops.length*K) (applyOperations ops u) := by
  induction ops generalizing K u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (r.act_lipschitz hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

structure CylinderBases (Γ : Type*) where
  coordinates : Γ → Finset ℕ
  coordinates_nonempty : ∀ γ, (coordinates γ).Nonempty
  band : Γ → ℕ
  ell : ℕ → ℝ
  ell_pos : ∀ j, 0 < ell j
  base : (γ : Γ) → Cube (coordinates γ) → ℝ
  A : ℝ≥0
  L0 : ℝ≥0
  base_sup : ∀ γ x, |base γ x| ≤ A
  base_lipschitz : ∀ γ, LipschitzWith L0 (base γ)

structure GeneratedRepresentation {Γ : Type*} (B : CylinderBases Γ) (γ : Γ) where
  operations : List (CylinderOperation (B.coordinates γ))
  ordered : operations.Pairwise (fun p q => q.scale ≤ p.scale)
  budget : (operations.map CylinderOperation.scale).sum < B.ell (B.band γ)/2

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def cubeValue (r : GeneratedRepresentation B γ) : Cube (B.coordinates γ) → ℝ :=
  applyOperations r.operations (B.base γ)

def value (r : GeneratedRepresentation B γ) : C0Ball → ℝ :=
  r.cubeValue ∘ cubeRestrict (B.coordinates γ)

theorem cubeValue_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.cubeValue :=
  applyOperations_lipschitz _ (B.base_lipschitz γ)

theorem value_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.value := by
  simpa only [value, mul_one] using r.cubeValue_lipschitz.comp (cubeRestrict_lipschitz (B.coordinates γ))

end GeneratedRepresentation

def TClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, r.operations.length ≤ h ∧ f = r.value}

structure TailOperation where
  scaleIndex : ℕ
  tailIndex : ℕ
  isBasic : Bool

namespace TailOperation

def factor (t : TailOperation) (s : C0Ball) : ℝ :=
  if t.isBasic then tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  else tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1

end TailOperation

def tailProduct (ts : List TailOperation) (s : C0Ball) : ℝ := (ts.map (fun t => t.factor s)).prod

@[simp] theorem tailProduct_nil (s : C0Ball) : tailProduct [] s = 1 := rfl
@[simp] theorem tailProduct_cons (t : TailOperation) (ts : List TailOperation) (s : C0Ball) :
    tailProduct (t::ts) s = t.factor s * tailProduct ts s := rfl

def VClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, ∃ ts : List TailOperation,
    r.operations.length ≤ h ∧ B.band γ ≤ h ∧ ts.length ≤ h ∧
      (∀ t ∈ ts, t.scaleIndex ≤ h) ∧ f = fun s => r.value s*tailProduct ts s}

theorem TClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : LipschitzWith (4^h*B.L0) f := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  apply r.value_lipschitz.weaken
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) B.L0.coe_nonneg

def sourceClasses {Γ : Type*} (B : CylinderBases Γ) (n : ℕ) : Set (C0Ball → ℝ) :=
  if n % 2 = 0 then TClass B (n/2+1) else VClass B (n/2+1)

@[simp] theorem sourceClasses_even {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h) = TClass B (h+1) := by simp [sourceClasses]

@[simp] theorem sourceClasses_odd {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h+1) = VClass B (h+1) := by
  have hh : (2*h+1)/2 = h := by omega
  simp [sourceClasses, hh]

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def append (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    GeneratedRepresentation B γ where
  operations := r.operations++[op]
  ordered := List.pairwise_append.mpr ⟨r.ordered, by simp, by
    intro p hp q hq; have hq' : q=op := by simpa using hq
    subst q; exact hord p hp⟩
  budget := by simpa using hbudget

@[simp] theorem append_cubeValue (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    (r.append op hord hbudget).cubeValue = op.act r.cubeValue := by
  exact applyOperations_append r.operations [op] (B.base γ)

end GeneratedRepresentation

end
end C0Absorption

end OAI


