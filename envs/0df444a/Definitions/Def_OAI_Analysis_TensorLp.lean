-- Prove2me | Definitions.Def_OAI_Analysis_TensorLp
-- name    : OAI_Analysis_TensorLp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:07:35.720257+00:00
-- url     : https://prove2.me/theorems/abdb186b-abdd-4dd3-bf4c-5087fbe3a503
-- title:
--   Tensor products, slices and operator lifts on $\ell^2(A\times B)$
-- statement:
--   This file realises the Hilbert tensor product of two sequence spaces concretely as $\ell^2(A\times B)$ and sets up the elementary operations on it: product vectors, slices along the second factor, and the lift $Z\otimes 1$ of an operator on the first factor.
--
--   Throughout, $A$ and $B$ are arbitrary index types and $\ell^2(A) = \ell^2(A;\mathbb{C})$ is the Hilbert space of square-summable complex families, with $\|x\|^2 = \sum_a|x_a|^2$.
--
--   1. **Product vectors.** For $x\in\ell^2(A)$ and $y\in\ell^2(B)$ the family $(x\otimes y)(a,b) = x_a\,y_b$ lies in $\ell^2(A\times B)$ and
--   $$
--   \|x\otimes y\| = \|x\|\,\|y\| .
--   $$
--   For fixed $y$ the map $x\mapsto x\otimes y$ is a bounded linear map $\ell^2(A)\to\ell^2(A\times B)$ (with bound $\|y\|$), and for fixed $x$ the map $y\mapsto x\otimes y$ is bounded linear with bound $\|x\|$.
--
--   2. **Slices.** For $z\in\ell^2(A\times B)$ and $b\in B$ the slice $z_b = (z(a,b))_{a\in A}$ lies in $\ell^2(A)$, $\sum_b\|z_b\|^2 = \|z\|^2$, and $\|z_b\|\le\|z\|$; the slice map $z\mapsto z_b$ is a bounded linear map of norm at most $1$.
--
--   3. **Lifting operators on the first factor.** For a bounded operator $Z$ on $\ell^2(A)$ define $(Z\otimes 1)z$ by applying $Z$ slice by slice:
--   $$
--   \bigl((Z\otimes 1)z\bigr)(a,b) = (Z z_b)(a).
--   $$
--   This is a bounded operator on $\ell^2(A\times B)$ with $\|(Z\otimes1)z\|\le\|Z\|\,\|z\|$; its slices are $((Z\otimes1)z)_b = Zz_b$, and the lift is unital and multiplicative: $1\otimes 1 = 1$ and $(ZT)\otimes 1 = (Z\otimes1)(T\otimes1)$.
--
--   These constructions provide the two-port Hilbert space $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$ used for beam-splitter mixing, the product states $x\otimes y$ of the two inputs, and the operators $Z\otimes 1$ that act on one output port only, which is what is needed to express partial traces.
--
--   **Formalization Note** All spaces are Mathlib's `lp (fun _ => ℂ) 2`; the bounded maps are built with `LinearMap.mkContinuous` from the stated norm bounds (`tensorRight`, `tensorLeft`, `sliceCLM`, `liftLeft`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TensorLp.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TensorLp.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace TensorLp
variable {A B : Type*}
abbrev H (A : Type*) := lp (fun _ : A => ℂ) 2

theorem hasSum_square (x : H A) : HasSum (fun a => ‖x a‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.hasSum_norm (p := 2) (by norm_num) x)

theorem tensor_mem (x : H A) (y : H B) :
    Memℓp (fun ab : A × B => x ab.1 * y ab.2) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow] using
    (hasSum_square x).summable.mul_of_nonneg (hasSum_square y).summable
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

def tensor (x : H A) (y : H B) : H (A × B) := ⟨_, tensor_mem x y⟩
@[simp] theorem tensor_apply (x : H A) (y : H B) (a : A) (b : B) :
    tensor x y (a,b) = x a*y b := rfl

theorem tensor_norm_sq (x : H A) (y : H B) : ‖tensor x y‖^2 = ‖x‖^2*‖y‖^2 := by
  apply (hasSum_square (tensor x y)).unique
  have hd := (hasSum_square x).summable.mul_of_nonneg (hasSum_square y).summable
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  change HasSum (fun ab : A × B => ‖x ab.1*y ab.2‖^2) _
  simpa only [norm_mul, mul_pow] using
    (hasSum_square x).mul (hasSum_square y) hd

theorem tensor_norm (x : H A) (y : H B) : ‖tensor x y‖ = ‖x‖*‖y‖ := by
  have h := tensor_norm_sq x y
  have he : ‖tensor x y‖^2 = (‖x‖*‖y‖)^2 := by rw [mul_pow, h]
  nlinarith [norm_nonneg (tensor x y), mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem slice_mem (z : H (A × B)) (b : B) : Memℓp (fun a => z (a,b)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  have hs : Summable (fun a => ‖z (a,b)‖^2) :=
    (hasSum_square z).summable.comp_injective (fun a c h => congrArg Prod.fst h)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

def slice (z : H (A × B)) (b : B) : H A := ⟨_, slice_mem z b⟩
@[simp] theorem slice_apply (z : H (A × B)) (b : B) (a : A) : slice z b a = z (a,b) := rfl

theorem hasSum_slice_norm_sq (z : H (A × B)) : HasSum (fun b => ‖slice z b‖^2) (‖z‖^2) := by
  have hs := (hasSum_square z).summable
  have hp (b : B) : (∑' a, ‖z (a,b)‖^2) = ‖slice z b‖^2 := (hasSum_square (slice z b)).tsum_eq
  have ht : (∑' b, ∑' a, ‖z (a,b)‖^2) = ‖z‖^2 := by
    calc
      _ = ∑' a, ∑' b, ‖z (a,b)‖^2 :=
        Summable.tsum_comm (f := fun a b => ‖z (a,b)‖^2) hs
      _ = ∑' ab : A × B, ‖z ab‖^2 := hs.tsum_prod.symm
      _ = ‖z‖^2 := (hasSum_square z).tsum_eq
  have hh := hs.prod_symm.prod.hasSum
  have hh' := ht ▸ hh
  simpa only [Prod.swap_prod_mk, hp] using hh'

theorem slice_norm_le (z : H (A × B)) (b : B) : ‖slice z b‖ ≤ ‖z‖ := by
  have h := (hasSum_slice_norm_sq z).summable.le_tsum b (fun _ _ => sq_nonneg _)
  rw [(hasSum_slice_norm_sq z).tsum_eq] at h
  nlinarith [norm_nonneg z, norm_nonneg (slice z b)]

def sliceCLM (b : B) : H (A × B) →L[ℂ] H A :=
  LinearMap.mkContinuous
    { toFun := fun z => slice z b
      map_add' := fun x y => by apply lp.ext; rfl
      map_smul' := fun c x => by apply lp.ext; rfl }
    1 (fun z => by change ‖slice z b‖ ≤ 1*‖z‖; simpa only [one_mul] using slice_norm_le z b)

@[simp] theorem sliceCLM_apply (b : B) (z : H (A × B)) : sliceCLM b z = slice z b := rfl

end TensorLp

namespace TensorLp
variable {A B : Type*}

def tensorRight (y : H B) : H A →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := fun x => tensor x y
      map_add' := fun x z => by
        apply lp.ext
        funext ab
        change (x ab.1 + z ab.1)*y ab.2 = x ab.1*y ab.2 + z ab.1*y ab.2
        ring
      map_smul' := fun c x => by apply lp.ext; funext ab; simp [tensor, mul_assoc] }
    ‖y‖ (fun x => by change ‖tensor x y‖ ≤ ‖y‖*‖x‖; rw [tensor_norm, mul_comm])

@[simp] theorem tensorRight_apply (y : H B) (x : H A) : tensorRight y x = tensor x y := rfl

def tensorLeft (x : H A) : H B →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := fun y => tensor x y
      map_add' := fun y z => by
        apply lp.ext
        funext ab
        change x ab.1*(y ab.2 + z ab.2) = x ab.1*y ab.2 + x ab.1*z ab.2
        ring
      map_smul' := fun c y => by apply lp.ext; funext ab; simp [tensor, mul_left_comm] }
    ‖x‖ (fun y => by change ‖tensor x y‖ ≤ ‖x‖*‖y‖; rw [tensor_norm])

@[simp] theorem tensorLeft_apply (x : H A) (y : H B) : tensorLeft x y = tensor x y := rfl

end TensorLp

namespace TensorLp
variable {A B : Type*}

theorem lift_mem (Z : H A →L[ℂ] H A) (z : H (A × B)) :
    Memℓp (fun ab : A × B => Z (slice z ab.2) ab.1) 2 := by
  have hr : Summable (fun b => ‖Z (slice z b)‖^2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
      ((hasSum_slice_norm_sq z).summable.mul_left (‖Z‖^2))
    intro b
    calc
      _ ≤ (‖Z‖*‖slice z b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) 2
      _ = ‖Z‖^2*‖slice z b‖^2 := mul_pow _ _ _
  have hd : Summable (fun ba : B × A => ‖Z (slice z ba.1) ba.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun b => (hasSum_square (Z (slice z b))).summable, ?_⟩
    simpa only [(hasSum_square _).tsum_eq] using hr
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simpa only [Prod.swap, ENNReal.toReal_ofNat, Real.rpow_two] using hd.prod_symm

def liftVector (Z : H A →L[ℂ] H A) (z : H (A × B)) : H (A × B) :=
  ⟨_, lift_mem Z z⟩

@[simp] theorem liftVector_apply (Z : H A →L[ℂ] H A) (z : H (A × B)) (a : A) (b : B) :
    liftVector Z z (a,b) = Z (slice z b) a := rfl

@[simp] theorem slice_liftVector (Z : H A →L[ℂ] H A) (z : H (A × B)) (b : B) :
    slice (liftVector Z z) b = Z (slice z b) := by apply lp.ext; rfl

theorem liftVector_norm (Z : H A →L[ℂ] H A) (z : H (A × B)) :
    ‖liftVector Z z‖ ≤ ‖Z‖*‖z‖ := by
  have h₁ : Summable (fun b => ‖Z (slice z b)‖^2) := by
    simpa only [slice_liftVector] using (hasSum_slice_norm_sq (liftVector Z z)).summable
  have h₂ := (hasSum_slice_norm_sq z).summable.mul_left (‖Z‖^2)
  have hb (b : B) : ‖Z (slice z b)‖^2 ≤ ‖Z‖^2*‖slice z b‖^2 := by
    calc
      _ ≤ (‖Z‖*‖slice z b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) 2
      _ = _ := mul_pow _ _ _
  have ht := h₁.tsum_le_tsum hb h₂
  have he : (∑' b, ‖Z (slice z b)‖^2) = ‖liftVector Z z‖^2 := by
    simpa only [slice_liftVector] using (hasSum_slice_norm_sq (liftVector Z z)).tsum_eq
  rw [he, tsum_mul_left, (hasSum_slice_norm_sq z).tsum_eq, ← mul_pow] at ht
  nlinarith [norm_nonneg (liftVector Z z), mul_nonneg (norm_nonneg Z) (norm_nonneg z)]

def liftLeft (Z : H A →L[ℂ] H A) : H (A × B) →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := liftVector Z
      map_add' := fun x y => by
        apply lp.ext
        funext ab
        change Z (slice (x+y) ab.2) ab.1 = (Z (slice x ab.2) + Z (slice y ab.2)) ab.1
        rw [show slice (x+y) ab.2 = slice x ab.2 + slice y ab.2 from (sliceCLM ab.2).map_add x y,
          map_add]
      map_smul' := fun c x => by
        apply lp.ext
        funext ab
        change Z (slice (c • x) ab.2) ab.1 = (c • Z (slice x ab.2)) ab.1
        rw [show slice (c • x) ab.2 = c • slice x ab.2 from (sliceCLM ab.2).map_smul c x,
          map_smul] }
    ‖Z‖ (liftVector_norm Z)

@[simp] theorem liftLeft_apply (Z : H A →L[ℂ] H A) (z : H (A × B)) (a : A) (b : B) :
    liftLeft Z z (a,b) = Z (slice z b) a := rfl

@[simp] theorem slice_liftLeft (Z : H A →L[ℂ] H A) (z : H (A × B)) (b : B) :
    slice (liftLeft Z z) b = Z (slice z b) := slice_liftVector Z z b

@[simp] theorem liftLeft_one : liftLeft (B := B) (1 : H A →L[ℂ] H A) = 1 := by
  ext z ab
  rfl

@[simp] theorem liftLeft_mul (Z T : H A →L[ℂ] H A) :
    liftLeft (B := B) (Z*T) = liftLeft Z * liftLeft T := by
  ext z ab
  change Z (T (slice z ab.2)) ab.1 = Z (slice (liftLeft T z) ab.2) ab.1
  rw [slice_liftLeft]

end TensorLp

end

end

end OAI


