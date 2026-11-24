-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
-- name    : GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:52.714977+00:00
-- url     : https://prove2.me/theorems/a5e70908-3b5e-4fba-8913-bc0265a14543
-- title:
--   Rig Sym Form Tau INontrivial
-- statement:
--   Definitions and structural lemmas for Rig Sym Form Tau INontrivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauINontrivial.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix Real
noncomputable section
structure SiegelPt (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ
  isSymm : τ.IsSymm
  im_posDef : (τ.map Complex.im).PosDef
def intVec {g : ℕ} (v : Fin g → ℤ) : Fin g → ℂ := fun i => (v i : ℂ)
structure HalfChar (g : ℕ) where

  ε : Fin g → Fin 2

  ε' : Fin g → Fin 2
namespace HalfChar
variable {g : ℕ} (m : HalfChar g)
def a : Fin g → ℂ := fun i => ((m.ε i : ℕ) : ℂ) / 2
def b : Fin g → ℂ := fun i => ((m.ε' i : ℕ) : ℂ) / 2
def zero (g : ℕ) : HalfChar g := ⟨fun _ => 0, fun _ => 0⟩
end HalfChar
def autFactor {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) (u : Fin g → ℤ) (z : Fin g → ℂ) :
    ℂ :=
  cexp (-(π * I * n * (intVec u ⬝ᵥ P.τ *ᵥ intVec u)) - 2 * π * I * n * (intVec u ⬝ᵥ (z + m.b)))
def perFactor {g : ℕ} (m : HalfChar g) (n : ℕ) (v : Fin g → ℤ) : ℂ :=
  cexp (2 * π * I * n * (m.a ⬝ᵥ intVec v))
def thetaSec {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) :
    Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ (v : Fin g → ℤ) (z : Fin g → ℂ), f (z + intVec v) = perFactor m n v * f z) ∧
    ∀ (u : Fin g → ℤ) (z : Fin g → ℂ), f (z + P.τ *ᵥ intVec u) = autFactor P m n u z * f z}
  add_mem' := by
    rintro f h ⟨hf, hf1, hf2⟩ ⟨hh, hh1, hh2⟩
    refine ⟨hf.add hh, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.add_apply, hf1, hh1]; ring
    · simp only [Pi.add_apply, hf2, hh2]; ring
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hf2⟩
    refine ⟨hf.const_smul c, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hf2]; ring
lemma perFactor_add {g : ℕ} (m : HalfChar g) (k n : ℕ) (v : Fin g → ℤ) :
    perFactor m k v * perFactor m n v = perFactor m (k + n) v := by
  unfold perFactor
  rw [← Complex.exp_add]; congr 1; push_cast; ring
lemma autFactor_add {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (k n : ℕ) (u : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor P m k u z * autFactor P m n u z = autFactor P m (k + n) u z := by
  unfold autFactor
  rw [← Complex.exp_add]; congr 1; push_cast; ring
theorem thetaSec_mul {g : ℕ} (P : SiegelPt g) (m : HalfChar g) {k n : ℕ}
    {f h : (Fin g → ℂ) → ℂ} (hf : f ∈ thetaSec P m k) (hh : h ∈ thetaSec P m n) :
    f * h ∈ thetaSec P m (k + n) := by
  obtain ⟨hf, hf1, hf2⟩ := hf
  obtain ⟨hh, hh1, hh2⟩ := hh
  refine ⟨hf.mul hh, fun v z => ?_, fun u z => ?_⟩
  · simp only [Pi.mul_apply, hf1, hh1, ← perFactor_add]; ring
  · simp only [Pi.mul_apply, hf2, hh2, ← autFactor_add]; ring
theorem const_mem_thetaSec_zero {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (c : ℂ) :
    (fun _ => c) ∈ thetaSec P m 0 := by
  refine ⟨differentiable_const c, fun v z => ?_, fun u z => ?_⟩
  · simp [perFactor]
  · simp [autFactor]
structure RigSymForm (K : Type) [Field K] [Algebra K ℂ] where

  g : ℕ

  pt : SiegelPt g

  ch : HalfChar g

  S : ℕ → Submodule K ((Fin g → ℂ) → ℂ)
  S_le : ∀ n, ∀ f ∈ S n, f ∈ thetaSec pt ch n
  one_mem : (fun _ => (1 : ℂ)) ∈ S 0
  mul_mem : ∀ k n f h, f ∈ S k → h ∈ S n → f * h ∈ S (k + n)
  span_eq : ∀ n, Submodule.span ℂ (S n : Set ((Fin g → ℂ) → ℂ)) = thetaSec pt ch n
  linIndep : ∀ (n : ℕ) (s : Finset ((Fin g → ℂ) → ℂ)), (↑s : Set ((Fin g → ℂ) → ℂ)) ⊆ S n →
    LinearIndependent K (fun f : s => (f : (Fin g → ℂ) → ℂ)) →
    LinearIndependent ℂ (fun f : s => (f : (Fin g → ℂ) → ℂ))

  rig : ℂˣ
  rig_mem : ∀ n, ∀ f ∈ S n, ∃ c : K, (rig : ℂ) ^ n * f 0 = algebraMap K ℂ c
def tauI : SiegelPt 1 where
  τ := I • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  isSymm := by simp [Matrix.IsSymm, Matrix.transpose_smul]
  im_posDef := by
    have : (I • (1 : Matrix (Fin 1) (Fin 1) ℂ)).map Complex.im = 1 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this]; exact Matrix.PosDef.one
def thetaOneVar : (Fin 1 → ℂ) → ℂ := fun z => jacobiTheta₂ (z 0) I
def rigSymFormTauI : RigSymForm ℂ where
  g := 1
  pt := tauI
  ch := HalfChar.zero 1
  S := fun n => thetaSec tauI (HalfChar.zero 1) n
  S_le := fun _ _ hf => hf
  one_mem := const_mem_thetaSec_zero _ _ 1
  mul_mem := fun _ _ _ _ hf hh => thetaSec_mul _ _ hf hh
  span_eq := fun n => Submodule.span_eq _
  linIndep := fun _ _ _ h => h
  rig := 1
  rig_mem := fun n f _ => ⟨(1 : ℂ) ^ n * f 0, by simp⟩
end
end GroundTheory.Heights₂.Heights.KeyFormula


