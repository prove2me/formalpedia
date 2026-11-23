-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:06.303588+00:00
-- url     : https://prove2.me/theorems/051d960f-d79d-48d3-9236-bf000cda6911
-- title:
--   Is First Chern Class Of Line Bundle
-- statement:
--   Definitions and structural lemmas for Is First Chern Class Of Line Bundle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsFirstChernClassOfLineBundle.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace GlobalTheory.NeedB
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
def kum {N : ℕ} (ζ θ : Ω) (g : Ω ≃ₐ[K] Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ then h.choose else 0
def Inert (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1
def Over (R : Subring K) (B : ValuationSubring Ω) : Prop :=
  ∀ x ∈ R, algebraMap K Ω x ∈ B
def RY (R : Subring K) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.normalClosure {g | ∃ B : ValuationSubring Ω, Over R B ∧ Inert B g}).topologicalClosure
def ThmA : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ α (g * h) = kum ζ α g + kum ζ α h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ α) ∧
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ β (g * h) = kum ζ β g + kum ζ β h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ β) ∧
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0
def ThmB : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
        (∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0) →
        ∀ r ∈ RY (Ω := Ω) (FunctionField.ringOfIntegers k K).toSubring,
          η r = 0 ∧ kum (N := N) ζ α r = 0 ∧ kum (N := N) ζ β r = 0 ∧ ∀ g, η (g * r) = η g ∧ η (r * g) = η g
def IsFirstChernClassOfLineBundle (K : Type*) [Field K] : Prop :=
  ∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n →
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0
def Tsen : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [FiniteDimensional (RatFunc k) K], IsFirstChernClassOfLineBundle K
def TsenCochain : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra (RatFunc k) K]
    [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ), 0 < N →
    ∀ z : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N,
      IsLocallyConstant (fun p : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) => z p.1 p.2) →
      (∀ g h l, z h l - z (g * h) l + z g (h * l) - z g h = 0) →
      ∃ y : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant y ∧ ∀ g h, z g h = y h - y (g * h) + y g
def ClDiv : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 0 < N →
    ∀ c : ClassGroup (FunctionField.ringOfIntegers k K), ∃ d, c = d ^ N
def PropC : Prop :=
  ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ r ∈ (Subgroup.normalClosure {g : Ω ≃ₐ[F] Ω | (∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
        ∃ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B ∧
          ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1}).topologicalClosure,
      (∀ x : K, r (algebraMap K Ω x) = algebraMap K Ω x) ∧ r ζ = ζ ∧
      ∀ (γ : Ω) (c : F), c ≠ 0 → γ ^ N = algebraMap F Ω c → algebraMap F K c ∈ FunctionField.ringOfIntegers k K →
        (algebraMap F K c)⁻¹ ∈ FunctionField.ringOfIntegers k K → r γ = γ
theorem kum_choose_spec {N : ℕ} {ζ θ : Ω} {g : Ω ≃ₐ[K] Ω} (h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  classical
  unfold kum
  rw [dif_pos h]
  exact h.choose_spec
theorem kum_eq_of {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) {g : Ω ≃ₐ[K] Ω}
    (i : ZMod N) (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i := by
  have hs := kum_choose_spec (N := N) ⟨i, hi⟩
  rw [hi] at hs
  have h2 : ζ ^ i.val = ζ ^ (kum (N := N) ζ θ g).val := mul_right_cancel₀ hθ hs
  exact (ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)).symm
theorem kum_one {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) :
    kum (N := N) ζ θ (1 : Ω ≃ₐ[K] Ω) = 0 :=
  kum_eq_of hζ hθ 0 (by simp)
theorem inert_one (B : ValuationSubring Ω) : Inert B (1 : Ω ≃ₐ[K] Ω) := by
  intro x _
  simp
theorem mem_RY_of_inert (R : Subring K) {B : ValuationSubring Ω} (hB : Over R B) {g : Ω ≃ₐ[K] Ω} (hg : Inert B g) :
    g ∈ RY R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨B, hB, hg⟩)
theorem over_top (R : Subring K) : Over R (⊤ : ValuationSubring Ω) := fun _ _ => trivial
example : Over (⊤ : Subring ℚ) (⊤ : ValuationSubring ℂ) := over_top _
example : (1 : ℂ ≃ₐ[ℚ] ℂ) ∈ RY (⊤ : Subring ℚ) := mem_RY_of_inert _ (over_top _) (inert_one _)
example : kum (N := 2) (-1 : ℂ) 1 (1 : ℂ ≃ₐ[ℚ] ℂ) = 0 :=
  kum_one (IsPrimitiveRoot.neg_one 0 (by norm_num)) one_ne_zero
end GlobalTheory.NeedB


