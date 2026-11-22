-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
-- name    : Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:59.642157+00:00
-- url     : https://prove2.me/theorems/f32e0252-2d27-4c4b-93f5-8bc2f4f4d1f5
-- title:
--   Lift Unitary Fixes Base
-- statement:
--   Definitions and structural lemmas for Lift Unitary Fixes Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/LiftUnitaryFixesBase.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.S6
def StrictUpper {R : Type} [Zero R] {j : ℕ} (A : Matrix (Fin j) (Fin j) R) : Prop :=
  ∀ b a : Fin j, a ≤ b → A b a = 0
def superSum {R : Type} [AddCommMonoid R] {j : ℕ} (A : Matrix (Fin j) (Fin j) R) : R :=
  ∑ a : Fin j, if h : a.val + 1 < j then A a ⟨a.val + 1, h⟩ else 0
def Zj {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] {H : HermSpace K V}
    {r : ℕ} (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) : Matrix (Fin j) (Fin j) K :=
  (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r)))
def CellExt : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      ∃ Y : V →ₗ[K] V, F.LieN Y ∧ F'.LieN Y ∧
        (∀ a : Fin j, Y (F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) =
          ∑ b, A b a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) ∧
        (∀ a : Fin j, Y (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) =
          ∑ b, A' b a • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) ∧
        (∀ w : V, (∀ x ∈ F.Xa j ⊔ F'.Xa j, H.B x w = 0) → Y w = 0) ∧
        F.DPsi Y (superSum A) ∧ F'.DPsi Y (superSum A')
def CellRelevant : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → Relevant F F' →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      superSum A + star (superSum A) = superSum A' + star (superSum A')
def CellRelevantE : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    (∃ μ : K, μ + star μ ≠ 0) → F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → Relevant F F' →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      superSum A = star (superSum A')
def CellRelevantAsm : Prop := CellExt → CellRelevant
def CellRelevantEAsm : Prop := CellRelevant → CellRelevantE
def InULift {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (Wt : Submodule K V) (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ ∀ y : V, (∀ w ∈ Wt, H.B y w = 0) → g y = y
def LiftUnitaryFixesBase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V) (g : V →ₗ[K] V), IsLift F F' Wt → InULift H Wt g →
      (∀ y ∈ V0 F F', g y = y) ∧ (∀ a : Fin (r + 1), g (F.e a) = F.e a) ∧
      (∀ a : Fin (r + 1), g (F'.e a) = F'.e a)
def LiftAniso : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V), F.Aniso → F'.Aniso → IsLift F F' Wt →
      ∀ w ∈ Wt, H.B w w = 0 → w = 0
def LiftDecomp : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (Wt : Submodule K V),
    F.Aniso → F'.Aniso → IsLift F F' Wt →
      ∀ y : V, ∃! w : V, w ∈ Wt ∧ ∀ w' ∈ Wt, H.B (y - w) w' = 0
def LiftUnitary : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (Wt : Submodule K V) (h : Wt →ₗ[K] Wt),
    F.Aniso → F'.Aniso → IsLift F F' Wt → (∀ x y : Wt, H.B (h x : V) (h y : V) = H.B (x : V) (y : V)) →
      ∃! g : V →ₗ[K] V, InULift H Wt g ∧ Function.Bijective g ∧ ∀ w : Wt, g (w : V) = (h w : V)
def LiftIsoW : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (Wt : Submodule K V),
    NFFull F F' j hj c → IsLift F F' Wt →
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F.X) ∧
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F'.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F'.X)
def ProdLeXi : Prop :=
  ∀ (l : ℕ) (la la' : Fin l → ℝ) (Xi Xi' : ℝ), (∀ a, 0 ≤ la a) → (∀ a, 0 ≤ la' a) →
    (∀ a, la a ≤ Xi) → (∀ a, la' a ≤ Xi') → ∏ a, la a * la' a ≤ (Xi * Xi') ^ l
def SgXi : Prop :=
  ∀ l Xi : ℝ, 0 < l → max 1 (max l (1 / l)) ≤ Xi → 1 ≤ Xi ∧ 1 / Xi ≤ l ∧ l ≤ Xi
def RelIndexInter : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ M W La : AddSubgroup G), La ≤ M ⊓ W →
    (Lam₁ ⊓ W).relIndex La ∣ Lam₁.relIndex M
def IndexChain : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ L W La : AddSubgroup G), Lam₁ ⊓ W ≤ La → La ≤ L ⊓ W →
    Lam₁.relIndex L ≠ 0 →
      La.relIndex (L ⊓ W) * (Lam₁ ⊓ W).relIndex La = (Lam₁ ⊓ W).relIndex (L ⊓ W) ∧
      (Lam₁ ⊓ W).relIndex (L ⊓ W) ≤ Lam₁.relIndex L
def BInGO : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : Set U) (ι' : U → U) (η : U →ₗ[K] U),
    g ∈ O → star g = g → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
    ∀ x' x'' : U, x' ∈ L₀ → x' ∈ L₀' → x'' ∈ L₀ → η x'' ∈ L₀' →
      (∃ l ∈ L₀, ι' x' - x' = g • l) → (∃ l ∈ L₀, ι' (η x'') - x'' = g • l) →
        ∃ t ∈ O, bEta h η x' x'' = g * t
def DetInPow : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R) (s : ℕ) (M : Matrix (Fin s) (Fin s) R),
    (∀ a b, M a b ∈ J) → M.det ∈ J ^ s
def DetBNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g s f : ℕ) (I : Ideal (NumberField.RingOfIntegers E)),
    Module.finrank ℚ E = 2 * f → I ≠ ⊥ →
    I ≤ Ideal.span {(g : NumberField.RingOfIntegers E)} ^ s → g ^ (2 * s * f) ≤ Ideal.absNorm I
def DetBNormAsm : Prop := Formalism.SLP.IdealNormBound → DetBNorm
def mI (f : ℕ) (v dF : ℝ) (Lv : ℕ → ℝ) (i : ℕ) : ℝ :=
  (((i - 1).factorial : ℝ) * (v / Real.pi) ^ i) ^ f * (Real.sqrt dF)⁻¹ * Lv i
def MassRatio : Prop :=
  ∀ (f k s i : ℕ) (v dF Z : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z →
    (∀ j, 3 ≤ j → (Z ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ Z ^ f) → s ≤ k → 3 ≤ i →
      (Real.pi ^ ((k - s) * f))⁻¹ * ((Z ^ 2) ^ f)⁻¹ ≤ mI f v dF Lv (k - s + i) / mI f v dF Lv i
def InvMI : Prop :=
  ∀ (f i : ℕ) (v dF Z : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z → 3 ≤ i → (Z ^ f)⁻¹ ≤ Lv i →
    (mI f v dF Lv i)⁻¹ ≤ Real.pi ^ (i * f) * Z ^ f * Real.sqrt dF
def XiSBound : Prop :=
  ∀ (f k s : ℕ) (v dF Z Hh : ℝ) (Lv mass : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z → 1 ≤ Hh →
    (∀ j, 3 ≤ j → (Z ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ Z ^ f) →
    (∀ j, 3 ≤ j → mass j = mI f v dF Lv j * mass (j - 1)) →
    0 < mass 1 → 0 < mass 2 → mass 1 ≤ Hh → mass 2 ≤ Hh → dF ≤ Hh → 3 ≤ k → 1 ≤ s → s < k →
      mass s * mass (k - s) / mass k ≤ Hh ^ 2 * (Real.pi * Z ^ 2) ^ (s * k * f)
def IsoTorsor : Prop :=
  ∀ (R K A B : Type) [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (qA : A → A → K) (qB : B → B → K),
    Finite {φ : B ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qB x y} →
      Finite {φ : A ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qA x y} ∧
      Nat.card {φ : A ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qA x y} ≤
        Nat.card {φ : B ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qB x y}
def PairsLoss : Prop :=
  ∀ (C s k : ℕ) (D' D'' NT Hh S' S'' : ℝ), s ≤ k → 1 ≤ Hh → 1 ≤ S' → 1 ≤ S'' → 0 ≤ D' → 0 ≤ D'' →
    0 ≤ NT → D' ≤ Hh * S' ^ 2 → D'' ≤ Hh * S'' ^ 2 → NT ≤ Hh →
      (D' * D'' * NT) ^ (C * s) ≤ Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * k)
def RatioSum : Prop :=
  ∀ (C k f : ℕ) (g Hh : ℝ), 0 < g → 1 ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      ∑ s ∈ Finset.Icc 1 (k - 1),
        ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ 1
def RatioBound : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ C₀ : ℕ, ∀ (k r f : ℕ) (b g : ℝ), 2 ≤ b → 1 ≤ f → Real.log f ≤ (r : ℝ) ^ 2 →
    C₀ * (2 * r + 2) ^ 2 ≤ k → ((k : ℝ) * b) ^ 8 ≤ g →
      ((C : ℝ) / g) ^ (k * f) * (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2
def SEqKCount : Prop :=
  ∀ (k f : ℕ) (g' g'' Hh S' S'' : ℝ), 1 ≤ k → 1 ≤ f → Real.log f ≤ k → 1 ≤ Hh → 1 ≤ S' → 1 ≤ S'' →
    0 ≤ g' → 0 ≤ g'' → g' ≤ Hh * S' ^ 2 → g'' ≤ Hh * S'' ^ 2 →
      (g' * g'') ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f))) ≤ Hh ^ (10 * k) * (S' * S'') ^ (10 * k)
def SEqKClose : Prop :=
  ∀ (C k f : ℕ) (g Hh NT : ℝ), 4 ≤ C → 0 < g → 1 ≤ Hh → 0 ≤ NT → NT ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hh ^ ((C - 1) * k) ≤ 1
end Formalism.HermitianLatticeCounting.S6


