-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
-- name    : Formalism_PeriodIntegrals_JointBlockShapes_JointShape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:10.458672+00:00
-- url     : https://prove2.me/theorems/28e49474-d767-49bc-97a6-9b7e742840a3
-- title:
--   Joint Shape
-- statement:
--   Definitions and structural lemmas for Joint Shape, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/JointBlockShapes/JointShape.lean

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace FockH1Action
def posC {p q : ℕ} : Ix p q → Ix p q → Prop
  | .inl i, .inl j => i < j
  | .inr i, .inr j => i < j
  | _, _ => False
def Eab {p q : ℕ} (a b : Ix p q) : Mat p q := Matrix.single a b 1
section Modules
variable {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
def wtSub (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) : Submodule ℂ V :=
  ⨅ a, LinearMap.ker (act (Eab a a) - ((μ a : ℚ) : ℂ) • LinearMap.id)
def hwSub (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) : Submodule ℂ V :=
  wtSub act μ ⊓ ⨅ a, ⨅ b, ⨅ (_ : posC a b), LinearMap.ker (act (Eab a b))
def IsHW (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ hwSub act μ
def KStable (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) : Prop :=
  ∀ X, IsKC X → ∀ w ∈ W, act X w ∈ W
def OfType (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) : Prop :=
  ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧ KStable act W ∧
    ∀ (ν : Ix p q → ℚ) (w : V), w ∈ W → IsHW act ν w → ν = μ
end Modules
def shiftNu {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) : Ix p q → ℚ
  | .inl i => μ (.inl i) - c
  | .inr j => μ (.inr j) + c
def degW {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) : ℚ := ∑ a, |shiftNu c μ a|
def cPair (r s : ℕ) : ℚ := ((r : ℚ) - (s : ℚ)) / 2
def ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) : Ix p q → ℚ
  | .inl i => l₁.getD i 0
  | .inr j => l₂.getD j 0
def pad (x : List ℤ) (k : ℕ) (y : List ℤ) : List ℚ :=
  (x ++ List.replicate k 0 ++ y).map (fun v : ℤ => (v : ℚ))
def JointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  ∃ a b c d : List ℤ,
    (∀ v ∈ a, 0 < v) ∧ (∀ v ∈ c, 0 < v) ∧ (∀ v ∈ b, v < 0) ∧ (∀ v ∈ d, v < 0) ∧
    a.Pairwise (· ≥ ·) ∧ b.Pairwise (· ≥ ·) ∧ c.Pairwise (· ≥ ·) ∧ d.Pairwise (· ≥ ·) ∧
    a.length + b.length ≤ p ∧ c.length + d.length ≤ q ∧
    a.length + d.length ≤ r ∧ c.length + b.length ≤ s ∧
    shiftNu (cPair r s) μ =
      ofBlocks (pad a (p - a.length - b.length) b) (pad c (q - c.length - d.length) d) ∧
    shiftNu (cPair p q) μ' =
      ofBlocks (pad a (r - a.length - d.length) d) (pad c (s - c.length - b.length) b)
def Jset (p q r s : ℕ) : Set (Pol p q r s) :=
  {P | (∀ X, IsPC X → minusPart (fockAct1 p q r s X) P = 0) ∧ (∀ Y, IsPC Y → minusPart (fockAct2 p q r s Y) P = 0)}
def lowKer (p q r s : ℕ) (u1 u2 : Bool) : Set (Pol p q r s) :=
  {P | (u1 = true → ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) P = 0) ∧
    (u2 = true → ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0)}
def raised (p q r s : ℕ) (u1 u2 : Bool) (d : ℕ) : Set (Pol p q r s) :=
  {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
    (u1 = true ∧ ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
    (u2 = true ∧ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q)}
def H2 : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct1 p q r s) μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct2 p q r s) μ P →
    degW (cPair p q) μ ≤ d) ∧
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s) = ⊥)) ∧
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer p q r s u1 u2)) ⊔
      Submodule.span ℂ (raised p q r s u1 u2 d))
end FockH1Action


