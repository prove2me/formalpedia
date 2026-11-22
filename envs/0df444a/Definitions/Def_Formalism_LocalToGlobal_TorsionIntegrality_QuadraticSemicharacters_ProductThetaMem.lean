-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:17.176096+00:00
-- url     : https://prove2.me/theorems/d17b810f-a0ad-487c-b3fb-0837ecc54531
-- title:
--   Product Theta Mem
-- statement:
--   Definitions and structural lemmas for Product Theta Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/ProductThetaMem.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
def F0 (L : PeriodPair) (ω₀ : ℂ) (n : Type*) [Fintype n] : (n → ℂ) → ℂ :=
  prodFn fun _ : n => Formalism.L2.Th1.F.th0 L (ω₀ / 2)
def stdChar (L : PeriodPair) (ω₀ : ℂ) {n : Type*} [Fintype n] (x : n → ℂ) : ℂ :=
  ∏ i, Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ (x i)
def qOf {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℝ) (H : Sesq V) (x : V) : ℝ := c * (H x x).re
def alphaQ {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℝ) (H : Sesq V) (x : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (qOf c H x : ℂ))
def StdSelfDual : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n], IsSelfDual (stdH L n) (stdLat L n)
def StdSemiChar : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice →
    IsSemiChar (stdH L n) (stdLat L n) (stdChar L ω₀)
def ProductThetaMem : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ α : (n → ℂ) → ℂ, (∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) →
      F0 L ω₀ n ∈ Th (stdH L n) α (stdLat L n) ∧ F0 L ω₀ n 0 = 1
def ThStd : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ α : (n → ℂ) → ℂ, (∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) →
      ∀ F ∈ Th (stdH L n) α (stdLat L n), F = F 0 • F0 L ω₀ n
def Tens4Mem : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ)
    (θ : Fin 4 → (n → ℂ) → ℂ), (∀ a, θ a ∈ Th (matH h) α Λ) →
      (fun v => ∏ a, θ a (slice a v)) ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ)
def FourthRoot : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ), α 0 = 1 →
    ∀ P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ), P ≠ 0 →
    (∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ), ∃ c : ℂ, G = c • P) →
    (∃ θ ∈ Th (matH h) α Λ, tens4 θ = P) ∧
    ∀ θ ∈ Th (matH h) α Λ, tens4 θ = P →
      (∀ θ' ∈ Th (matH h) α Λ, tens4 θ' = P → ∃ ζ : ℂ, ζ ^ 4 = 1 ∧ θ' = ζ • θ) ∧
      ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ
structure StdData (L : PeriodPair) (ω₀ : ℂ) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Prop where
  per : ω₀ ∈ L.lattice
  half : ω₀ / 2 ∉ L.lattice
  isom : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
  alpha0 : α 0 = 1
  betaStd : ∀ x ∈ stdLat L (Fin 4 × n), β x = stdChar L ω₀ x
  betaSemi : IsSemiChar (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β
  betaAlpha : ∀ x, β (g x) = ∏ a, α (slice a x)
  selfDual : IsSelfDual (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
  idx₁ : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0
  idx₂ : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0
def kernel4 (L : PeriodPair) (ω₀ : ℂ) {n : Type} [Fintype n] [DecidableEq n] (Λ : AddSubgroup (n → ℂ))
    (β : (Fin 4 × n → ℂ) → ℂ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (z : Fin 4 × n → ℂ) : ℂ :=
  inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (F0 L ω₀ (Fin 4 × n)) (g z)
def ThetaVector : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g → ∀ κ : ℂ, κ ≠ 0 →
    (∃ θ ∈ Th (matH h) α Λ, tens4 θ = κ • kernel4 L ω₀ Λ β g) ∧
    ∀ θ ∈ Th (matH h) α Λ, tens4 θ = κ • kernel4 L ω₀ Λ β g → θ ≠ 0 ∧
      (∀ θ' ∈ Th (matH h) α Λ, tens4 θ' = κ • kernel4 L ω₀ Λ β g → ∃ ζ : ℂ, ζ ^ 4 = 1 ∧ θ' = ζ • θ) ∧
      ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ
def AlphaQSemi : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (b : ℤ) (d : ℕ), Odd b →
    ∀ Λ : AddSubgroup V, Λ ≤ dualLat H Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) →
    (∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ)) ∧
    (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x
        - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ)) ∧
    IsSemiChar H Λ (alphaQ (Real.sqrt d / 2) H)
def AlphaQRules : Prop :=
  (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V →ₗ[ℂ] W), IsIsom H H' g → ∀ (c : ℝ) (x : V), alphaQ c H' (g x) = alphaQ c H x) ∧
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (c : ℝ) (x : Fin 4 × n → ℂ),
    alphaQ c (matH (blk4 h)) x = ∏ a, alphaQ c (matH h) (slice a x)
def CmStdChar : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a → d % 8 = 7 →
    ∀ (n : Type) [Fintype n] [DecidableEq n], ∀ x ∈ stdLat (Formalism.L2.Th1.F.cmPair a b d ha hd) n,
      alphaQ (Real.sqrt d / 2) (stdH (Formalism.L2.Th1.F.cmPair a b d ha hd) n) x
        = stdChar (Formalism.L2.Th1.F.cmPair a b d ha hd) (a : ℂ) x
end Formalism.L2.Th1.H


