-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
-- name    : Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:31.027858+00:00
-- url     : https://prove2.me/theorems/f1156cec-a968-46cb-b307-2d4a172c7e1a
-- title:
--   Rational Matrix Prime Order Bound
-- statement:
--   Definitions and structural lemmas for Rational Matrix Prime Order Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/RationalMatrixPrimeOrderBound.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.RamifiedHeckeModels
open Finset Matrix ComplexConjugate Formalism.HermitianLattices.LocalLatticeBases
def RationalMatrixPrimeOrderBound : Prop :=
  ∀ (n p : ℕ), p.Prime → ∀ A : Matrix (Fin n) (Fin n) ℚ, A ^ p = 1 → A ≠ 1 → p ≤ n + 1
def LogRatioAtMostOne : Prop := ∀ q : ℕ, 3 ≤ q → Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2) ≤ 1
def LemmaC_twist : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      (∀ s ∈ S, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R (S ⧸ (S.map ((ϖ ^ b) • U)).comap S.subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)
def LemmaC_twist_ram : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)
def TableauExponentRange : Prop :=
  ∀ (μ : YoungDiagram) (T : SemistandardYoungTableau μ) (j : ℕ),
    (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ μ.rowLen 0
def ConjRatioPowUnitModulus : Prop :=
  ∀ (z : ℂ) (g : ℕ), z ≠ 0 →
    ‖(z / conj z) ^ g‖ = 1 ∧ ((Complex.normSq z : ℝ) : ℂ) ^ g * (z / conj z) ^ g = z ^ (2 * g)
def HeckeKernelPreservesRamified : Prop :=
  ∀ (q : ℕ) [NeZero q] (n n' : ℕ) (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ),
    (∀ f, ∑ c : (ZMod q)ˣ, ph ((c : ZMod q) • f) = 0) →
    ∀ fW : Fin n' → ZMod q, ∑ c : (ZMod q)ˣ, kerK w ph ((c : ZMod q) • fW) = 0
def LatticeColumnOperatorBound : Prop :=
  ∀ (O L : Type) [CommRing O] [Field L] [Algebra O L] (M : ℕ → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module L (M i)] [∀ i, Module O (M i)] [∀ i, IsScalarTower O L (M i)]
    (S : ∀ i, Submodule O (M i)) (U : ∀ j, Module.End L (M j)) (K : ∀ j, M j →ₗ[L] M (j + 1))
    (c : ℕ → Lˣ) (ϖ : O) (e1 : ℕ) (w : ℕ → ℕ),
    (∀ j, (U (j + 1)).comp (K j) = (c j : L) • (K j).comp (U j)) →
    (∀ j, ∀ s ∈ S j, ϖ ^ e1 • (U (j + 1)) (K j s) ∈ S (j + 1)) →
    (∀ j, ∃ r : O, algebraMap O L r = ((c j)⁻¹ : Lˣ) * algebraMap O L ϖ ^ w j) →
    ∀ m : ℕ, ∀ s ∈ S 0,
      ϖ ^ (m * e1 + ∑ j ∈ range m, (m - j) * w j) • chainK L M K m (((U 0) ^ m) s) ∈ S m
def CauchySchwarzUnitModulus : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y y' : V) (T : ℝ) (ε : ℂ), 0 < T →
    ‖y‖ ^ 2 = 1 / T → ‖y'‖ ^ 2 = 1 / T →
    (‖(T : ℂ) * inner ℂ y y'‖ ≤ 1) ∧
    ((ε = 1 ∨ ε = -1) → (T : ℂ) * inner ℂ y y' = ε → y' = ε • y)
def ImprimitiveOrbitCondition : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (f : Fin n → ZMod q) (e : Fin n → ℤ) (xz : Fin n → ℚ),
    (∑ j, f j * (e j : ZMod q)) = 1 →
    (∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
      (∑ j, xz j * l j) ∈ Set.range (Int.cast : ℤ → ℚ)) →
    (∃ z : ℤ, (q : ℚ) * ∑ j, xz j * e j = z ∧ (z : ZMod q) = 1) →
    (¬ ∀ j, xz j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ j, (q : ℚ) * xz j ∈ Set.range (Int.cast : ℤ → ℚ))
end Formalism.HermitianLattices.RamifiedHeckeModels


