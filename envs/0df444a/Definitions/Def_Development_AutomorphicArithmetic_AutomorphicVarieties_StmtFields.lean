-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:41.006569+00:00
-- url     : https://prove2.me/theorems/79e7b46e-92a7-41d6-b3a9-602058eecf01
-- title:
--   Stmt Fields
-- statement:
--   Definitions and structural lemmas for Stmt Fields, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Polynomial
namespace UpperTheory.V
open Formalism.HC UpperTheory.Top
structure AbF where
  m : ℕ
  pos : 0 < m
  H : Subgroup (ZMod m)ˣ
namespace AbF
def ker (A : AbF) (a : ℕ) : Prop := ∃ u ∈ A.H, ((u : (ZMod A.m)ˣ) : ZMod A.m) = (a : ZMod A.m)
def deg (A : AbF) : ℕ := A.H.index
def HasMu (A : AbF) (l : ℕ) : Prop := l ∣ A.m ∧ ∀ a : ℕ, A.ker a → a ≡ 1 [MOD l]
def ofChar (ψ : PChar) : AbF := ⟨ψ.N, NeZero.pos _, ψ.χ.toUnitHom.ker⟩
def cyc (m : ℕ) : AbF := ⟨max m 1, by omega, ⊥⟩
end AbF
def IsAbField (A : AbF) (L : Type) [Field L] [NumberField L] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : L →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    A.m ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : L, τ (j x) = j x) ↔ A.ker a)
def IsCompField (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ A.m ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)
def condF (E : Type) [Field E] [NumberField E] : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}
def IsLayer (l j : ℕ) (L L' : Type) [Field L] [Field L'] [Algebra L L'] : Prop :=
  (∃ k : ℕ, IsCyclotomicExtension {l ^ k} L L') ∧ Module.finrank L L' = l ^ j
def Kstar (p : ℕ) : Type := (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField
instance (p : ℕ) : Field (Kstar p) := inferInstanceAs (Field (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField)
instance (p : ℕ) : NumberField (Kstar p) :=
  NumberField.of_module_finite ℚ (X ^ 2 + C (p : ℚ) : ℚ[X]).SplittingField
def ordC (ψ : PChar) : ℕ := orderOf ψ.χ
def pK (ψ : PChar) : ℕ := sInf {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}
def hStar (ψ : PChar) : ℕ := classNumber (Kstar (pK ψ))
def pOne (ψ : PChar) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] (ordC ψ)] ∧ p.Coprime (2 * ψ.N * pK ψ)}
def Bchi (ψ : PChar) : Finset ℕ :=
  insert 3 ((ordC ψ * ψ.N * pK ψ * hStar ψ * pOne ψ).primeFactors.erase 2)
def minusBound (C : ℝ) (o n N t : ℕ) : ℝ :=
  3 * n * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) +
    C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * l * N) ^ 2
end UpperTheory.V
end


