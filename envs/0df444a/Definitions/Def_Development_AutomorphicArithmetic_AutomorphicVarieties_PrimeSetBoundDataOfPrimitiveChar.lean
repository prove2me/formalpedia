-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:38:10.048877+00:00
-- url     : https://prove2.me/theorems/a9a00f6b-1591-4024-a3c2-f0642c6e37a6
-- title:
--   Prime Set Bound Data Of Primitive Char
-- statement:
--   Definitions and structural lemmas for Prime Set Bound Data Of Primitive Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace UpperTheory.V
open Formalism.HC UpperTheory.Top
structure BConst where
  R0 : AbF → ℕ
  Rl : ℕ → AbF → ℕ
  CK : ℝ
  CK_pos : 0 < CK
def BConst.R (K : BConst) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) : ℕ := K.R0 M + ∑ l ∈ B', K.Rl l (L l)
def BConst.J (K : BConst) (Ct eps : ℝ) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) : ℝ :=
  2 ^ (K.R M B' L + 2) * (2 * K.CK * Ct / eps) ^ K.R M B' L
def admitted (A1 Ct : ℝ) (e t : ℝ → ℕ) : Prop :=
  ∀ x ≥ (2 : ℝ), 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ A1 ∧ 2 ≤ t x ∧ (t x : ℝ) ≤ x ^ Ct
def PrimePair (m q d : ℕ) : Prop := q.Prime ∧ q % 8 = 3 ∧ d.Prime ∧ d % 16 = 7 ∧ (q * d).Coprime m
def OddPrimesWithRootsOfUnity (B' : Finset ℕ) (L : ℕ → AbF) : Prop := ∀ l ∈ B', l.Prime ∧ l ≠ 2 ∧ (L l).HasMu l
def InRange (J X Y : ℝ) : Prop := X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X
def BaAt (M : AbF) (eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsCompField M (e x) q d E → BoundedHeightTwoPlaceCondition E (t x) (Real.exp (x ^ (4 * eps / 5)))
def BbAt (K : BConst) (B' : Finset ℕ) (L : ℕ → AbF) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) : Prop :=
  ∀ l ∈ B', ∀ [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField (L l) L₀ →
    ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l (Nat.log l (K.Rl l (L l)) + 3) L₀ L₁ →
      VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5)))
def IsBWindow (K : BConst) (Ct eps : ℝ) (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF) (e t : ℝ → ℕ) (q d : ℕ) (X Y : ℝ) : Prop :=
  InRange (K.J Ct eps M B' L) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → BaAt M eps e t q d x ∧ BbAt K B' L eps t x
def BShape (K : BConst) (Ct : ℝ)
    (P : ℝ → AbF → Finset ℕ → (ℕ → AbF) → (ℝ → ℕ) → (ℝ → ℕ) → ℕ → ℕ → ℝ → ℝ → Prop) : Prop :=
  ∀ (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF), OddPrimesWithRootsOfUnity B' L → ∀ eps A1 : ℝ, 0 < eps → eps < 1 / 52 →
    ∃ X0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair M.m q d →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * K.J Ct eps M B' L)) → ∃ Y : ℝ, P eps M B' L e t q d X Y
def ThmBab (K : BConst) (Ct : ℝ) : Prop := BShape K Ct (IsBWindow K Ct)
def ThmBa (K : BConst) (Ct : ℝ) : Prop :=
  BShape K Ct fun eps M B' L e t q d X Y =>
    InRange (K.J Ct eps M B' L) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → BaAt M eps e t q d x
def ThmBb (K : BConst) (Ct : ℝ) : Prop :=
  BShape K Ct fun eps M B' L _ t _ _ X Y =>
    InRange (K.J Ct eps M B' L) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → BbAt K B' L eps t x
def ThmBc (Ct : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (M : AbF) (A1 : ℝ) (e t : ℝ → ℕ), admitted A1 Ct e t → ∀ x ≥ (2 : ℝ), ∀ q d : ℕ, PrimePair M.m q d →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsCompField M (e x) q d E →
      VVminusLe E (t x) (minusBound C M.deg (Module.finrank ℚ E) (condF E) (t x))
def ThmBcFree : Prop :=
  ∃ C : ℝ, ∀ (M : AbF) (e t q d : ℕ), 2 ≤ e → 2 ≤ t → PrimePair M.m q d →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsCompField M e q d E →
      VVminusLe E t (minusBound C M.deg (Module.finrank ℚ E) (condF E) t)
def ThmB (K : BConst) (Ct : ℝ) : Prop := ThmBab K Ct ∧ ThmBc Ct
def Lchi (ψ : PChar) (l : ℕ) : AbF := AbF.cyc (l * ψ.N)
def Jchi (K : BConst) (Ct eps : ℝ) (ψ : PChar) : ℝ := K.J Ct eps (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ)
def HVAt (ψ : PChar) (C eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField ψ (e x) q d E →
    VVplusLe E (t x) (((condF E : ℝ) * t x) ^ C + C * Real.exp (x ^ (4 * eps / 5)))
def ThmHV (K : BConst) (Ct : ℝ) : Prop :=
  ∀ ψ : PChar, ∃ (C : ℝ) (r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ eps A1 : ℝ, 0 < eps → eps < 1 / 52 →
    ∃ X0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair ψ.N q d →
      2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) →
      (∀ y ∈ [ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂], y < q ∧ y < d) →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * Jchi K Ct eps ψ)) →
      ∀ Y : ℝ, IsBWindow K Ct eps (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ) e t q d X Y →
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → HVAt ψ C eps e t q d x
def JointWin (Ct : ℝ) : Prop :=
  ∀ (ψ : PChar) (eps A1 : ℝ), 0 < eps → eps < 1 / 52 → ∀ e t : ℝ → ℕ, admitted A1 Ct e t →
    ∃ (J C P X0 : ℝ), 0 < J ∧ ∀ X ≥ X0, ∀ q d : ℕ, PrimePair ψ.N q d →
      2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) → P < (q : ℝ) → P < (d : ℝ) →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
      ∃ Y : ℝ, InRange J X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        BaAt (AbF.ofChar ψ) eps e t q d x ∧ HVAt ψ C eps e t q d x
end UpperTheory.V
end


