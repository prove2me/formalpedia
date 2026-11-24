-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:47.460826+00:00
-- url     : https://prove2.me/theorems/1dc22d17-2104-4567-a2fe-921656e547f9
-- title:
--   Lower Unipotent Minors
-- statement:
--   Definitions and structural lemmas for Lower Unipotent Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/LowerUnipotentMinors.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
open MvPolynomial Matrix MeasureTheory
abbrev Var (n p q : ℕ) := Fin n × (Fin p ⊕ Fin q)
abbrev Pol (n p q : ℕ) := MvPolynomial (Var n p q) ℂ
def zPlus (n p q : ℕ) : Matrix (Fin n) (Fin p) (Pol n p q) := fun c a => X (c, Sum.inl a)
def zMinus (n p q : ℕ) : Matrix (Fin n) (Fin q) (Pol n p q) := fun c b => X (c, Sum.inr b)
def subst {n p q : ℕ} (yp : Matrix (Fin n) (Fin p) (Pol n p q))
    (ym : Matrix (Fin n) (Fin q) (Pol n p q)) : Pol n p q →ₐ[ℂ] Pol n p q :=
  aeval fun v : Var n p q => Sum.elim (fun a => yp v.1 a) (fun b => ym v.1 b) v.2
def nextRow {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : i.val + 1 < l then a ⟨i.val + 1, h⟩ else 0
section Minors
variable {R : Type*} [CommRing R] {n l : ℕ}
def topMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det
def botMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨n - (i.val + 1) + k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det
def powProd (a : Fin l → ℕ) (m : Fin l → R) : R := ∏ i, m i ^ (a i - nextRow a i)
end Minors
def delPlus {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) : Pol n p q :=
  powProd ap (topMinor (by omega) (zPlus n p q))
def delMinus {n p q : ℕ} (h : p + q ≤ n) (am : Fin q → ℕ) : Pol n p q :=
  powProd am (botMinor (by omega) (zMinus n p q))
def del {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Pol n p q :=
  delPlus h ap * delMinus h am
def lower {n p q : ℕ} (a : Fin p) (b : Fin q) (P : Pol n p q) : Pol n p q :=
  ∑ c : Fin n, pderiv (c, Sum.inl a) (pderiv (c, Sum.inr b) P)
def leftAct {n : ℕ} (p q : ℕ) (h : GL (Fin n) ℂ) : Pol n p q →ₐ[ℂ] Pol n p q :=
  subst (((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map C * zPlus n p q)
    ((h : Matrix (Fin n) (Fin n) ℂ)ᵀ.map C * zMinus n p q)
def rightMul (n : ℕ) {p q : ℕ} (m₁ : Matrix (Fin p) (Fin p) ℂ) (m₂ : Matrix (Fin q) (Fin q) ℂ) :
    Pol n p q →ₐ[ℂ] Pol n p q :=
  subst (zPlus n p q * m₁.map C) (zMinus n p q * m₂.map C)
def compactAct (n : ℕ) {p q : ℕ} (k₁ : Matrix (Fin p) (Fin p) ℂ) (w₁ : ℂˣ)
    (k₂ : Matrix (Fin q) (Fin q) ℂ) (w₂ : ℂˣ) (P : Pol n p q) : Pol n p q :=
  ((w₁ ^ (n : ℤ) * w₂ ^ (-(n : ℤ)) : ℂˣ) : ℂ) • rightMul n k₁ (k₂.map (starRingEnd ℂ)) P
def IsLowerUnipotent {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, i < j → u i j = 0
def IsUpperUnipotent {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0
def fockForm {σ : Type*} [DecidableEq σ] (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ P.support ∪ Q.support,
    ((α.prod fun _ k => k.factorial : ℕ) : ℂ) * coeff α P * starRingEnd ℂ (coeff α Q)
def fockDensity {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℂ) (z : σ → ℂ) : ℝ :=
  ‖eval z P‖ ^ 2 * Real.exp (-∑ v, ‖z v‖ ^ 2) / Real.pi ^ Fintype.card σ
def hookProd {l : ℕ} (a : Fin l → ℕ) : ℝ :=
  (∏ i : Fin l, ((a i + (l - (i.val + 1))).factorial : ℝ)) /
    ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, ((a i : ℝ) - (a j : ℝ) + (j.val : ℝ) - (i.val : ℝ))
section Clauses
variable {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
def KilledByLower : Prop := ∀ (a : Fin p) (b : Fin q), lower a b (del h ap am) = 0
def LeftFixed : Prop :=
  ∀ g : GL (Fin n) ℂ, IsLowerUnipotent (g : Matrix (Fin n) (Fin n) ℂ) →
    leftAct p q g (del h ap am) = del h ap am
def RightFixed : Prop :=
  ∀ (u₁ : Matrix (Fin p) (Fin p) ℂ) (u₂ : Matrix (Fin q) (Fin q) ℂ),
    IsUpperUnipotent u₁ → IsUpperUnipotent u₂ → rightMul n u₁ u₂ (del h ap am) = del h ap am
def LeftWeight : Prop :=
  ∀ (t : Fin n → ℂˣ) (g : GL (Fin n) ℂ),
    (g : Matrix (Fin n) (Fin n) ℂ) = diagonal (fun c => (t c : ℂ)) →
    leftAct p q g (del h ap am) =
      (((∏ c : Fin p, t ⟨c.val, by omega⟩ ^ (-(ap c : ℤ))) *
        ∏ i : Fin q, t ⟨n - 1 - i.val, by omega⟩ ^ (am i : ℤ) : ℂˣ) : ℂ) • del h ap am
def RightWeight : Prop :=
  ∀ (s : Fin p → ℂˣ) (s' : Fin q → ℂˣ),
    rightMul n (diagonal fun a => (s a : ℂ)) (diagonal fun b => (s' b : ℂ)) (del h ap am) =
      (((∏ a, s a ^ ap a) * ∏ b, s' b ^ am b : ℂˣ) : ℂ) • del h ap am
def CompactWeight : Prop :=
  ∀ (u : Fin p → ℂˣ) (v : Fin q → ℂˣ), (∀ a, ‖(u a : ℂ)‖ = 1) → (∀ b, ‖(v b : ℂ)‖ = 1) →
    compactAct n (diagonal fun a => (u a : ℂ) ^ 2) (∏ a, u a)
        (diagonal fun b => (v b : ℂ) ^ 2) (∏ b, v b) (del h ap am) =
      (((∏ a, u a ^ (2 * (ap a : ℤ) + n)) * ∏ b, v b ^ (-(2 * (am b : ℤ)) - n) : ℂˣ) : ℂ) •
        del h ap am
def NormSq : Prop :=
  fockForm (del h ap am) (del h ap am) = ((hookProd ap * hookProd am : ℝ) : ℂ)
def NormSqIntegral : Prop :=
  Integrable (fockDensity (del h ap am)) ∧
    ∫ z, fockDensity (del h ap am) z = hookProd ap * hookProd am
end Clauses
def JointHarmonic : Prop :=
  ∀ (n p q : ℕ) (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    KilledByLower h ap am ∧ LeftFixed h ap am ∧ RightFixed h ap am ∧ LeftWeight h ap am ∧
      RightWeight h ap am ∧ CompactWeight h ap am ∧ NormSq h ap am
def JointHarmonicIntegral : Prop :=
  ∀ (n p q : ℕ) (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    NormSqIntegral h ap am
example : hookProd ![2, 1] = 3 := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [hookProd, Fin.prod_univ_two, h0, h1, Nat.factorial]
  norm_num
example (k m : ℕ) : del (n := 2) (p := 1) (q := 1) le_rfl ![k] ![m] =
    X (0, Sum.inl 0) ^ k * X (1, Sum.inr 0) ^ m := by
  simp [del, delPlus, delMinus, powProd, nextRow, topMinor, botMinor, zPlus, zMinus,
    Matrix.det_unique]
end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials


