-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Arithmetic
-- name    : HighPrecSAC1_Main_Arithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:23:24.216315+00:00
-- url     : https://prove2.me/theorems/92c34d7a-766b-4d6a-a7a8-ef67bb744e2c
-- title:
--   Literal arithmetic circuits and floating-point approximation families
-- statement:
--   The paper-specific circuit instantiates the separate arithmetic DAG with Boolean literals and constants zero and one. The separate numerical specialization used only in Section 3.1 permits input words and arbitrary valid floating-point constants. Uniformity prints the explicit DAG. The headline approximation interface asserts an actual Boolean circuit family, common computable output widths, size and depth bounds, valid decoding on every Boolean input, both relative-error inequalities, and the stated conditional AC¹ guarantee.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 10 (PDF 11)

import Definitions.Def_HighPrecSAC1_Main_Floating
import Definitions.Def_HighPrecSAC1_Main_ArithmeticCircuit

namespace HighPrecSAC1.Main

inductive Literal (n : ℕ) where
  | input (j : Fin n) (complement : Bool)
  | const (b : Bool)

def Literal.value {n : ℕ} (x : Fin n → Bool) : Literal n → ℕ
  | .input j neg => if (if neg then !(x j) else x j) then 1 else 0
  | .const b => if b then 1 else 0

def Literal.code {n : ℕ} : Literal n → List Bool
  | .input j neg => [false,neg] ++ codeNat j.val
  | .const b => [true,b]

abbrev PositiveCircuit (n : ℕ) := ACircuit (Literal n) 1

def AUniform (G : ∀ n, PositiveCircuit n) : Prop :=
  UniformWords (fun n => codeNat n ++ (G n).description Literal.code)

def APoly (G : ∀ n, PositiveCircuit n) : Prop := PolyBound (fun n => (G n).size)

def AComputes (G : ∀ n, PositiveCircuit n) (F : ∀ n, (Fin n → Bool) → ℕ) : Prop :=
  ∀ n, 1 ≤ n → ∀ x, (G n).eval (Literal.value x) 0 = F n x

/-- Fixed-word numerical atoms used only in §3.1, not in Definition 2.3. -/
abbrev NumericalAtom (m : ℕ) := Fin m ⊕ FloatRep

noncomputable def NumericalAtom.value {m : ℕ} (x : Fin m → ℝ) : NumericalAtom m → ℝ
  | .inl j => x j
  | .inr w => w.value

def NumericalAtom.code {m : ℕ} (p b : ℕ) : NumericalAtom m → List Bool
  | .inl j => [false] ++ codeNat j.val
  | .inr w => [true] ++ (List.finRange (wordLength p b)).map (w.encode p b)

def NumericalConstantsValid {m o : ℕ} (p b : ℕ) (H : ACircuit (NumericalAtom m) o) : Prop :=
  ∀ j w, H.gate j = .atom (.inr w) → w.Valid p b

/-- The output family in the headline theorems; constants and widths are chosen before n,x. -/
noncomputable def Approximates (F : ∀ n, (Fin n → Bool) → ℕ)
    (K t : ℕ → ℕ) (extra : ℕ) (d : ℕ → ℝ) (acCondition : Prop) : Prop :=
  ∃ b : ℕ → ℕ, Parameter b ∧
    Bound (fun n => b n) (fun n => (K n : ℝ) + lg n) ∧
    ∃ C : ∀ n, BCircuit n (wordLength (t n + extra) (b n)),
      BUniform C ∧ BPoly C ∧ BDepthBound C d ∧
      (acCondition → BAC1 C) ∧
      ∀ n, 1 ≤ n → ∀ x,
        ∃ z : ℝ, Encodes (t n + extra) (b n) (bEval (C n) x) z ∧
          (1-err (t n)) * (F n x : ℝ) ≤ z ∧ z ≤ F n x

end HighPrecSAC1.Main


