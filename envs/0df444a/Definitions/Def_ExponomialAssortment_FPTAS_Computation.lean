-- Prove2me | Definitions.Def_ExponomialAssortment_FPTAS_Computation
-- name    : ExponomialAssortment_FPTAS_Computation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:14:44.682437+00:00
-- url     : https://prove2.me/theorems/7ddc3b2a-7a7d-4ae0-9d29-695eb217a1d0
-- title:
--   Computational specification of the cardinality FPTAS
-- statement:
--   Rational binary inputs retain unrestricted real-valued revenue semantics. Outputs encode feasible assortments, with trivial cases returning only the outside option. Polynomial majorants have uniform coefficients and degree; Theorem 5 retains its literal stronger parameter dependence and exact expression output.
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §1.1, §2.4, §5.3, §8, printed 4, 9, 19, 30, PDF 5, 10, 20, 31

import Definitions.Def_ExponomialAssortment_FPTAS_DP
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

noncomputable section

namespace ExponomialAssortment.FPTAS
open scoped BigOperators

structure RationalInput where
  n : ℕ
  outside : Fin n
  price : Fin n → ℚ
  utility : Fin n → ℚ
  rate : ℚ
  capacity : ℕ
  accuracy : ℚ

def RationalInput.model (q : RationalInput) : Instance q.n :=
  ⟨q.outside, (fun i => (q.price i : ℝ)), (fun i => (q.utility i : ℝ))⟩

def InputValid (q : RationalInput) : Prop :=
  (∀ i, 0 ≤ q.price i) ∧ q.price q.outside = 0 ∧ 0 < q.rate ∧
    1 ≤ q.capacity ∧ q.capacity ≤ q.n ∧ 0 < q.accuracy

def NormalInput (q : RationalInput) : Prop :=
  InputValid q ∧ q.rate = 1 ∧ Valid q.model

def encodeInput (q : RationalInput) : List Bool :=
  encodeNat q.n ++ encodeNat q.outside.val ++ encodeNat q.capacity ++
  encodeRat q.rate ++ encodeRat q.accuracy ++
  ((List.finRange q.n).flatMap (fun i => encodeRat (q.price i) ++ encodeRat (q.utility i)))

def encodeSet {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  (List.finRange n).map (fun i => decide (i ∈ S))

def ExactExpr.eval : ExactExpr → ℝ
  | .rational q => q
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .exp a => Real.exp a.eval

def inputRevenue (q : RationalInput) (S : Finset (Fin q.n)) : ℝ :=
  ∑ i ∈ S, (q.price i : ℝ) * probability (fun j => (q.utility j : ℝ)) q.rate S i

/-- Numerical normalization and relabeling, not an assumption of correct optimization. -/
def Represents (q : RationalInput) (I : Instance q.n) (e : Fin q.n ≃ Fin q.n) : Prop :=
  Valid I ∧ I.outside = e.symm q.outside ∧
  ∃ b : ℝ, ∀ i, I.price i = (q.price (e i) : ℝ) ∧
    I.utility i = (q.rate : ℝ) * (q.utility (e i) : ℝ) - b

def SchemeOutput {n : ℕ} (I : Instance n) (C : ℕ) (ε : ℝ)
    (S : Finset (Fin n)) : Prop :=
  if 1 ≤ ε ∨ C = 1 ∨ (∀ i, I.price i = 0) then S = {I.outside}
  else Selected I C (ε / 4) S

def EncodedSchemeOutput (q : RationalInput) (S : Finset (Fin q.n)) : Prop :=
  ∃ I e T, Represents q I e ∧ SchemeOutput I q.capacity q.accuracy T ∧
    S = T.map e.toEmbedding

def RevenueGuarantee {n : ℕ} (I : Instance n) (C : ℕ) (ε : ℝ)
    (S : Finset (Fin n)) : Prop :=
  Feasible I C S ∧ ∀ T, Feasible I C T →
    (1 - ε) * revenue I T ≤ revenue I S ∧
    (ε < 1 → (1 - ε / 4)^4 * revenue I T ≤ revenue I S)

/-- A fixed polynomial majorant in binary input length and inverse accuracy. -/
def HeadlineBound (c d : ℕ) (q : RationalInput) : ℕ :=
  c * (1 + (encodeInput q).length + ⌈1 / (q.accuracy : ℝ)⌉₊)^d

/-- Theorem 5's literal, stronger parameter dependence: no utility/input-length term. -/
def EvaluationBound (c d : ℕ) (q : RationalInput) : ℕ :=
  c * (1 + q.n + ⌈1 / (q.accuracy : ℝ)⌉₊ +
    ⌈Real.log (pmax q.model / pmin q.model)⌉₊)^d

end ExponomialAssortment.FPTAS


