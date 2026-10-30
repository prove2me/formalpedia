-- Prove2me | Definitions.Def_MITMSynthesis_Timed
-- name    : MITMSynthesis_Timed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:50.835102+00:00
-- url     : https://prove2.me/theorems/913b967c-3ad4-4d83-8586-29554ddaf36c
-- title:
--   A tick-counting cost monad for the RAM model
-- statement:
--   The paper analyses its algorithm in the RAM model. Running times are counted here with a cost monad: a computation returns a value together with the number of unit-cost steps it performed.
--
--   1. `pure a` returns $a$ at cost $0$; a sequential composition costs the sum of its parts.
--   2. `tick` is one unit-cost step, `ticks k` is $k$ steps.
--   3. The unit-cost primitives on unitaries are: one multiplication $A B$ (`mulC`), one adjoint $A^\dagger$ (`starC`), and one three-way comparison under a linear order (`cmpC`).
--
--   These are the operations whose counts the running-time bounds of the meet-in-the-middle algorithm are stated in.
--
--   **Formalization Note** `Timed α` is a structure with fields `val : α` and `cost : ℕ` and a `Monad` instance. Treating a product, an adjoint and a comparison of $2^n \times 2^n$ matrices as one step each is the paper's accounting: its bound $O(|V_{n,\mathcal G}|^{\lceil l/2\rceil}\log|V_{n,\mathcal G}|^{\lceil l/2\rceil})$ has no dependence on $n$ beyond $|V_{n,\mathcal G}|$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, footnote 1, p. 4 ("We assume the RAM model of computation throughout this paper.")

import Mathlib

namespace MITMSynthesis


/-- **A tick-counting cost monad** for the RAM model (arXiv:1206.0758v3, footnote 1, p. 4: "We
assume the RAM model of computation throughout this paper."). A computation returns a value
`val` and the number `cost` of unit-cost steps it performed. -/
structure Timed (α : Type) where
  /-- the result -/
  val : α
  /-- the number of unit-cost steps -/
  cost : ℕ

/-- `pure` costs nothing; `bind` adds the costs of both parts. -/
instance : Monad Timed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- One unit-cost step. -/
def tick : Timed Unit := ⟨(), 1⟩

/-- `k` unit-cost steps. -/
def ticks (k : ℕ) : Timed Unit := ⟨(), k⟩

/-- Multiplication of two elements (unitaries), one unit of cost. -/
def mulC {M : Type} [Mul M] (a b : M) : Timed M := ⟨a * b, 1⟩

/-- The adjoint `a†` of an element (unitary), one unit of cost. -/
def starC {M : Type} [Star M] (a : M) : Timed M := ⟨star a, 1⟩

/-- One three-way comparison under a linear order, one unit of cost. -/
def cmpC {κ : Type} [LinearOrder κ] (a b : κ) : Timed Ordering := ⟨compare a b, 1⟩

end MITMSynthesis


