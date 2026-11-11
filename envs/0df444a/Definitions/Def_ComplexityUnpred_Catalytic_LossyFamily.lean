-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_LossyFamily
-- name    : ComplexityUnpred_Catalytic_LossyFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:04:25.110455+00:00
-- url     : https://prove2.me/theorems/0919f269-989a-498b-b3d2-0ba057e67082
-- title:
--   LossyCoding families, polynomial-time pair maps and polynomial-time inplaceFL machines with advice (Definitions 2.13, 4.12)
-- statement:
--   A **LossyCoding family** is given by $n:\{0,1\}^*\to\mathbb N$ and, for every $x\in\{0,1\}^*$, $C_x:\{0,1\}^{n(x)}\to\{0,1\}^{n(x)-1}$ and $D_x:\{0,1\}^{n(x)-1}\to\{0,1\}^{n(x)}$. **LossyCoding on $(C_x,D_x)_x$** is the search problem with input $x$ (every string is valid) whose solutions are the $y\in\{0,1\}^{n(x)}$ with $D_x(C_x(y))\neq y$.
--
--   $(x,y)\mapsto C_x(y)$ is **polynomial-time computable** if a polynomial-time Turing machine maps the pair $(x,y)$, for every $y\in\{0,1\}^{n(x)}$, to $C_x(y)$.
--
--   A **polynomial-time inplaceFL machine with read-only advice $x$** computing maps $F_x:\{0,1\}^{n(x)}\to\{0,1\}^{n(x)}$ is a machine with read-only access to $x$, a read-write input tape holding $y$ of length exactly $n(x)$ and a work tape, which for every $x$ and $y$ halts within $C(|x|+2)^k$ steps with $F_x(y)$ on its input tape, using at most $C(\lfloor\log_2(|x|+2)\rfloor+1)$ work cells (efficiency is measured in $|x|$).
--
--   These are the hypotheses and conclusions of Theorems 4.18 and 4.19, the reductions FastCatTape $\to$ LossyCoding $\to$ WeakExcess.
--
--   **Formalization Note** Pairs $(x,y)$ use the tagged-pair string of the published `CardinalMatching.SearchReduces`, and polynomial time is the published `CookPvsNP.PolyTimeComputable`. The in-place machine with advice is the published catalytic machine with the advice $x$ on its read-only input tape and $y$ on its catalytic tape, which is *not* restored: it must hold $F_x(y)$ at the halt. Its catalytic tape has exactly $n(x)$ cells, as the paper's in-place input tape ("the input tape has size exactly $|x|$", p. 22).
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 22, Definition 2.13; p. 34, Definition 4.12 and the text after it; pp. 37, 39, conditions of Theorems 4.18–4.19

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ComplexityUnpred_Catalytic_FastCatTape
import Definitions.Def_ComplexityUnpred_Catalytic_LossyCoding

namespace ComplexityUnpred.Catalytic

open CatalyticMatching.General

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1: LossyCoding
families (Definition 4.12, p. 34) and the resource conditions of Theorems 4.18–4.19 (pp. 37,
39): polynomial-time computation of `C_x(y)` from `(x, y)`, and polynomial-time `inplaceFL`
computation of `D^ext_x(y)` with read-only advice `x` (Definition 2.13, p. 22; p. 34).

A LossyCoding family is given by the length map `n : {0,1}* → ℕ` and, for every `x`,
`C_x : {0,1}^{n(x)} → {0,1}^{n(x)−1}` and `D_x : {0,1}^{n(x)−1} → {0,1}^{n(x)}`. -/

/-- The pair `(x, y)` as one string over `Option (Bool ⊕ Bool)`: `x`, a separator, `y` (the same
tagged-pair convention as the published `CardinalMatching.SearchReduces`). -/
def pairCode (x y : List Bool) : List (Option (Bool ⊕ Bool)) :=
  x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)

/-- `(x, y) ↦ C_x(y)` is computable in polynomial time: a polynomial-time Cook machine maps the
pair `(x, y)`, for every `y ∈ {0,1}^{n(x)}`, to `C_x(y)`. -/
def PairPolyTime (n : List Bool → ℕ)
    (C : (x : List Bool) → (Fin (n x) → Bool) → Fin (n x - 1) → Bool) : Prop :=
  ∃ f : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ (x : List Bool) (y : Fin (n x) → Bool), f (pairCode x (List.ofFn y)) = List.ofFn (C x y)

/-- A polynomial-time `inplaceFL` machine with read-only advice `x` computes the
length-preserving maps `F_x : {0,1}^{n(x)} → {0,1}^{n(x)}`. On the published machine model the
advice `x` is the read-only input tape and the read-write input `y` is the catalytic tape (which
need not be restored: it must hold `F_x(y)` at the halt). For every `x` and every
`y ∈ {0,1}^{n(x)}` the machine halts within `C · (|x| + 2)^k` steps with `F_x(y)` on that tape,
having visited at most `C · logBudget(|x|)` work cells (efficiency measured in `|x|`, p. 34). -/
def InPlaceFLPoly (n : List Bool → ℕ)
    (F : (x : List Bool) → (Fin (n x) → Bool) → Fin (n x) → Bool) : Prop :=
  ∃ (M : Machine) (C k : ℕ), 1 ≤ C ∧ ∀ (x : List Bool) (y : Fin (n x) → Bool),
    ∃ t c, t ≤ C * (x.length + 2) ^ k ∧ M.run x (List.ofFn y) t = some c ∧ c.state = none ∧
      c.catalyst = List.ofFn (F x y) ∧ M.workBound x (List.ofFn y) t (C * logBudget x.length)

/-- **Definition 4.12** (p. 34): LossyCoding on the family `(C_x, D_x)_x`, the search problem
with input `x ∈ {0,1}*` (every string valid) whose answers are the strings `y ∈ {0,1}^{n(x)}`
with `D_x(C_x(y)) ≠ y`. -/
def LossyCodingFamily (n : List Bool → ℕ)
    (C : (x : List Bool) → (Fin (n x) → Bool) → Fin (n x - 1) → Bool)
    (D : (x : List Bool) → (Fin (n x - 1) → Bool) → Fin (n x) → Bool) :
    TetrisHard.Rows.SearchProblem where
  valid _ := True
  answer x t := ∃ y : Fin (n x) → Bool, t = List.ofFn y ∧ IsLossySolution (C x) (D x) y

end ComplexityUnpred.Catalytic


