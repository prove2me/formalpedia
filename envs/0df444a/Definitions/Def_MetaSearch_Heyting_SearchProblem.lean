-- Prove2me | Definitions.Def_MetaSearch_Heyting_SearchProblem
-- name    : MetaSearch_Heyting_SearchProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:21:13.964055+00:00
-- url     : https://prove2.me/theorems/ac9ea684-bc80-4261-bf78-19ed33a7e1e2
-- title:
--   Search problems, polynomial-time computability, Verifiable, FP, mapping reductions, triv and imp (§2.1)
-- statement:
--   A **search problem** is a relation $S\subseteq\{0,1\}^*\times\{0,1\}^*$: on input $x$ the task is to output some $y$ with $(x,y)\in S$. Impossible problems (an input with no valid output) are allowed.
--
--   A function $F:\{0,1\}^*\to\{0,1\}^*$ is **polynomial-time computable** if some machine $M$ and some $k$ satisfy: for every $x$, $M$ on input $x$ halts within $p_k(|x|)$ steps with output $F(x)$. A function $G$ of two strings is polynomial-time computable if some machine on input $\langle x,y\rangle$ halts within $p_k(|x|+|y|)$ steps with output $G(x,y)$.
--
--   $S$ is **(polytime) verifiable** if $S\in\mathsf P$ as a language: some machine $V$ and some $k$ satisfy, for all $x,y$: $V$ on input $\langle x,y\rangle$ halts within $p_k(|x|+|y|)$ steps, and its output is the one-bit string $1$ exactly when $(x,y)\in S$. $\mathsf{Verifiable}$ is the set of verifiable search problems, and
--   $$\mathsf{FP}=\{S\in\mathsf{Verifiable} : \text{some polynomial-time computable } A \text{ has } (x,A(x))\in S \text{ for all } x\}.$$
--
--   A **mapping reduction** from $R$ to $S$ is a pair $(F,G)$ of polynomial-time computable functions, $F$ of one string and $G$ of two, with
--   $$(F(x),y)\in S\;\Longrightarrow\;(x,G(x,y))\in R\qquad\text{for all strings } x,y.$$
--   $R\le S$ (`Reduces R S`) means some mapping reduction from $R$ to $S$ exists. Finally $\mathsf{triv}=\{0,1\}^*\times\{0,1\}^*$ (every output valid) and $\mathsf{imp}=\emptyset$ (no output valid).
--
--   **Formalization Note.** $\le$ is a preorder on all search problems; verifiability is not preserved downwards by reductions, which is why complexity classes are taken inside $\mathsf{Verifiable}$.
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 15-17, §2.1

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine

namespace MetaSearch.Heyting

/-! # Search problems, polynomial-time computability, `Verifiable`, `FP`, mapping reductions,
`triv` and `imp` (§2.1) -/

/-- A search problem: a relation `S ⊆ {0,1}* × {0,1}*`; `(x, y) ∈ S` means `y` is a valid
output for the input `x`. Impossible problems (an input with no valid output) are allowed. -/
abbrev SearchProblem := Set (List Bool × List Bool)

/-- `F : {0,1}* → {0,1}*` is polynomial-time computable: some machine computes `F x` on input
`x` within `p_k(|x|)` steps, for one fixed `k`. -/
def PolyTimeFun (F : List Bool → List Bool) : Prop :=
  ∃ (M : Machine) (k : ℕ), ∀ x, M.evalWithin x (p k x.length) = some (F x)

/-- `G : {0,1}* × {0,1}* → {0,1}*` is polynomial-time computable: some machine computes
`G x y` on input `⟨x, y⟩` within `p_k(|x| + |y|)` steps, for one fixed `k`. -/
def PolyTimeFun₂ (G : List Bool → List Bool → List Bool) : Prop :=
  ∃ (M : Machine) (k : ℕ), ∀ x y,
    M.evalWithin (pair x y) (p k (x.length + y.length)) = some (G x y)

/-- `S` is polytime verifiable (`S ∈ P` as a language): some machine halts on every input
`⟨x, y⟩` within `p_k(|x| + |y|)` steps and outputs `1` exactly when `(x, y) ∈ S`. -/
def IsVerifiable (S : SearchProblem) : Prop :=
  ∃ (V : Machine) (k : ℕ), ∀ x y, ∃ o,
    V.evalWithin (pair x y) (p k (x.length + y.length)) = some o ∧ (o = [true] ↔ (x, y) ∈ S)

/-- `Verifiable = Search ∩ P`. -/
def Verifiable : Set SearchProblem := {S | IsVerifiable S}

/-- `FP`: the polytime verifiable search problems with a polynomial-time algorithm mapping
each `x` to some valid output. -/
def FP : Set SearchProblem :=
  {S | IsVerifiable S ∧ ∃ A, PolyTimeFun A ∧ ∀ x, (x, A x) ∈ S}

/-- A mapping reduction from `R` to `S`: polynomial-time `F` and `G` with
`(F x, y) ∈ S → (x, G x y) ∈ R` for all strings `x, y`. -/
def IsReduction (R S : SearchProblem) (F : List Bool → List Bool)
    (G : List Bool → List Bool → List Bool) : Prop :=
  PolyTimeFun F ∧ PolyTimeFun₂ G ∧ ∀ x y, (F x, y) ∈ S → (x, G x y) ∈ R

/-- `R ≤ S`: `R` reduces to `S` by some mapping reduction. -/
def Reduces (R S : SearchProblem) : Prop :=
  ∃ F G, IsReduction R S F G

/-- `triv`: every output is valid for every input. -/
def triv : SearchProblem := Set.univ

/-- `imp`: no output is valid for any input. -/
def imp : SearchProblem := ∅

end MetaSearch.Heyting


