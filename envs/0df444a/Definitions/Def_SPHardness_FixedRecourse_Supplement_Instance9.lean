-- Prove2me | Definitions.Def_SPHardness_FixedRecourse_Supplement_Instance9
-- name    : SPHardness_FixedRecourse_Supplement_Instance9
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:59:56.671581+00:00
-- url     : https://prove2.me/theorems/87c36b9d-c956-48e2-a93c-80704581faa6
-- title:
--   Rational instances of problem (9), their encoding, the tolerance bound $\delta/(8\max\{1,\alpha^\top e-\beta\})$, and the $\epsilon$-optimal-decision relation
-- statement:
--   An **instance** of problem (9) is a tuple $I=(k,\alpha,\beta,c)$ with $k\in\mathbb N$, weights $\alpha\in\mathbb Q^k$, budget $\beta\in\mathbb Q$ and cost coefficient $c\in\mathbb Q$. Its **encoding** writes $k$ in self-delimiting binary followed by $\alpha_1,\dots,\alpha_k,\beta,c$, each rational as the sign and binary absolute value of its reduced numerator followed by its binary denominator.
--
--   The instance lies in the **source domain** of Theorem 2 if $\alpha\ge0$, $\beta\ge0$ and $\alpha^\top e\ge\beta$, where $e$ is the all-ones vector. Write
--
--   $$
--   \bar\delta(I)=\left(\frac{\alpha_k}{2k!(1+\alpha_k)(\|\alpha\|_1+2)^k(k+1)^{k+1}\prod_{j=1}^k\alpha_j}\right)^2
--   $$
--
--   for the right-hand side of threshold (7) of Theorem 1 ($\bar\delta(I)=0$ when $k=0$), and $s(I)=\max\{1,\alpha^\top e-\beta\}$. A tolerance $\epsilon$ is **admissible** for $I$ if
--
--   $$
--   0\le\epsilon\quad\text{and}\quad \epsilon<\frac{\delta}{8\,s(I)}\ \text{ for some }\delta<\bar\delta(I),
--   $$
--
--   that is, $\epsilon<\delta/(8\max\{1,\alpha^\top e-\beta\})$ for an accuracy $\delta$ permitted by Theorem 1.
--
--   For a tolerance assignment $\epsilon=\mathrm{tol}(I)$, the search relation **"determine a $\mathrm{tol}$-optimal decision to (9)"** accepts an answer $a$ to a query $q$ when, if $q$ encodes an instance $I$ of the source domain with $\bar\delta(I)>0$, $a$ encodes a rational $x$ that is a $\mathrm{tol}(I)$-optimal decision of (9) for $I$. Queries that encode no such instance impose no condition.
--
--   These are the inputs, outputs and accuracy requirement of Theorem 2.
--
--   **Formalization Note** A reduction queries finite strings, so instance data and returned decisions are rational; every rational instance is an instance of the paper's real problem, and the uniform law and the linear programs stay real. The threshold reuses the published `delta7` and `lastWeight`, so $\alpha_k$ is the last coordinate. Since $\alpha\ge0$, $\bar\delta(I)>0$ exactly when $k\ge1$ and every $\alpha_j>0$; for a zero weight the printed bound (7) divides by zero, and Lean's convention gives $\bar\delta(I)=0$, so no tolerance is admissible there. The encodings are the published `encBin`/`encRat` and are prefix-free, so a string encodes at most one instance.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 8, definition of an ϵ-optimal solution; p. 7, threshold (7); p. 9, the domain α⊤e ≥ β and Theorem 2's bound ϵ < δ/(8 max{1, α⊤e − β}); p. 2, α ∈ ℝ^k_+, β ∈ ℝ_+

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model
import Definitions.Def_SPHardness_FixedRecourse_Supplement_Problem9
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

set_option autoImplicit false

namespace SPHardness.FixedRecourse.Supplement

open QAlgorithms.LocalHamiltonian

/-- A rational instance of problem (9): the dimension `k`, the weights `α ∈ ℚᵏ`, the budget `β ∈ ℚ`
and the first-stage cost `c ∈ ℚ`. -/
structure Inst9 where
  /-- The dimension `k` of the random vector `ξ̃`. -/
  k : ℕ
  /-- The weights `α`. -/
  α : Fin k → ℚ
  /-- The budget `β`. -/
  β : ℚ
  /-- The first-stage cost coefficient `c`. -/
  c : ℚ

namespace Inst9

/-- The weights as a real vector. -/
def αR (I : Inst9) : Fin I.k → ℝ := fun j => (I.α j : ℝ)

/-- The binary encoding of an instance: `k` in self-delimiting binary, then `α₁, …, α_k`, `β` and `c`,
each rational written as the sign and binary absolute value of its reduced numerator followed by its
binary denominator (the published `encBin` / `encRat`). -/
def enc (I : Inst9) : List Bool :=
  encBin I.k ++ (List.finRange I.k).flatMap (fun j => encRat (I.α j)) ++ encRat I.β ++ encRat I.c

/-- The source domain of Theorem 2 (pp. 2, 9): `α ∈ ℝᵏ₊`, `β ∈ ℝ₊`, and the nontrivial case
`αᵀe ≥ β`. -/
def Admissible (I : Inst9) : Prop :=
  (∀ j, 0 ≤ I.α j) ∧ 0 ≤ I.β ∧ I.β ≤ ∑ j, I.α j

/-- The right-hand side of threshold (7) of Theorem 1 for the instance, with `α_k` the last
coordinate (the published `delta7` and `lastWeight`); for `k = 0`, where `α_k` does not exist, it is
`0`. -/
noncomputable def deltaBound (I : Inst9) : ℝ :=
  if h : 0 < I.k then delta7 I.αR (lastWeight h I.αR) else 0

/-- The denominator `max{1, αᵀe − β}` of Theorem 2's tolerance bound. -/
noncomputable def scale (I : Inst9) : ℝ :=
  max 1 ((∑ j, I.αR j) - (I.β : ℝ))

/-- A tolerance `ε` is admissible for `I` in Theorem 2: `ε ≥ 0` and `ε < δ / (8 max{1, αᵀe − β})` for
some accuracy `δ` satisfying (7) of Theorem 1, i.e. `δ < deltaBound I`. -/
def AdmissibleTol (I : Inst9) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∃ δ : ℝ, δ < I.deltaBound ∧ ε < δ / (8 * I.scale)

end Inst9

/-- The search relation "determine an `ε`-optimal decision to (9)" for the tolerance assignment
`tol`: on a query `q` that encodes an instance `I` of the source domain whose threshold (7) is
positive, a legal answer is the encoding `encRat x` of a rational decision `x` that is
`tol I`-optimal for (9). On every other query, every answer is legal. -/
def SolvesEpsOpt9 (tol : Inst9 → ℝ) (q a : List Bool) : Prop :=
  ∀ I : Inst9, I.enc = q → I.Admissible → 0 < I.deltaBound →
    ∃ x : ℚ, a = encRat x ∧ IsEpsOptimal9 I.αR (I.β : ℝ) (I.c : ℝ) (tol I) (x : ℝ)

end SPHardness.FixedRecourse.Supplement


