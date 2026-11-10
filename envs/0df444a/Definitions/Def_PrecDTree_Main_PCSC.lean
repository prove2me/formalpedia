-- Prove2me | Definitions.Def_PrecDTree_Main_PCSC
-- name    : PrecDTree_Main_PCSC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:50:47.805031+00:00
-- url     : https://prove2.me/theorems/98f59ac6-14cb-4985-94a5-6e31dfd64f33
-- title:
--   Precedence-Constrained Set Cover f-PCSC, its optimum and bicriteria (α, β) solutions (Problem 2.3)
-- statement:
--   An instance of **f-PCSC** is a family $\mathcal S$ of $m$ subsets of a universe $U=\bigcup\mathcal S$ with $n=|U|$, a partial order $\preceq$ on $\mathcal S$ and $0<f\le 1$. For $\mathcal C\subseteq\mathcal S$, $\mathrm{cov}(\mathcal C)=\bigcup_{C\in\mathcal C}C$. A **feasible solution** is a precedence-closed $\mathcal C$ with $|\mathrm{cov}(\mathcal C)|\ge f\cdot n$, and $\mathrm{OPT}$ is the least $|\mathcal C|$ of a feasible solution. A family $\mathcal C$ meets the **bicriteria ratio** $(\alpha,\beta)$ if
--   $$\mathcal C\ \text{precedence-closed},\qquad |\mathrm{cov}(\mathcal C)|\ \ge\ \frac{f\cdot n}{\beta},\qquad |\mathcal C|\ \le\ \alpha\cdot\mathrm{OPT}:$$
--   it covers a $1/\beta$ fraction of the target while its cost is compared with the optimum for the original target.
--
--   **Formalization Note.** The family is indexed, `S : Fin m → Finset U` (distinct indices may carry equal sets), the order is a relation on the indices, and a subfamily is a `Finset (Fin m)`. The universe is `coverUniverse S = ⋃ᵢ S i`, as on p. 1. `pcscOpt` is `sInf` over $\mathbb N$; the full family is always feasible, so it is a minimum.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 1 and p. 5, §2, Problem 2.3 and 'Approximation conventions'

import Mathlib
import Definitions.Def_PrecDTree_Main_Order

set_option autoImplicit false

/-!
# Precedence-Constrained Set Cover f-PCSC (Problem 2.3) and bicriteria solutions

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), p. 1 (`⋃S = U`), p. 5, §2 (coverage, Problem 2.3, approximation
conventions).

An instance is an indexed family `S : Fin m → Finset U` of `m` sets, a relation `le` on the indices
(a partial order) and `0 < f ≤ 1`. Its universe is `U = ⋃_i S i` (p. 1: "such that ⋃_{S∈S} S = U"),
and `n = |U|`. A subfamily is a set of indices `C : Finset (Fin m)`.
-/

namespace PrecDTree.Main

variable {U : Type} [DecidableEq U] {m : ℕ}

/-- `cov(C) = ⋃_{C ∈ C} C`. -/
def cov (S : Fin m → Finset U) (C : Finset (Fin m)) : Finset U := C.biUnion S

/-- The universe `U = ⋃ S` of the instance. -/
def coverUniverse (S : Fin m → Finset U) : Finset U := Finset.univ.biUnion S

/-- `C` is a feasible f-PCSC solution: precedence-closed with `|cov(C)| ≥ f · n`. -/
def PCSCFeasible (le : Fin m → Fin m → Prop) (S : Fin m → Finset U) (f : ℝ)
    (C : Finset (Fin m)) : Prop :=
  PrecClosedSet le C ∧ f * ((coverUniverse S).card : ℝ) ≤ ((cov S C).card : ℝ)

/-- `OPT` of f-PCSC: the least size of a feasible solution. -/
noncomputable def pcscOpt (le : Fin m → Fin m → Prop) (S : Fin m → Finset U) (f : ℝ) : ℕ :=
  sInf {c | ∃ C : Finset (Fin m), PCSCFeasible le S f C ∧ C.card = c}

/-- `C` is an optimal f-PCSC solution. -/
def IsPCSCOptimal (le : Fin m → Fin m → Prop) (S : Fin m → Finset U) (f : ℝ)
    (C : Finset (Fin m)) : Prop :=
  PCSCFeasible le S f C ∧ ∀ C' : Finset (Fin m), PCSCFeasible le S f C' → C.card ≤ C'.card

/-- `C` meets the bicriteria ratio `(α, β)` (p. 5): it is precedence-closed, covers at least a
`1/β` fraction of the target `f · n`, and its size is at most `α` times the optimum for the
original target `f`. -/
def IsBicriteria (le : Fin m → Fin m → Prop) (S : Fin m → Finset U) (f α β : ℝ)
    (C : Finset (Fin m)) : Prop :=
  PrecClosedSet le C ∧ f * ((coverUniverse S).card : ℝ) / β ≤ ((cov S C).card : ℝ) ∧
    (C.card : ℝ) ≤ α * (pcscOpt le S f : ℝ)

end PrecDTree.Main


