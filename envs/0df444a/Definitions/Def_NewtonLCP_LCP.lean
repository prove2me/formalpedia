-- Prove2me | Definitions.Def_NewtonLCP_LCP
-- name    : NewtonLCP_LCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:56.426514+00:00
-- url     : https://prove2.me/theorems/832488e5-b29b-4b23-9494-c0824fca951f
-- title:
--   The linear complementarity problem LCP$(M,q)$ and its feasible regions $\mathcal F$, $\mathcal F_{>0}$
-- statement:
--   Let $M\in\mathbb R^{n\times n}$ and $q\in\mathbb R^n$. The **linear complementarity problem** LCP$(M,q)$ asks for vectors $x,s\in\mathbb R^n$ with
--
--   $$Mx+q=s,\qquad x^\top s=0,\qquad x,s\ge 0_n .$$
--
--   Such a pair is a *solution* (complementary feasible solution) of LCP$(M,q)$. The **linear feasible region** and the **positive feasible region** are
--
--   $$\mathcal F(M,q)=\{(x,s)\in\mathbb R^{2n}_{\ge 0}: s=Mx+q\},\qquad \mathcal F_{>0}(M,q)=\mathcal F(M,q)\cap\mathbb R^{2n}_{>0}.$$
--
--   These are the basic objects of every statement of the mission: interior point methods move inside $\mathcal F_{>0}$, and the LP oracle of Algorithm 3 searches $\mathcal F$.
--
--   **Formalization Note** The index set $[n]$ is a finite type with $n$ elements; a point of $\mathbb R^{2n}$ is a pair $(x,s)$ of vectors.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), display (LCP(M, q)), p.1; §2.1, p.6

import Mathlib

open Matrix

namespace NewtonLCP

/-!
# The linear complementarity problem LCP(M, q) and its feasible regions

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8),
§1, display (LCP(M, q)), p.1; §2.1 "Feasibility and centrality", p.6.

**Formalization Note.** The index set `[n]` is a finite type `ι` with `n = Fintype.card ι`;
vectors are functions `ι → ℝ` and matrices are `Matrix ι ι ℝ`. A point of `ℝ²ⁿ` is a pair
`(x, s)`.
-/

variable {ι : Type*} [Fintype ι]

/-- `IsLCPSol M q x s`: `(x, s)` solves LCP(M, q), i.e. `Mx + q = s`, `xᵀs = 0`, `x, s ≥ 0`
(p.1, display (LCP(M, q))). -/
def IsLCPSol (M : Matrix ι ι ℝ) (q x s : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ s i) ∧ s = M *ᵥ x + q ∧ x ⬝ᵥ s = 0

/-- The linear feasible region `F(M, q) = {(x, s) ∈ ℝ²ⁿ_{≥0} : s = Mx + q}` (p.6). -/
def Feas (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ p.2 i) ∧ p.2 = M *ᵥ p.1 + q}

/-- The positive feasible region `F_{>0}(M, q) = F(M, q) ∩ ℝ²ⁿ_{>0}` (p.6). -/
def FeasPos (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {p | (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i) ∧ p.2 = M *ᵥ p.1 + q}

end NewtonLCP


