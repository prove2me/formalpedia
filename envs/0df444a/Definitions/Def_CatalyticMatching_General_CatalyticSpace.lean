-- Prove2me | Definitions.Def_CatalyticMatching_General_CatalyticSpace
-- name    : CatalyticMatching_General_CatalyticSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:44.660222+00:00
-- url     : https://prove2.me/theorems/4f362147-dc0f-4c03-90f5-fe3c70dbdcc2
-- title:
--   Catalytic logspace and simultaneous polynomial-time search
-- statement:
--   For an explicit input domain $D$ and relation $R$, catalytic solvability means one fixed finite program restores every initial catalyst and outputs a valid witness on every $x\in D$. Its quantifiers are
--
--   $$\exists M,C,p\ \forall x\in D\ \forall\tau\in\{0,1\}^{p(|x|)}\ \exists t:\quad \operatorname{RestoredOutput}(M,R,C,x,\tau,t).$$
--
--   Here $C\ge1$, $p$ has nonnegative integer coefficients, and the work bound is $C(\lfloor\log_2(|x|+2)\rfloor+1)$. CL imposes halting without a time bound. CLP additionally chooses a uniform exponent $k$ and requires $t\le C(|x|+2)^k$ simultaneously. Restoration means equality of the entire catalyst at halt; every intermediate work head is bounded. Witnesses may depend on $\tau$. A single-valued relation enforces a function. The domain is a separate argument, so it is never inferred from the existence of the requested witness.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Definitions 2.1–2.3 p.10

import Definitions.Def_CatalyticMatching_General_Machine

namespace CatalyticMatching.General

/-- Positive integer logarithm convention, equivalent to ceil log₂(L+2)
up to an absolute factor absorbed into C. -/
def logBudget (L : ℕ) : ℕ := Nat.log 2 (L + 2) + 1

/-- Exact restored execution, including all intermediate workspace. -/
def RestoredOutput (M : Machine) (R : List Bool → List Bool → Prop)
    (C : ℕ) (x τ : List Bool) (t : ℕ) : Prop :=
  ∃ c, M.run x τ t = some c ∧ c.state = none ∧ c.catalyst = τ ∧
    R x c.output ∧ M.workBound x τ t (C * logBudget x.length)

/-- Definitions 2.1--2.3 p.10: universal halting on the relation's domain.
The polynomial has natural coefficients; no favorable initial tape is assumed. -/
def InCL (D : List Bool → Prop) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ (M : Machine) (C : ℕ) (p : Polynomial ℕ), 1 ≤ C ∧
    ∀ x, D x → ∀ τ, τ.length = p.eval x.length →
      ∃ t, RestoredOutput M R C x τ t

/-- One program and simultaneous uniform time, work, and catalyst bounds.
Search witnesses may depend on τ; a single-valued R enforces function output. -/
def InCLP (D : List Bool → Prop) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ (M : Machine) (C k : ℕ) (p : Polynomial ℕ), 1 ≤ C ∧
    ∀ x, D x → ∀ τ, τ.length = p.eval x.length →
      ∃ t, t ≤ C * (x.length + 2)^k ∧ RestoredOutput M R C x τ t

end CatalyticMatching.General


