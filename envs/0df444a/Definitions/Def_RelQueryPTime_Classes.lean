-- Prove2me | Definitions.Def_RelQueryPTime_Classes
-- name    : RelQueryPTime_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:11.534606+00:00
-- url     : https://prove2.me/theorems/761f6d7f-7d38-4827-80f6-186501ae4684
-- title:
--   $\mathrm{Q}(\le)\mathrm{PTIME}$, $\mathrm{FP}(\le)$, $\Sigma_\omega(\le)$ and its positive form
-- statement:
--   For a scheme $\sigma$ and an arity $r$:
--
--   1. $\mathrm{Q}(\le)\mathrm{PTIME}$ is the set of $r$-ary queries $Q$ on ordered databases with $\mathrm{Graph}(Q) \in \mathrm{P}$, for Cook's one-tape Turing machines (a machine running in time $|w|^k + k$).
--   2. $\mathrm{FP}(\le)$ is the set of queries defined by well-formed formulas of relational calculus with $\le$ and LFP whose free variables are among $x_0,\dots,x_{r-1}$. LFP may occur anywhere, nested and with parameters.
--   3. $\Sigma_\omega(\le)$ is the set of queries $\bar c \mapsto B \models \mathrm{LFP}(\varphi)(\bar v)$, where $\varphi \in \Sigma_\alpha$ for some finite $\alpha$ is first order, has free variables among its head variables, is monotone in the relation variable, and $\bar v$ is a tuple of the query variables:
--   $$
--   \Sigma_\omega = \{\psi(\bar v) \mid \psi = \mathrm{LFP}(\varphi),\ \varphi \text{ monotone},\ \varphi \in \Sigma_\alpha,\ \alpha < \omega\}.
--   $$
--   4. The positive form of $\Sigma_\omega(\le)$ is the same with "monotone" replaced by "the relation variable occurs only positively in $\varphi$".
--   5. $\mathrm{liftBool}(Q)$ reads a Boolean query ($r = 0$) as a unary query with one dummy free variable.
--
--   These are the classes compared in Theorem 1.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, §2 p.148 (Σβ for β a limit ordinal), §2 p.149 (QPTIME ≡ {φ | Graph(φ) ∈ P}; Q(≤)PTIME; FP(≤)), p.147 (Theorem 1 in words) (PDF pp.1–3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding

namespace RelQueryPTime

/-- `Q(≤)PTIME`, the `r`-ary queries on ordered databases computable in polynomial time
(Immerman, STOC 1982, §2, p.149): `QPTIME ≡ {φ | Graph(φ) ∈ P}`, with `P` the class of Cook's
one-tape Turing machines (`CookPvsNP.P`). -/
def QPTIME (σ : Schema) (r : ℕ) : Set (Query σ r) := {Q | Graph Q ∈ CookPvsNP.P Bool}

/-- `FP(≤)`, the queries expressible in relational calculus with `≤` plus the least fixpoint
operator (Immerman, STOC 1982, p.147 Theorem 1, and §2, p.149): queries `c ↦ B ⊨ φ(c)` of
well-formed formulas whose free variables are among `0, …, r-1`.

**Formalization Note** `LFP` may occur anywhere, nested and with parameters; every `LFP` body
must be monotone (`Formula.Wf`). -/
def FP (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ φ : Formula σ, φ.Wf ∧ φ.fv ⊆ {i | i < r} ∧ Q = φ.query r}

/-- `Σ_ω(≤)` (Immerman, STOC 1982, §2, p.148):
`Σ_ω = {ψ(v) | ψ = LFP(φ), φ monotone, φ ∈ Σ_α, α < ω}`, a substitution of variables `v` into
the least fixpoint of a first-order `φ ∈ Σ_α` whose free variables are its head variables.
"Monotone" is read semantically (`MonotoneIn`, on every database). -/
def SigmaOmega (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ (a α : ℕ) (φ : Formula σ) (ν : Fin a → Fin r),
      IsSigma α φ ∧ φ.fv ⊆ {i | i < a} ∧ MonotoneIn 0 a φ ∧ Q = (lfpAtom φ ν).query r}

/-- `Σ_ω(≤)` with "monotone" read syntactically: the relation variable occurs only positively in
`φ` (Immerman, STOC 1982, §2, p.148). -/
def SigmaOmegaPos (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ (a α : ℕ) (φ : Formula σ) (ν : Fin a → Fin r),
      IsSigma α φ ∧ φ.fv ⊆ {i | i < a} ∧ φ.Polar 0 a true ∧ Q = (lfpAtom φ ν).query r}

/-- The Boolean query `Q` read as a unary query with one dummy free variable. -/
def liftBool {σ : Schema} (Q : Query σ 0) : Query σ 1 := fun n B _ => Q n B Fin.elim0

end RelQueryPTime


