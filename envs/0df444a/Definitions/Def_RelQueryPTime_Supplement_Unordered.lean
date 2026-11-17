-- Prove2me | Definitions.Def_RelQueryPTime_Supplement_Unordered
-- name    : RelQueryPTime_Supplement_Unordered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:44:09.274566+00:00
-- url     : https://prove2.me/theorems/dc1ff9c3-58e9-4280-9ae6-a3f78993d59a
-- title:
--   $\le$-free formulas and the classes $\mathrm{FP}$, $\Sigma_\omega$, $\Sigma_\omega^{+}$ without an ordering
-- statement:
--   This module fixes the setting of Theorem 2, the case of databases without an ordering.
--
--   1. A formula of relational calculus with the least fixpoint operator is **$\le$-free** if no atom $x \le y$ occurs in it, also not inside the body of a (possibly nested) $\mathrm{LFP}$.
--   2. $\mathrm{FP}$ (without ordering) is the class of $r$-ary queries $\bar c \mapsto B \models \varphi(\bar c)$ defined by a well-formed $\le$-free formula $\varphi$ whose free variables are among $x_0,\dots,x_{r-1}$; $\mathrm{LFP}$ may occur anywhere in $\varphi$, nested and with parameters, each body monotone in its relation variable.
--   3. $\Sigma_\omega$ (without ordering) is
--   $$
--   \Sigma_\omega = \{\psi(\bar v) \mid \psi = \mathrm{LFP}(\varphi),\ \varphi \text{ monotone},\ \varphi \in \Sigma_\alpha,\ \alpha < \omega\},
--   $$
--   with $\varphi$ a $\le$-free first-order $\Sigma_\alpha$ formula whose free variables are its head variables $x_0,\dots,x_{a-1}$, monotone in its relation variable on every database, and $\bar v$ a tuple of query variables (repetitions allowed).
--   4. $\Sigma_\omega^{+}$ is the same class with "monotone" replaced by "the relation variable occurs only positively in $\varphi$".
--
--   These are the classes $\mathrm{FP}(\le)$, $\Sigma_\omega(\le)$, $\Sigma_\omega^{+}(\le)$ of the published module RelQueryPTime.Classes with the single additional requirement that the defining formula be $\le$-free. The module also records the three trivial inclusions into those classes.
--
--   **Formalization Note** The base language has $\le$ built in, interpreted as the natural order of the domain $\{0,\dots,n-1\}$. Forbidding the atom models "no ordering": a $\le$-free formula cannot see the order of the domain, and every finite database is isomorphic to one on $\{0,\dots,n-1\}$, so no instance is lost.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187; Σω and FP, §2, p.148; "If we do not have an ordering", §3, p.149 (statement of Theorem 2)

import Mathlib
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Classes

namespace RelQueryPTime.Supplement

open RelQueryPTime

/-- `φ` is `≤`-free: no atom `x ≤ y` occurs in `φ`, also not inside the body of an `LFP`
(Immerman, STOC 1982, §3, p.149: "If we do not have an ordering …", the setting of Theorem 2).

**Formalization Note** The base language `RelQueryPTime.Formula` has the order `≤` built in as
the atom `Formula.le`; a database "without an ordering" is modelled by forbidding that atom. The
databases stay on `Fin n`: a `≤`-free formula cannot see the order of `Fin n`, and every finite
database is isomorphic to one on `Fin n`. -/
def Formula.NoLe {σ : Schema} : Formula σ → Prop
  | .le _ _ => False
  | .neg φ | .ex _ φ | .all _ φ => Formula.NoLe φ
  | .and φ ψ | .or φ ψ => Formula.NoLe φ ∧ Formula.NoLe ψ
  | .lfp _ _ _ body _ => Formula.NoLe body
  | _ => True

/-- `FP` without an ordering (Immerman, STOC 1982, p.148 and §3, p.149, Theorem 2): the queries
`c ↦ B ⊨ φ(c)` of well-formed `≤`-free formulas of relational calculus with the least fixpoint
operator, with free variables among `0, …, r-1`.

**Formalization Note** The base class `RelQueryPTime.FP` with the one extra conjunct
`φ.NoLe`; `LFP` may occur anywhere, nested and with parameters. -/
def FPu (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ φ : Formula σ, φ.Wf ∧ Formula.NoLe φ ∧ φ.fv ⊆ {i | i < r} ∧ Q = φ.query r}

/-- `Σ_ω` without an ordering (Immerman, STOC 1982, §2, p.148:
`Σ_ω = {ψ(v) | ψ = LFP(φ), φ monotone, φ ∈ Σ_α, α < ω}`; §3, p.149, Theorem 2): the base class
`RelQueryPTime.SigmaOmega` with the extra conjunct that `φ` is `≤`-free. "Monotone" is read
semantically (`MonotoneIn`, on every database). -/
def SigmaOmegaU (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ (a α : ℕ) (φ : Formula σ) (ν : Fin a → Fin r),
      IsSigma α φ ∧ Formula.NoLe φ ∧ φ.fv ⊆ {i | i < a} ∧ MonotoneIn 0 a φ ∧
      Q = (lfpAtom φ ν).query r}

/-- `Σ_ω` without an ordering, "monotone" read syntactically: the relation variable occurs only
positively in the `≤`-free `φ` (Immerman, STOC 1982, §2, p.148; §3, p.149, Theorem 2). The base
class `RelQueryPTime.SigmaOmegaPos` with the extra conjunct `φ.NoLe`. -/
def SigmaOmegaPosU (σ : Schema) (r : ℕ) : Set (Query σ r) :=
  {Q | ∃ (a α : ℕ) (φ : Formula σ) (ν : Fin a → Fin r),
      IsSigma α φ ∧ Formula.NoLe φ ∧ φ.fv ⊆ {i | i < a} ∧ φ.Polar 0 a true ∧
      Q = (lfpAtom φ ν).query r}

/-- The `≤`-free classes are subclasses of the base classes. -/
theorem FPu_subset (σ : Schema) (r : ℕ) : FPu σ r ⊆ FP σ r := by
  rintro Q ⟨φ, h1, -, h3, h4⟩
  exact ⟨φ, h1, h3, h4⟩

theorem SigmaOmegaU_subset (σ : Schema) (r : ℕ) : SigmaOmegaU σ r ⊆ SigmaOmega σ r := by
  rintro Q ⟨a, α, φ, ν, h1, -, h3, h4, h5⟩
  exact ⟨a, α, φ, ν, h1, h3, h4, h5⟩

theorem SigmaOmegaPosU_subset (σ : Schema) (r : ℕ) : SigmaOmegaPosU σ r ⊆ SigmaOmegaPos σ r := by
  rintro Q ⟨a, α, φ, ν, h1, -, h3, h4, h5⟩
  exact ⟨a, α, φ, ν, h1, h3, h4, h5⟩

end RelQueryPTime.Supplement


