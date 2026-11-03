-- Prove2me | Definitions.Def_RiskAverseConsistency_IsNonatomic
-- name    : RiskAverseConsistency_IsNonatomic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:01.354259+00:00
-- url     : https://prove2.me/theorems/87ab3b39-b344-4cbc-bae0-77fc4c72e714
-- title:
--   Nonatomic (atomless) probability space
-- statement:
--   A measure $P$ on $(\Omega,\mathcal F)$ is **nonatomic** if every measurable set $A$ with $P(A)>0$ contains a measurable set $B\subseteq A$ with
--
--   $$
--   0<P(B)<P(A).
--   $$
--
--   On a nonatomic probability space there is a random variable $G:\Omega\to[0,1]$ with the uniform distribution, which is how the paper represents every law in $L^p$ as a quantile function evaluated at $G$.
--
--   **Formalization Note** This is the classical notion. Mathlib's `NoAtoms` (all singletons are null) is strictly weaker and is not used.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.3, §2.1 ("Let (Ω, F, P) be nonatomic")

import Mathlib

open MeasureTheory

namespace RiskAverseConsistency

/-- A measure `P` is **nonatomic** (atomless): every measurable set `A` with `P A > 0` contains a
measurable `B ⊆ A` with `0 < P B < P A`.

Milz, Surowiec, arXiv:2207.14756v2, §2.1, p.3 ("Let (Ω, F, P) be nonatomic"); the paper uses it
to obtain a uniform random variable via [21, Prop. A.7] (Dudley–Norvaiša, *Concrete Functional
Calculus*).

Formalization Note: this is the classical notion. Mathlib's `NoAtoms` (singletons are null) is
strictly weaker (the countable–cocountable probability on an uncountable set satisfies `NoAtoms`
and is atomic) and is not used. -/
def IsNonatomic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → 0 < P A →
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < P B ∧ P B < P A

end RiskAverseConsistency


