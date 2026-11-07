-- Prove2me | Definitions.Def_SecondBestBT_IsPriorOn
-- name    : SecondBestBT_IsPriorOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:35.281192+00:00
-- url     : https://prove2.me/theorems/37e14286-76c5-48bc-bbb0-896975bf1c1a
-- title:
--   Prior supported on a type set $T$
-- statement:
--   A **prior on a type set** $T\subseteq\mathbb R$ is a Borel probability measure $\mu$ on $\mathbb R$ that puts no mass outside $T$:
--   $$
--   \mu \text{ is a probability measure and } \mu(\mathbb R\setminus T)=0 .
--   $$
--   The seller's value $s\sim F_S$ and the buyer's value $b\sim F_B$ are drawn from such priors; $\Delta(A)$ in the paper is the set of priors on $A$.
--
--   Priors are completely arbitrary: no density, no bounded or finite support, no regularity is assumed.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, pp.3–5

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- A prior on a type set `T ⊆ ℝ`: a probability measure on `ℝ` that gives no mass outside `T`
(Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version
sha256 17184930…, Section 2, p.3, and "∆(A) denotes the set of priors supported on A", p.5).

**Formalization Note** Priors are arbitrary Borel probability measures on `ℝ` (no density, no
finite support, no regularity); "supported on `T`" is read as `μ Tᶜ = 0`. -/
def IsPriorOn (T : Set ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Tᶜ = 0

end SecondBestBT


