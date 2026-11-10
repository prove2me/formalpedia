-- Prove2me | Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
-- name    : RandLatEnum_IsHaarLatticeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:36.458463+00:00
-- url     : https://prove2.me/theorems/c0869421-ca92-44ee-9fc8-b347070248e3
-- title:
--   The Haar probability measure $\mu_n$ on $X_n$
-- statement:
--   A measure $\mu$ on $X_n$ is the **Haar probability measure** $\mu_n$ if it is a probability measure on the Borel $\sigma$-algebra of $X_n$ and it is invariant under the action of $\mathrm{SL}_n(\mathbb R)$:
--   $$
--   \mu(g^{-1}S)=\mu(S)\qquad\text{for every } g\in\mathrm{SL}_n(\mathbb R)\text{ and every Borel set } S\subseteq X_n .
--   $$
--   A **Haar-random lattice** $L\sim\mu_n$ is the lattice of a $\mu_n$-random point of $X_n$.
--
--   All probabilistic statements of the mission are about this measure.
--
--   **Formalization Note** $X_n$ carries exactly one $\mathrm{SL}_n(\mathbb R)$-invariant Borel probability measure (Siegel), so the predicate characterizes $\mu_n$. Mathlib does not construct it, so theorems take $\mu_n$ as a hypothesis satisfying this predicate. No other regularity is assumed.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14

import Mathlib
import Definitions.Def_RandLatEnum_X

namespace RandLatEnum

open MeasureTheory

/-- `μ` is the Haar probability measure `µ_n` on `X_n` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14: "µn is its Haar
probability measure. When referring to a Haar-random lattice, we mean L ∼ µn"): a probability
measure on the Borel σ-algebra of `X_n` that is invariant under the left action of every
`g ∈ SL_n(ℝ)`.

**Formalization Note.** `X_n` carries exactly one `SL_n(ℝ)`-invariant Borel probability measure
(Siegel), so this predicate pins down `µ_n`; theorems take `µ_n` as a hypothesis because Mathlib
does not construct it. No further regularity is bundled. -/
def IsHaarLatticeMeasure {n : ℕ} (μ : Measure (X n)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (g : Matrix.SpecialLinearGroup (Fin n) ℝ) (s : Set (X n)), MeasurableSet s →
      μ ((fun x => g • x) ⁻¹' s) = μ s

end RandLatEnum


