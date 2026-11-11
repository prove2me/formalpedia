-- Prove2me | Definitions.Def_GaussDiffSVP_intensity
-- name    : GaussDiffSVP_intensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:46.075305+00:00
-- url     : https://prove2.me/theorems/6ced9984-ad11-41ad-8a7d-b085503e2fef
-- title:
--   Intensity $m_\Xi = \mathbb E[\Xi]$ of a random record list
-- statement:
--   A **record list** is a finite list of values; its records are the list positions, so records are distinct even when their values coincide. For a random record list with law $\mu$ and counting measure $\Xi = \sum_i \delta_{X_i}$, the **intensity** is
--   $$m_\Xi(x) = \mathbb E\,\Xi(\{x\}),$$
--   the expected number of records with value $x$, counted with multiplicity.
--
--   **Formalization Note** The law is a `PMF` on lists, the count is the cardinality of the set of positions holding $x$, and the expectation is a sum in $[0,\infty]$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (4), §3.2, p.18

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The intensity `m_Ξ = E[Ξ]` of a random record list (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.2, (4), p.18): the expected
number of records with value `x`, counted with multiplicity.

**Formalization Note.** A record list is a `List α`; its records are the list positions, so record
IDs are distinct while values may repeat ("IDs remain distinct even when their values coincide",
p.18). A random record list is a law `μ : PMF (List α)`. The count is `Set.encard` of the set of
positions holding `x`, and the expectation is a sum in `ℝ≥0∞`. -/
noncomputable def intensity {α : Type*} (μ : PMF (List α)) (x : α) : ℝ≥0∞ :=
  ∑' l : List α, μ l * (({i : Fin l.length | l.get i = x}.encard : ℕ∞) : ℝ≥0∞)

end GaussDiffSVP


