-- Prove2me | Definitions.Def_BilatMatch_bilateral
-- name    : BilatMatch_bilateral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:58.496209+00:00
-- url     : https://prove2.me/theorems/8f3fa724-b14d-4e77-81d9-f54fcefd5ef3
-- title:
--   Bilateral trade and finitely supported priors
-- statement:
--   **Bilateral trade** with buyer prior $F_B$ and seller prior $F_S$ is the matching market with one buyer, one seller, one compatible edge $e$ and feasible family $\{\emptyset,\{e\}\}$.
--
--   A prior on $\mathbb R$ is **finite** (finitely supported) if it is a probability measure giving full mass to a finite set. The **atoms** of a measure are the points of positive mass.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), p.1 (pdf p.3), p.5 (pdf p.7), p.6 (pdf p.8)

import Mathlib
import Definitions.Def_BilatMatch_Market

open MeasureTheory

namespace BilatMatch

/-- The atoms of a measure on `ℝ`: the points of positive mass. -/
def atoms (μ : Measure ℝ) : Set ℝ := {x | 0 < μ {x}}

/-- A finitely supported prior ("finite prior", Liu, Qin, Wang, arXiv:2609.30702, held version,
sha256 ff1490ad…, p.1 and p.6): a probability measure on `ℝ` giving full mass to a finite set. -/
def IsFiniteSupport (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ s : Finset ℝ, μ (↑s)ᶜ = 0

/-- Bilateral trade with buyer prior `FB` and seller prior `FS` (p.5): one buyer, one seller, one
compatible edge, and the feasible family `{∅, {e}}`. -/
def bilateral (FB FS : Measure ℝ) : Market Unit Unit where
  edges := {((), ())}
  family := {∅, {((), ())}}
  buyerLaw := fun _ => FB
  sellerLaw := fun _ => FS

end BilatMatch


