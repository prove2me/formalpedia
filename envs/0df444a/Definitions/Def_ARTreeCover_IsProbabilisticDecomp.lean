-- Prove2me | Definitions.Def_ARTreeCover_IsProbabilisticDecomp
-- name    : ARTreeCover_IsProbabilisticDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:54:15.103279+00:00
-- url     : https://prove2.me/theorems/729f7875-bb6e-478d-b1bb-9a6f32ecbce6
-- title:
--   Padded and probabilistic decompositions
-- statement:
--   Let $\Delta,\alpha>0$ and $0<p\le 1$. A distribution $D$ on partitions of $V$ whose partitions all have strong (weak) radius at most $\alpha\Delta$ is
--
--   1. a strong (weak) **$(\Delta,\alpha)$-probabilistic decomposition** with probability parameter $p$ if for all $u,v$ with $d_G(u,v)\le\Delta$,
--   $$\Pr_{\Pi\leftarrow D}[\exists C\in\Pi:\ u,v\in C]\ge p;$$
--   2. a strong (weak) **$(\Delta,\alpha)$-padded decomposition** with probability parameter $p$ if for every $u$,
--   $$\Pr_{\Pi\leftarrow D}[\exists C\in\Pi:\ B_G(u,\Delta)\subseteq C]\ge p.$$
--
--   Every padded decomposition is a probabilistic decomposition with the same parameters.
--
--   **Formalization Note** $D$ is a `PMF` on `Finpartition univ`; the radius bound holds for every partition in the support; the probability is the outer measure of the event, the sum of its point masses. The range of $p$ is stated in the theorems.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 10, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_RadiusLE

open scoped ENNReal

namespace ARTreeCover

/-!
# Padded and probabilistic decompositions

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 10, p.12 (PDF p.15).

**Formalization Note.** A distribution of partitions of `V` is a `PMF` on
`Finpartition (Finset.univ : Finset V)`. "With strong (resp., weak) radius at most α∆" is required
of every partition in the support. Probabilities are `D.toOuterMeasure` of the event; every set is
an event (a `PMF`'s outer measure is the sum of the point masses). The paper's range `0 < p ≤ 1` is
stated in the theorems, not here.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every cluster of every partition in the support of `D` has strong/weak radius at most `R`. -/
def DecompRadiusLE (G : WGraph V) (strong : Bool)
    (D : PMF (Finpartition (Finset.univ : Finset V))) (R : ℝ) : Prop :=
  ∀ P ∈ D.support, ∀ C ∈ P.parts, RadiusLE G strong C R

/-- A strong/weak `(∆, α)`-probabilistic decomposition with probability parameter `p`: radius at
most `α∆`, and `Pr_{Π←D}[∃ C ∈ Π, u, v ∈ C] ≥ p` for all `u, v` with `d_G(u, v) ≤ ∆`. -/
def IsProbabilisticDecomp (G : WGraph V) (strong : Bool) (Δ α p : ℝ)
    (D : PMF (Finpartition (Finset.univ : Finset V))) : Prop :=
  DecompRadiusLE G strong D (α * Δ) ∧
    ∀ u v, G.dist u v ≤ ENNReal.ofReal Δ →
      ENNReal.ofReal p ≤ D.toOuterMeasure {P | ∃ C ∈ P.parts, u ∈ C ∧ v ∈ C}

/-- A strong/weak `(∆, α)`-padded decomposition with probability parameter `p`: radius at most
`α∆`, and `Pr_{Π←D}[∃ C ∈ Π, B_G(u, ∆) ⊆ C] ≥ p` for every `u`. -/
def IsPaddedDecomp (G : WGraph V) (strong : Bool) (Δ α p : ℝ)
    (D : PMF (Finpartition (Finset.univ : Finset V))) : Prop :=
  DecompRadiusLE G strong D (α * Δ) ∧
    ∀ u, ENNReal.ofReal p ≤
      D.toOuterMeasure {P | ∃ C ∈ P.parts, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ → v ∈ C}

end ARTreeCover


