-- Prove2me | Definitions.Def_MultiphaseDisj_Rectangle
-- name    : MultiphaseDisj_Rectangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:23.009122+00:00
-- url     : https://prove2.me/theorems/2ebf19e5-796f-41a5-a22c-515927866c9f
-- title:
--   Deficit, $d$-rectangles, $(d,\kappa)$-near-rectangles and $\delta$-monochromatic distributions
-- statement:
--   Let $\mathcal S$ be a finite family of sets and let $\mu$ be a distribution of a pair $(A,B)$ on $\mathcal S\times\mathcal S$ with marginals $\mu_A,\mu_B$.
--
--   1. The **deficit** of a distribution $\nu$ on $\mathcal S$ is $\log|\mathcal S|-H_\infty(\nu)$.
--   2. $\mu$ is a **$d$-rectangle** if $\mu=\mu_A\otimes\mu_B$ and both marginals have deficit at most $d$, that is $H_\infty(\mu_A)\ge\log|\mathcal S|-d$ and $H_\infty(\mu_B)\ge\log|\mathcal S|-d$.
--   3. $\mu$ is a **$(d,\kappa)$-near-rectangle** if both marginals have deficit at most $d$ and $I_\mu(A;B)\le\kappa$.
--   4. $\mu$ is **$\delta$-monochromatic** if $\Pr_\mu[A\cap B\neq\emptyset]\le\delta$, and **monochromatic** if it is $0$-monochromatic, i.e. supported on disjoint pairs.
--
--   A $d$-rectangle is the distributional analogue of a large combinatorial rectangle: for $A,B\subseteq\mathcal S$ the uniform distribution on $A\times B$ is a $d$-rectangle exactly when $|A|,|B|\ge2^{-d}|\mathcal S|$.
--
--   **Formalization Note** Sets are finite subsets of a finite type; logarithms, min-entropy and mutual information are in bits. Rectangles and near-rectangles are required to be distributions on $\mathcal S\times\mathcal S$.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Definitions 2.12 and 2.13, p.14

import Mathlib
import Definitions.Def_MultiphaseDisj_FiniteInfo

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiphaseDisj

variable {α : Type*} [Fintype α]

/-- **Deficit** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*,
arXiv:2610.10904, held version sha256 ba26649b…, Definition 2.12, p.14): for a finite family `S`
of sets and a distribution `ν` on `S`, the deficit is `log₂ |S| − H∞(ν)`. -/
def deficit (S : Finset (Finset α)) (ν : Finset α → ℝ) : ℝ :=
  Real.logb 2 S.card - minEntropy ν

/-- **d-rectangle** (Definition 2.13(a), p.14): a distribution `μ` on `S × S` with
`μ = μ_A ⊗ μ_B` whose two marginals have deficit at most `d`. -/
def IsRect (S : Finset (Finset α)) (d : ℝ) (μ : Finset α × Finset α → ℝ) : Prop :=
  IsDistOn (S ×ˢ S) μ ∧ μ = prodDist (marg1 μ) (marg2 μ) ∧
    deficit S (marg1 μ) ≤ d ∧ deficit S (marg2 μ) ≤ d

/-- **(d, κ)-near-rectangle** (Definition 2.13(b), p.14): a distribution `μ` of `(A, B)` on
`S × S` whose two marginals have deficit at most `d` and with `I_μ(A; B) ≤ κ`. -/
def IsNearRect (S : Finset (Finset α)) (d κ : ℝ) (μ : Finset α × Finset α → ℝ) : Prop :=
  IsDistOn (S ×ˢ S) μ ∧ deficit S (marg1 μ) ≤ d ∧ deficit S (marg2 μ) ≤ d ∧
    mutualInfo μ Prod.fst Prod.snd ≤ κ

/-- **δ-monochromatic** (Definition 2.13(c), p.14): `Pr_μ[A ∩ B ≠ ∅] ≤ δ`; *monochromatic* is
`0`-monochromatic, i.e. supported on disjoint pairs. -/
def IsMono (δ : ℝ) (μ : Finset α × Finset α → ℝ) : Prop :=
  pr μ (fun p => ¬ Disjoint p.1 p.2) ≤ δ

end MultiphaseDisj


