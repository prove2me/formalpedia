-- Prove2me | Definitions.Def_SBMThreshold_Main_Branching
-- name    : SBMThreshold_Main_Branching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:03.250361+00:00
-- url     : https://prove2.me/theorems/cdc61abb-7831-4464-921b-7c77f65b95d3
-- title:
--   §3.3.1, pp. 13–14 — the labelled Poisson(d) Galton–Watson tree (T, η⁺): generation counts, Ψ⁺_R, and P[Ψ⁺_R ≥ ξκs^R]
-- statement:
--   This file encodes the labelled branching process of §3.3.1 of Mossel, Neeman and Sly, through the quantities that Lemma 3.7 uses.
--
--   **The tree.** $T$ is a Galton–Watson tree rooted at $\rho$ with $\mathrm{Poisson}(d)$ offspring, $d=(a+b)/2$. The labelling $\eta^+$ fixes $\eta^+_\rho=+1$; then, recursively down the tree, every child $w$ of a vertex $u$ independently receives $\eta^+_w=\eta^+_u$ with probability $a/(a+b)$ and $\eta^+_w=-\eta^+_u$ otherwise. Write $S_R(\rho)$ for the vertices at depth $R$ and
--   $$
--   \Psi^+_R=\sum_{v\in S_R(\rho)}\eta^+_v .
--   $$
--
--   **Generation counts.** Let $Z^+_r$ and $Z^-_r$ be the numbers of vertices at depth $r$ labelled $+1$ and $-1$. Then $\Psi^+_R=Z^+_R-Z^-_R$. Thinning the $\mathrm{Poisson}(d)$ offspring of each vertex with probability $a/(2d)$ gives $\mathrm{Poisson}(a/2)$ children with the parent's label and, independently, $\mathrm{Poisson}(b/2)$ with the opposite label. Superposing the independent Poisson counts of all vertices of a generation, $(Z^+_r,Z^-_r)_{r\ge0}$ is a Markov chain on $\mathbb N^2$ started at $(1,0)$ whose step from $(x,y)$ draws independently
--   $$
--   Z^+\sim\mathrm{Poisson}\Bigl(\frac{xa+yb}{2}\Bigr),\qquad Z^-\sim\mathrm{Poisson}\Bigl(\frac{xb+ya}{2}\Bigr).
--   $$
--   The file defines this one-step law, its $R$-fold iterate (the law of $(Z^+_R,Z^-_R)$), the uniform distribution on $[-1,1]$, and, for $\kappa\in\mathbb R$,
--   $$
--   p_R(\kappa)=\mathbb P\bigl[\Psi^+_R\ge\xi\,\kappa\,s^R\bigr],
--   $$
--   where $s=(a-b)/2$ and $\xi$ is uniform on $[-1,1]$ and independent of the tree.
--
--   This is the object of Lemma 3.7, which compares the labelled neighbourhood of a vertex of $\mathcal G(n,a/n,b/n)$ with a branching process.
--
--   **Formalization Note** Only the law of $\Psi^+_R$ enters Lemma 3.7, so the tree is encoded by its generation counts rather than as a random labelled tree; the equality in law rests on independent Poisson thinning and superposition, as explained above. The step law is a product of two `poissonMeasure`s, iterated with `Measure.bind`; $p_R(\kappa)$ is the product measure of this law with the uniform law on $[-1,1]$, evaluated on the event. The Poisson means are passed through `Real.toNNReal`; they are nonnegative whenever $a,b\ge0$.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, pp. 13–14, §3.3.1 (the branching process T, the labellings η, η^±, Ψ_R, Ψ^±_R); p. 15 (Poisson(a/2) / Poisson(b/2) offspring of the same and the opposite label)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting

namespace SBMThreshold.Main

/-! Mossel, Neeman and Sly, arXiv:1311.4115v4, §3.3.1, pp. 13–14: the labelled Galton–Watson tree
`(T, η⁺)` with Poisson(`d`) offspring, root label `η⁺_ρ = +1`, and each child carrying its parent's
label with probability `a/(a+b)` and the opposite label otherwise.

Only the generation counts enter Lemma 3.7: `Ψ⁺_R = Σ_{v ∈ S_R(ρ)} η⁺_v = Z⁺_R - Z⁻_R`, where `Z^±_r`
is the number of vertices at depth `r` labelled `±1`. By independent thinning of the Poisson(`d`)
offspring (with probability `a/(2d)`) and superposition of independent Poisson variables,
`(Z⁺_r, Z⁻_r)` is a Markov chain on `ℕ × ℕ` started at `(1, 0)`, whose step from `(x, y)` draws
independently `Z⁺ ∼ Poisson((x a + y b)/2)` and `Z⁻ ∼ Poisson((x b + y a)/2)`. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- One generation of the two-type chain: from `x = (Z⁺, Z⁻)`, the next generation has
`Poisson((Z⁺ a + Z⁻ b)/2)` vertices labelled `+1` and, independently, `Poisson((Z⁺ b + Z⁻ a)/2)`
vertices labelled `-1`. -/
noncomputable def branchStep (a b : ℝ) (x : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (((x.1 : ℝ) * a + (x.2 : ℝ) * b) / 2))).prod
    (poissonMeasure (Real.toNNReal (((x.1 : ℝ) * b + (x.2 : ℝ) * a) / 2)))

/-- The law of `(Z⁺_R, Z⁻_R)` for the tree `(T, η⁺)`: the root generation is `(1, 0)` (root labelled
`+1`), and each further generation is drawn by `branchStep`. -/
noncomputable def branchGen (a b : ℝ) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (1, 0)
  | R + 1 => (branchGen a b R).bind (branchStep a b)

/-- `Ψ⁺_R = Z⁺_R - Z⁻_R`, the sum of the labels `η⁺_v` over generation `R`. -/
def psiOf (x : ℕ × ℕ) : ℝ := (x.1 : ℝ) - (x.2 : ℝ)

/-- The uniform distribution on `[-1, 1]`. -/
noncomputable def uniformPM1 : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- `P[Ψ⁺_R ≥ ξ κ s^R]` with `ξ` uniform on `[-1, 1]` and independent of the tree, `s = (a-b)/2`. -/
noncomputable def psiPlusProb (a b κ : ℝ) (R : ℕ) : ℝ :=
  (((branchGen a b R).prod uniformPM1)
    {p : (ℕ × ℕ) × ℝ | p.2 * κ * sPar a b ^ R ≤ psiOf p.1}).toReal

end SBMThreshold.Main


