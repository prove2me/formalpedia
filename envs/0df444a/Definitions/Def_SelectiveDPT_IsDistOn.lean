-- Prove2me | Definitions.Def_SelectiveDPT_IsDistOn
-- name    : SelectiveDPT_IsDistOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:53.166218+00:00
-- url     : https://prove2.me/theorems/2aa07582-50bf-4d36-9983-ffa7629beda1
-- title:
--   Probability distribution on a domain $D$ and its purification $|\mathcal D\rangle$
-- statement:
--   A function $\mu : X^\iota \to \mathbb R$ is a **probability distribution on the domain** $D$ if $\mu(x) \ge 0$ for all $x$, $\mu(x) = 0$ for $x \notin D$, and
--   $$\sum_{x \in D} \mu(x) = 1 .$$
--   Its **purification** is the vector $|\mathcal D\rangle = \sum_{x \in D} \sqrt{\mu(x)}\,|x\rangle \in \mathbb C^D$.
--
--   The hard input distributions of the adversary methods and the product distributions of the direct product theorems are distributions in this sense; the adversary matrices fix the purification $|\mathcal D\rangle$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.9 (ρ_D and |D⟩)

import Mathlib

namespace SelectiveDPT

/-- `μ` is a probability distribution supported on the domain `D` (arXiv:2609.26678, §2.2, p.9:
"some relation-dependent hard distribution `D` supported on some subset `D` of `X^n`"):
`μ ≥ 0`, `μ = 0` outside `D`, and `Σ_{x ∈ D} μ(x) = 1`. -/
def IsDistOn {α : Type*} (μ : α → ℝ) (D : Finset α) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∀ x, x ∉ D → μ x = 0) ∧ ∑ x ∈ D, μ x = 1

/-- The purification `|D⟩ = Σ_{x ∈ D} √(D(x)) |x⟩` of the input distribution (arXiv:2609.26678,
§2.2, p.9), as a vector indexed by the domain `D`. -/
noncomputable def sqrtDist {α : Type*} (μ : α → ℝ) (D : Finset α) : D → ℂ :=
  fun x => (Real.sqrt (μ x.1) : ℂ)

end SelectiveDPT


