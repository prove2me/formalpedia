-- Prove2me | Definitions.Def_DistQuantumQuery_gammaBar
-- name    : DistQuantumQuery_gammaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:49.537255+00:00
-- url     : https://prove2.me/theorems/b7e21735-a719-4305-b0ee-da74b23e2573
-- title:
--   Filtered distributional $\gamma_2$ norm $\bar\gamma^\mu_2(B\mid\{Z_i\})$
-- statement:
--   Let $\Sigma$ be a finite set, $\mu$ a distribution on $\Sigma$, $B\in\mathbb C^{\Sigma\times\Sigma}$ and $\{Z_i\}_{i\in[n]}$ filters. The **filtered distributional $\gamma_2$ norm** is
--   $$
--   \bar\gamma^\mu_2(B\mid\{Z_i\}):=\max_{\Gamma\in L(\Sigma):\ \max_i\|\Gamma\circ Z_i\|\le1}\big|\langle\Gamma,B\circ|\mu\rangle\langle\mu|\rangle\big|,
--   $$
--   understood to be $+\infty$ if the optimization is unbounded. Here $\circ$ is the Hadamard product and $\|\cdot\|$ the operator norm. The module also fixes $\max_i\|\Gamma\circ Z_i\|$ for a finite family of filters.
--
--   With the query filters $\Delta_i$ this norm lower-bounds the cost of generating a Gram matrix and upper-bounds state conversion; it is the core of every adversary measure in the paper.
--
--   **Formalization Note** The value is in $[0,\infty]$, the supremum over complex $\Gamma$ (the set always contains $\Gamma=0$); it is $\infty$ exactly when the objective is unbounded. The paper assumes the filters non-zero; the definition is stated for any filters and coincides with the paper's on non-zero ones. The maximum over filters is a supremum over the finite index type (it is $0$ for an empty family, which is never used).
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 4.1 p.36; Lemma 4.5 p.39

import Mathlib
import Definitions.Def_DistQuantumQuery_traceNorm
import Definitions.Def_DistQuantumQuery_muMat

open scoped Matrix ENNReal

namespace DistQuantumQuery

/-- The largest filtered norm `max_i ‖Γ ∘ Z_i‖` over a finite family of filters
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, Definition 4.1, p.36; Lemma 4.5, p.39).

**Formalization Note** Written as `⨆ i` over the finite index type, which is the maximum when
the index type is nonempty (and `0` for an empty family, a case the paper never uses). -/
noncomputable def maxFilterNorm {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P]
    (Γ : Matrix X X ℂ) (Z : P → Matrix X X ℂ) : ℝ :=
  ⨆ i, opNorm (Γ ⊙ Z i)

/-- The **filtered distributional γ₂ norm** (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 4.1, p.36): for a distribution `μ` on a finite set `Σ`, a matrix `B ∈ ℂ^{Σ×Σ}` and
filters `{Z_i}_{i∈[n]}`,
`γ̄^μ₂(B | {Z_i}) := max { |⟨Γ, B ∘ |μ⟩⟨μ|⟩| : Γ ∈ L(Σ), max_i ‖Γ ∘ Z_i‖ ≤ 1 }`,
understood to be `+∞` if the optimization is unbounded.

**Formalization Note** The value is in `ℝ≥0∞`: the supremum over complex `Γ` with every
`‖Γ ∘ Z_i‖ ≤ 1` (operator norm), which is `⊤` exactly when the objective is unbounded. The set
of `Γ` always contains `0`. `∘` is the Hadamard product `⊙`, `⟨A, B⟩ = Tr[A†B]`. The paper
assumes the filters non-zero; the definition is stated for any filters and agrees with the
paper's on non-zero ones. -/
noncomputable def gammaBar {X P : Type*} [Fintype X] [DecidableEq X]
    (μ : X → ℝ) (B : Matrix X X ℂ) (Z : P → Matrix X X ℂ) : ℝ≥0∞ :=
  ⨆ (Γ : Matrix X X ℂ) (_ : ∀ i, opNorm (Γ ⊙ Z i) ≤ 1), ENNReal.ofReal ‖hsInner Γ (B ⊙ muMat μ)‖

end DistQuantumQuery


