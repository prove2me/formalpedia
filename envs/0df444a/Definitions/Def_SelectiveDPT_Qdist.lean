-- Prove2me | Definitions.Def_SelectiveDPT_Qdist
-- name    : SelectiveDPT_Qdist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:01.63998+00:00
-- url     : https://prove2.me/theorems/63c685ba-b3db-44b4-91c6-32fc4e9937bc
-- title:
--   Distributional quantum query complexity $Q^{\mathcal D}_\varepsilon(R)$
-- statement:
--   For a relation $R \subseteq D \times Y$ and a distribution $\mu$ on $D$, the **distributional quantum query complexity** $Q^{\mathcal D}_\varepsilon(R)$ is the least $T$ such that some $T$-query algorithm (same model as for $Q_\varepsilon$) succeeds with probability at least $1-\varepsilon$ on average over $x \sim \mu$:
--   $$\sum_{x \in D} \mu(x)\,\Pr[\text{the output } y \text{ satisfies } (x,y) \in R] \;\ge\; 1-\varepsilon ,$$
--   and $\infty$ if there is none. The average equals the success probability $\|\Pi_{\mathrm{succ}}|\psi_T\rangle\|^2$ with the purified input $|\mathcal D\rangle$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.10 (Q^D_ε(R))

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel

namespace SelectiveDPT

open QAlgorithms

/-- The distributional quantum query complexity `Q^D_ε(R)` (arXiv:2609.26678, §2.2, p.10: "We use
`Q^D_ε(R)` to denote the quantum query complexity of computing `R` on an input `x ∼ D` with
probability at least `1 − ε`"): the least `T` such that some `T`-query algorithm with some
post-processing succeeds with probability at least `1 − ε` **on average** over `x ∼ μ`, i.e.
`Σ_{x ∈ D} μ(x)·Pr[(x, A(x)) ∈ R] ≥ 1 − ε`; `⊤` if there is none.

**Formalization Note.** The average equals the paper's `‖Π_succ |ψ_T⟩‖²` for the purified input
`|D⟩` (p.9–10). Same algorithm model as `Qrel`. -/
noncomputable def Qdist {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (μ : (ι → ZMod d) → ℝ) (R : (ι → ZMod d) → Y → Prop) (ε : ℝ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (b : ℕ) (A : QueryAlg ι (ZMod d) (Fin b) T)
      (out : (ι × ZMod d) × Fin b → Y), 1 - ε ≤ ∑ x ∈ D, μ x * successProb A out R x), (T : ℕ∞)

end SelectiveDPT


