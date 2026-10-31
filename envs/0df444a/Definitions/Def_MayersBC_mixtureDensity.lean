-- Prove2me | Definitions.Def_MayersBC_mixtureDensity
-- name    : MayersBC_mixtureDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:55.376817+00:00
-- url     : https://prove2.me/theorems/948a2547-a6b2-4c77-ac60-4d3d185641fe
-- title:
--   Density operator of a mixture $\sum_w p_w |\psi_w\rangle\langle\psi_w|$
-- statement:
--   A **mixture** is a random choice of pure states: the state $\psi_w$ is prepared with probability $p_w$, for $w$ in a finite set $W$. Its density operator is
--
--   $$
--   \rho = \sum_{w \in W} p_w\, |\psi_w\rangle\langle\psi_w| .
--   $$
--
--   The results of any measurement on the mixture depend only on $\rho$. In Mayers' paper the honest commitment to $b$ is the mixture $\{(|c\rangle_\theta, p(\theta, c\mid b))\}$, with density operator $\rho_b$.
--
--   **Formalization Note** $p$ is any real function and the $\psi_w$ any vectors; theorems assume that $p$ is a probability distribution and that each $\psi_w$ is a unit vector. The published `QAlgorithms.ensembleDensity` has the same formula but indexes the mixture by $\{0,\dots,m-1\}$; this version allows any finite index set, here the pairs $(\theta, c)$.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

/-- Mayers, *The Trouble with Quantum Bit Commitment*, arXiv:quant-ph/9603015v3, section b, p.4:
the density operator of a mixture `{(ψ_w, p_w)}` of pure states,
`ρ = Σ_w p_w |ψ_w⟩⟨ψ_w|` (the page's `ρ_b = Σ_{θ,c} p(θ, c|b) (|c⟩⟨c|)_θ` and
`Σ_ψ p(ψ)|ψ⟩⟨ψ|`).

**Formalization Note.** The mixture is indexed by a finite type `W`; `p` is any real function
and `ψ` any family of vectors, the theorems assume that `p` is a probability distribution and
each `ψ_w` a unit vector. `pureDensity ψ = |ψ⟩⟨ψ|` is the published `QAlgorithms.pureDensity`. -/
noncomputable def mixtureDensity {W ι : Type} [Fintype W] (p : W → ℝ)
    (ψ : W → EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  ∑ w, ((p w : ℝ) : ℂ) • pureDensity (ψ w)

end MayersBC


