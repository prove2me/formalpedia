-- Prove2me | Definitions.Def_GoldenRatioVI_Psi
-- name    : GoldenRatioVI_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:39.557001+00:00
-- url     : https://prove2.me/theorems/35114cd6-78cf-4c0f-9e6b-73b225ddc9d2
-- title:
--   The bifunction $\Psi(u,v)=\langle F(u),v-u\rangle+g(v)-g(u)$
-- statement:
--   For $g$ with finite values on its domain and $F:\mathcal E\to\mathcal E$, define for $u,v\in\operatorname{dom} g$
--   $$\Psi(u,v)=\langle F(u),\,v-u\rangle+g(v)-g(u).$$
--   Problem (1) is equivalent to the equilibrium problem: find $z^*$ with $\Psi(z^*,z)\ge0$ for all $z$; for fixed $u$ the function $\Psi(u,\cdot)$ is convex.
--
--   It is the gap-type quantity in the energy inequality (27) of the convergence proof.
--
--   **Formalization Note** Real-valued; it agrees with the paper's $\Psi$ at points of $\operatorname{dom} g$, which is where it is used.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §2.1, p. 6 (unnumbered definition of Ψ)

import Mathlib

namespace GoldenRatioVI

/-- **The bifunction `Ψ(u, v) = ⟨F(u), v − u⟩ + g(v) − g(u)`.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §2.1, p. 6:
"Define the bifunction Ψ(u, v) := ⟨F(u), v − u⟩ + g(v) − g(u). It is clear that (1) is equivalent
to the following equilibrium problem: find z∗ ∈ E such that Ψ(z∗, z) ≥ 0 ∀z ∈ E."

`Psi g F u v = ⟪F u, v − u⟫ + g v − g u`.

**Formalization Note.** Real-valued; it is used only at points `u, v` of `dom g`, where it agrees
with the paper's `Ψ`. -/
def Psi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → ℝ) (F : E → E) (u v : E) : ℝ :=
  inner ℝ (F u) (v - u) + g v - g u

end GoldenRatioVI


