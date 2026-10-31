-- Prove2me | Definitions.Def_SeqExpDiffusion_pairMax
-- name    : SeqExpDiffusion_pairMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:01.981921+00:00
-- url     : https://prove2.me/theorems/e0448ba9-a629-45ec-a331-ee6e10530fa3
-- title:
--   The maximum $\tilde V=\max_{\{a_i,a_j\}}\tilde{\mathcal G}_{ij}$ over pairs of actions
-- statement:
--   For a finite action set and a family of functions $\tilde{\mathcal G}_{ij}$ indexed by pairs of distinct actions,
--
--   $$\tilde V(\delta):=\max_{\{a_i,a_j\}\subseteq\mathscr A}\tilde{\mathcal G}_{ij}(\delta).$$
--
--   Theorem 2 shows that, with $\tilde{\mathcal G}_{ij}$ the two-action values, $\tilde V$ is the value of the full problem.
--
--   **Formalization Note** Pairs are ordered pairs $i\ne j$; the two orders of a pair carry the same two-action problem. The maximum is defined when there are at least two actions, which every statement of the mission assumes.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, §4.3.3, p.21

import Mathlib

namespace SeqExpDiffusion

/-- `Ṽ(δ) = max_{{a_i, a_j} ∈ 𝒜} 𝒢̃_ij(δ)`, the pointwise maximum over pairs of distinct actions,
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, §4.3.3, p.21.

**Formalization Note** The family `v i j` is indexed by ordered pairs `i ≠ j` (`Finset.offDiag`); the
two orders of a pair carry the same two-action problem. The maximum is `Finset.sup'`, defined when
`ι` has two distinct elements; otherwise the value is `0`, a case that never arises in this
mission, which always assumes `Nontrivial ι`. -/
noncomputable def pairMax {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ι → ℝ → ℝ)
    (δ : ℝ) : ℝ :=
  if h : (Finset.univ.offDiag : Finset (ι × ι)).Nonempty then
    Finset.univ.offDiag.sup' h (fun p => v p.1 p.2 δ)
  else 0

end SeqExpDiffusion


