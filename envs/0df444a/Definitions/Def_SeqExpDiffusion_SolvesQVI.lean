-- Prove2me | Definitions.Def_SeqExpDiffusion_SolvesQVI
-- name    : SeqExpDiffusion_SolvesQVI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:43.38357+00:00
-- url     : https://prove2.me/theorems/1a058578-d123-4200-bab2-efea263c0c6c
-- title:
--   Definition 3: the quasi-variational inequalities (15)
-- statement:
--   Let $H$ be a payoff. A function $f\in\widehat{\mathcal C}^2$, with exceptional set $N_f$, **satisfies the quasi-variational inequalities** for (12) if for all $\delta\in[0,1]\setminus N_f$
--
--   $$f(\delta)-H(\delta)\ge0,\qquad \mathcal Hf(\delta)\le0,\qquad \big(f(\delta)-H(\delta)\big)\,\mathcal Hf(\delta)=0.$$
--
--   These conditions split $[0,1]$ into a continuation region, where $f>H$ and $\mathcal Hf=0$, and an intervention region, where $f=H$ and $\mathcal Hf\le0$.
--
--   **Formalization Note** $\mathcal H$ is the corrected operator (14). The payoff $H$ is a parameter, so the definition covers both the payoff $G$ of (1) and the two-action payoffs $\tilde G_{ij}$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Definition 3 and display (15), p.18

import Mathlib
import Definitions.Def_SeqExpDiffusion_IsHatC2With
import Definitions.Def_SeqExpDiffusion_genH

namespace SeqExpDiffusion

/-- Definition 3 (QVI), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.18: `f ∈ Ĉ²` satisfies the quasi-variational inequalities for
(12) with payoff `H` if for all `δ ∈ [0, 1] \ N_f`
`f(δ) − H(δ) ≥ 0`, `ℋf(δ) ≤ 0`, `(f(δ) − H(δ)) ℋf(δ) = 0` (display (15)).

**Formalization Note** The exceptional set `N` is the one of `Ĉ²`, so `ℋf` is only evaluated where
`f″` exists. `ℋ` is the corrected operator (14) (`genH`). The payoff `H` is a parameter, so the
definition serves the payoff `G` of (1) and the two-action payoffs `G̃_ij` alike. -/
def SolvesQVI (r σ : ℝ) (H f : ℝ → ℝ) : Prop :=
  ∃ N : Set ℝ, IsHatC2With f N ∧ ∀ δ ∈ Set.Icc (0 : ℝ) 1 \ N,
    0 ≤ f δ - H δ ∧ genH r σ f δ ≤ 0 ∧ (f δ - H δ) * genH r σ f δ = 0

end SeqExpDiffusion


