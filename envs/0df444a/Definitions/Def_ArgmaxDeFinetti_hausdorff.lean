-- Prove2me | Definitions.Def_ArgmaxDeFinetti_hausdorff
-- name    : ArgmaxDeFinetti_hausdorff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:15.643443+00:00
-- url     : https://prove2.me/theorems/c99e7b90-a49b-4059-bc0a-3a595ae438ff
-- title:
--   Distance to a set and Hausdorff distance $D^\star_H(K,L)$
-- statement:
--   For a distance $D^\star$ between states, a state $\rho$ and sets $K,L$ of states,
--   $$
--   D^\star(\rho,K)=\inf_{\sigma\in K}D^\star(\rho,\sigma),\qquad
--   D^\star_H(K,L)=\max\Big\{\sup_{\rho\in K}D^\star(\rho,L),\ \sup_{\sigma\in L}D^\star(\sigma,K)\Big\}.
--   $$
--   Every de Finetti error of the paper has the form $D^\star_H(K,L)$ with the finite-extension set first and the separable set second.
--
--   **Formalization Note** Infima and suprema are real `sInf`/`sSup`; they are used for nonempty compact sets of states, on which the distances are bounded.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.2, p.20, eqs. (2.5)–(2.6)

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- The distance from a state to a set, `D^⋆(ρ, K) = inf_{σ ∈ K} D^⋆(ρ, σ)`, for a distance `δ`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.5), p.20.

**Formalization Note** The infimum is the real `sInf`; it is used only for nonempty sets, on which a
nonnegative distance is bounded below. -/
noncomputable def distSet {ι : Type} (δ : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ) (ρ : Matrix ι ι ℂ)
    (K : Set (Matrix ι ι ℂ)) : ℝ :=
  sInf (δ ρ '' K)

/-- The Hausdorff distance `D^⋆_H(K, L) = max { sup_{ρ∈K} D^⋆(ρ, L), sup_{σ∈L} D^⋆(σ, K) }`
for a distance `δ`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.6), p.20.

**Formalization Note** Suprema are real `sSup`s; the paper uses them for nonempty compact sets of states,
on which the distances are bounded. -/
noncomputable def hausdorff {ι : Type} (δ : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ)
    (K L : Set (Matrix ι ι ℂ)) : ℝ :=
  max (sSup ((fun ρ => distSet δ ρ L) '' K)) (sSup ((fun σ => distSet δ σ K) '' L))

end ArgmaxDeFinetti


