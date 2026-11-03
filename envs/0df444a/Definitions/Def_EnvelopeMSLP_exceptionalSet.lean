-- Prove2me | Definitions.Def_EnvelopeMSLP_exceptionalSet
-- name    : EnvelopeMSLP_exceptionalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:50.408574+00:00
-- url     : https://prove2.me/theorems/8a6312af-1295-45df-ae8a-4ef86e7a19f9
-- title:
--   The exceptional set $Y$ of a polynomial family
-- statement:
--   For a finite family $\mathfrak P$ of polynomials in the data,
--   $$Y=\Theta\cap\bigcup_{p\in\mathfrak P}\partial\{\theta\in\Theta:p(d(\theta))=0\}.$$
--   Off $Y$, every $p\circ d$ with $p\in\mathfrak P$ vanishes identically near $\theta$ or nowhere near $\theta$. This set replaces the set of basis changes of the paper's proof of Theorem 2.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Theorem 2, p.10, as corrected

import Mathlib

namespace EnvelopeMSLP

/-- **The exceptional set `Y` of a finite polynomial family.** The `θ ∈ Θ` lying on the boundary of the
zero set in `Θ` of some `p ∘ d` with `p ∈ 𝔓`. It replaces the set `Y` of the proof of Theorem 2,
Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.10: off it, every `p ∘ d` with `p ∈ 𝔓` is identically zero or nowhere zero near `θ`. -/
def exceptionalSet {ι : Type*} (𝔓 : Finset (MvPolynomial ι ℝ)) (Θ : Set ℝ) (d : ℝ → ι → ℝ) :
    Set ℝ :=
  Θ ∩ ⋃ p ∈ 𝔓, frontier {θ | θ ∈ Θ ∧ MvPolynomial.eval (d θ) p = 0}

end EnvelopeMSLP


