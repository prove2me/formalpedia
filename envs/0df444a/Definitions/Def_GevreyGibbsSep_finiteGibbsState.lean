-- Prove2me | Definitions.Def_GevreyGibbsSep_finiteGibbsState
-- name    : GevreyGibbsSep_finiteGibbsState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:50.658353+00:00
-- url     : https://prove2.me/theorems/3e3640d6-5333-4893-91a7-7588b37185c9
-- title:
--   Normalized grid Gibbs state $|[e^{-\beta E/2}]\rangle$
-- statement:
--   For a potential $E$ on a finite grid $G$ and an inverse temperature $\beta$, the **normalized grid Gibbs state** is the unit vector
--   $$|\psi_\beta\rangle=\frac{[e^{-\beta E/2}]}{\big\|[e^{-\beta E/2}]\big\|},$$
--   the ket of the vector of values $e^{-\beta E(x)/2}$, $x\in G$. Its squared amplitudes form the grid Gibbs distribution; at $\beta=0$ it is the uniform superposition.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Appendix A 1, p.20; Lemma A.8, p.31

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The normalized grid Gibbs state `|[e^{−βE/2}]⟩ = [e^{−βE/2}]/‖[e^{−βE/2}]‖` of a potential `E`
on a finite grid `G` (arXiv:2608.24527 (sha256 d4fd40eb…), p.20: "the ket notation implies
normalization"; Lemma A.8, p.31; Theorem A.1, p.28). -/
noncomputable def finiteGibbsState {G : Type*} [Fintype G] (E : G → ℝ) (β : ℝ) :
    EuclideanSpace ℂ G :=
  let v : EuclideanSpace ℂ G := WithLp.toLp 2 (fun x => ((Real.exp (-(β * E x) / 2) : ℝ) : ℂ))
  ((‖v‖⁻¹ : ℝ) : ℂ) • v

end GevreyGibbsSep


