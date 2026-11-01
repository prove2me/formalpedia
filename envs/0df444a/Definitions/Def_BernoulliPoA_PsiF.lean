-- Prove2me | Definitions.Def_BernoulliPoA_PsiF
-- name    : BernoulliPoA_PsiF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:50.809027+00:00
-- url     : https://prove2.me/theorems/2f08f770-4e88-48ee-8fe7-ae3ad68ce994
-- title:
--   The piece-wise affine function $\Psi_{\mathcal F}$
-- statement:
--   For a finite nonempty set $\mathcal F$ of triples,
--   $$
--   \Psi_{\mathcal F}(\omega)=\max_{(c,k,m)\in\mathcal F}\beta_{c,k,m}(\omega).
--   $$
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Theorem 3, Case 2, display (EC.7), p.ec4

import Mathlib
import Definitions.Def_BernoulliPoA_beta

namespace BernoulliPoA

/-- **The piece-wise affine function** `Ψ_F`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Theorem 3, Case 2, display (EC.7), p.ec4:
`Ψ_F(ω) = max_{(c,k,m) ∈ F} β_{c,k,m}(ω)` for a finite nonempty set `F` of triples. -/
noncomputable def PsiF (q : ℝ) (F : Finset ((ℕ → ℝ) × ℕ × ℕ)) (hF : F.Nonempty) (ω : ℝ) : ℝ :=
  F.sup' hF (fun t => beta q t ω)

end BernoulliPoA


