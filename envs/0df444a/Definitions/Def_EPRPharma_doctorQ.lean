-- Prove2me | Definitions.Def_EPRPharma_doctorQ
-- name    : EPRPharma_doctorQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:21.779214+00:00
-- url     : https://prove2.me/theorems/006d3e27-fac9-4eef-8f74-dd9e071e8875
-- title:
--   The doctor's prescription $q_p^*(p,\eta_d,\eta_p)$
-- statement:
--   The doctor chooses her prescription to maximize her utility over the quantities at least equal to the need:
--
--   $$q_p^*(p,\eta_d,\eta_p)=\arg\max_{\theta_n\le q_p\le 1}U_d(q_p).$$
--
--   Since $U_d$ is affine in $q_p$, the maximizer is unique unless the slope $\eta_d-p-o_d(1-\eta_p)$ vanishes, in which case every $q_p\in[\theta_n,1]$ is optimal; $q_p^*$ is then the largest maximizer, $q_p^*=1$, as Lemma 1 prescribes at this tie.
--
--   **Formalization Note** Defined as the supremum of the set of maximizers on $[\theta_n,1]$. For $\theta_n\in[0,1]$ the set is nonempty and bounded, so the supremum is a maximizer in $[\theta_n,1]$; the value for $\theta_n\notin[0,1]$ is never used. The closed form of Lemma 1 is a theorem of the mission, not part of the definition.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.1, p. 10 (unnumbered display); Lemma 1, p. 15, and its proof, Online Appendix p. 1

import Mathlib
import Definitions.Def_EPRPharma_Ud

namespace EPRPharma

/-- **The doctor's prescription q*_p(p, η_d, η_p).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.1, p. 10 (unnumbered display):
q*_p(p, η_d, η_p) = argmax_{q_p} U_d(q_p) such that θ_n ≤ q_p ≤ 1.
`doctorQ P d θn` is the largest maximizer of q ↦ U_d(q) over [θ_n, 1].

**Formalization Note.** U_d is affine in q_p, so its maximizer on [θ_n, 1] is unique except when
its slope η_d − p − o_d(1 − η_p) is zero, where every q_p ties; there the doctor prescribes the
largest quantity, which is what Lemma 1 and its proof (Online Appendix p. 1: "q*_p = 1 ≥ θ_n, i.e.,
the doctor over-prescribes, if η_d ≥ p + o_d(1 − η_p)") prescribe. For θ_n ∈ [0, 1] the set of
maximizers is nonempty and bounded, so the supremum is attained and lies in [θ_n, 1]; outside
[0, 1] the value is never used (all expectations integrate over θ_n ∈ [0, 1]). The case formula of
Lemma 1 is a theorem (`lemma_1_doctor_prescription`), not part of this definition. -/
noncomputable def doctorQ (P : Params) (d : Decision) (θn : ℝ) : ℝ :=
  sSup {q : ℝ | q ∈ Set.Icc θn 1 ∧ ∀ q' ∈ Set.Icc θn 1, Ud P d θn q' ≤ Ud P d θn q}

end EPRPharma


