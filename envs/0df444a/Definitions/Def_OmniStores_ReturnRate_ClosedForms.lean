-- Prove2me | Definitions.Def_OmniStores_ReturnRate_ClosedForms
-- name    : OmniStores_ReturnRate_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:19.929874+00:00
-- url     : https://prove2.me/theorems/44ea9a70-4c1b-4f7c-9196-7c516d61589e
-- title:
--   Lemma 1 and Proposition 1 — positive-store turning point, assortment criteria, gap, and store size
-- statement:
--   For a return rate $\gamma\in(0,1)$, the positive-store turning point is
--
--   $$n^*(\gamma)=\frac{t}{2(\gamma h_r+h_o)}.$$
--
--   The file defines each product's incremental profit $c_i(\gamma)$ at that turning point exactly as displayed in the proof of Lemma 1; the strict-criterion assortment $I_s^*(\gamma)=\{i:c_i(\gamma)>0\}$; the alternative, positively rescaled criterion printed in Lemma 1; the positive-store profit gap $\sum_i[c_i(\gamma)]^+-n^*(\gamma)\xi\Omega_0$; and the store-size expression printed in the proof of Proposition 1. These quantities provide reusable names for the paper's closed-form calculations.
--
--   **Formalization Note.** The two assortment criteria are kept separately so their equivalence under the standing assumptions remains part of the theorem work. They do not replace the optimization relation in the main goal.
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), p. 11, Lemma 1; Online Appendix pp. 1–2 (PDF pp. 34–35), proofs of Lemma 1 and Proposition 1

import Definitions.Def_OmniStores_ReturnRate_Model

namespace OmniStores.ReturnRate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive-store turning point `t/(2(γ h_r + h_o))`, Lemma 1, p. 11. -/
noncomputable def nStar (P : Params ι) (γ : ℝ) : ℝ :=
  P.t / (2 * (γ * P.hr + P.ho))

/-- A product's incremental profit at `nStar`, in the form printed in the proof of
Lemma 1, Online Appendix p. 1. -/
noncomputable def crit (P : Params ι) (γ : ℝ) (i : ι) : ℝ :=
  P.k i * γ * P.θ * P.D i - nStar P γ * P.ξ * P.α i -
    P.ξ * (1 - γ) * P.β i * P.θ * P.D i -
    P.ξ * P.β i * (P.ho / (γ * P.hr + P.ho)) * (1 - P.θ) * P.D i

/-- The strictly profitable store assortment in the proof of Lemma 1. -/
noncomputable def IStar (P : Params ι) (γ : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < crit P γ i)

/-- The assortment criterion as printed in Lemma 1, p. 11, before division by
the positive factor `2(γ h_r + h_o)/t`. -/
noncomputable def IStarPrinted (P : Params ι) (γ : ℝ) : Finset ι :=
  Finset.univ.filter (fun i =>
    P.ξ * (P.α i + P.β i *
      ((2 * P.ho / P.t) * (1 - P.θ) * P.D i +
       (1 - γ) * (2 * (γ * P.hr + P.ho) / P.t) * P.θ * P.D i)) <
    P.k i * γ * (2 * (γ * P.hr + P.ho) / P.t) * P.θ * P.D i)

/-- The best positive-store profit less online-only profit, in Online Appendix p. 1. -/
noncomputable def gap (P : Params ι) (γ : ℝ) : ℝ :=
  Finset.univ.sum (fun i => max (crit P γ i) 0) - nStar P γ * P.ξ * P.Ω0

/-- The positive-store size formula of the proof of Proposition 1, Online Appendix
p. 2, using the strict-criterion assortment. -/
noncomputable def OmegaStar (P : Params ι) (γ : ℝ) : ℝ :=
  (IStar P γ).sum (fun i =>
    P.α i + P.β i * (1 - γ) * (2 * (γ * P.hr + P.ho) / P.t) * P.θ * P.D i +
      P.β i * (2 * P.ho / P.t) * (1 - P.θ) * P.D i) + P.Ω0

end OmniStores.ReturnRate


