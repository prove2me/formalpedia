-- Prove2me | Definitions.Def_OmniMix_FinDist_expect
-- name    : OmniMix_FinDist_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:57.311685+00:00
-- url     : https://prove2.me/theorems/40015289-92bb-40a7-926c-e4590c0726ef
-- title:
--   Expectation $\mathbb E_{P\sim D}[g(P)]$ (extended real)
-- statement:
--   For a finitely supported $D$ and $g:[0,1]\to\mathbb R\cup\{\pm\infty\}$,
--   $$
--   \mathbb E_{P\sim D}[g(P)]=\sum_{p\in\operatorname{supp}D}D(p)\,g(p).
--   $$
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib
import Definitions.Def_OmniMix_FinDist

namespace OmniMix

/-- **Expectation `E_{P∼D}[g(P)]` of an extended-real function.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1.

For a finitely supported `D`, `E_{P∼D}[g(P)] = Σ_{p ∈ supp D} D(p)·g(p)`, computed in `EReal`. -/
noncomputable def FinDist.expect (D : FinDist) (g : unitInterval → EReal) : EReal :=
  ∑ p ∈ D.wt.support, ((D.wt p : ℝ) : EReal) * g p

end OmniMix


