-- Prove2me | Definitions.Def_OmniMix_FinDist_expectR
-- name    : OmniMix_FinDist_expectR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:55.677874+00:00
-- url     : https://prove2.me/theorems/d5110e0b-6688-426b-9644-4aeb118d36dd
-- title:
--   Expectation $\mathbb E_{P\sim D}[g(P)]$ (real)
-- statement:
--   For a finitely supported $D$ and $g:[0,1]\to\mathbb R$,
--   $$
--   \mathbb E_{P\sim D}[g(P)]=\sum_{p\in\operatorname{supp}D}D(p)\,g(p).
--   $$
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 and Lemma 2.2, p.10

import Mathlib
import Definitions.Def_OmniMix_FinDist

namespace OmniMix

/-- **Expectation `E_{P∼D}[g(P)]` of a real function.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1 and Lemma 2.2, p.10.

For a finitely supported `D`, `E_{P∼D}[g(P)] = Σ_{p ∈ supp D} D(p)·g(p)`. -/
noncomputable def FinDist.expectR (D : FinDist) (g : unitInterval → ℝ) : ℝ :=
  ∑ p ∈ D.wt.support, D.wt p * g p

end OmniMix


