-- Prove2me | Definitions.Def_MetricMinTest_IsPseudometric
-- name    : MetricMinTest_IsPseudometric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:37.78221+00:00
-- url     : https://prove2.me/theorems/dca7e8c3-0d29-4b0d-8ded-84dc45805643
-- title:
--   Pseudometric $d$ on the index set
-- statement:
--   A function $d$ on pairs of indices is a **pseudometric** if $d(i,i)=0$, $d(i,j)=d(j,i)$ and $d(i,l)\le d(i,j)+d(j,l)$ for all indices. Nonnegativity follows. Distinct indices may be at distance $0$; the paper notes that such indices have equal means but need not have equal laws.
--
--   The pseudometric is the known side information of the testing problem: it bounds how far apart the unknown means can be.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §1, p.1 and §2, p.6

import Mathlib

namespace MetricMinTest

/-- **Pseudometric on the index set.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints: Shared Information, Certificates, and Adaptivity*, STOC 2027 submission
(manuscript sha256 dcece193…ad32bb), §1 p.1 and §2 p.6: "a supplied metric or pseudometric d".

**Formalization Note.** `d i i = 0`, symmetry and the triangle inequality; nonnegativity
follows. Distinct indices may be at distance zero ("Distance-zero indices have equal means but
need not have equal laws", p.6). -/
def IsPseudometric {ι : Type} (d : ι → ι → ℝ) : Prop :=
  (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧ (∀ i j l, d i l ≤ d i j + d j l)

end MetricMinTest


