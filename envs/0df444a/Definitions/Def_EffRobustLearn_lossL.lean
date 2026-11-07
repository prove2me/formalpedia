-- Prove2me | Definitions.Def_EffRobustLearn_lossL
-- name    : EffRobustLearn_lossL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:16.942445+00:00
-- url     : https://prove2.me/theorems/dc618b24-4ae8-4d23-a6e2-216d44ea01d6
-- title:
--   The objective $L(\bar h)$ (3.1)
-- statement:
--   For $\bar h:X\to[-1,1]$,
--   $$L(\bar h)=\sup_{c\in C}\Big(\widehat{\mathrm{err}}_{S_{\mathrm{ref}}}(\bar h,c)-\sup_{\bar\mu\in\mathrm{conv}(C)}\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})\Big).$$
--
--   It measures how much the error of a hypothesis can exceed the corruption level certified for a candidate concept.
--
--   **Formalization Note** Both suprema are taken over exactly the set, as the real supremum of an image, and are not clipped at $0$. For nonempty samples and $C\ne\emptyset$ both images are nonempty and bounded.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (3.1), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_errD
import Definitions.Def_EffRobustLearn_certificate

namespace EffRobustLearn

/-- The objective (3.1), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.13:
`L(h̄) = sup_{c∈C} ( err̂_{Sref}(h̄, c) - sup_{μ̄∈conv(C)} η(c, μ̄; S̄inp, Sref) )`.

**Formalization Note.** `conv(C)` is `convexHull ℝ (toPM '' C)`, all finite convex combinations (§2). Both suprema are `sSup` of the image of exactly the
set, not `⨆ x ∈ S`, so they are not clipped at `0`. For `n, m ≥ 1`, `C ≠ ∅` and `[-1, 1]`-valued `h̄`, both images are nonempty and bounded, so these are genuine suprema. -/
noncomputable def lossL {X : Type*} {n m : ℕ} (C : Set (X → Bool)) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) (hbar : X → ℝ) : ℝ :=
  sSup ((fun c : X → Bool => errHat Sref hbar (toPM c) -
    sSup ((fun μ : X → ℝ => certificate (toPM c) μ Sinp Sref) '' convexHull ℝ (toPM '' C))) '' C)

end EffRobustLearn


