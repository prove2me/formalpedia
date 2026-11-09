-- Prove2me | Definitions.Def_AgnosticTNS_LambdaP
-- name    : AgnosticTNS_LambdaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:22.202861+00:00
-- url     : https://prove2.me/theorems/d8ca1e4c-1aae-4f2f-a620-49c61838a9ea
-- title:
--   Number of retained eigenvectors $\Lambda_i$
-- statement:
--   At step $i$ of the agnostic sequence learner,
--   $$
--   \Lambda_i:=\left\lceil \frac{64\,r_i}{\alpha^2}\right\rceil,
--   $$
--   the number of leading eigenvectors retained when compression is needed.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, p.18

import Mathlib
import Definitions.Def_AgnosticTNS_rr
import Definitions.Def_AgnosticTNS_alphaP

namespace AgnosticTNS

/-- **The number of retained eigenvectors `Λ_i := ⌈64 r_i / α²⌉`**, §3.2, p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def LambdaP {n : ℕ} (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n)
    (ε ϑ : ℝ) (i : Fin Ls.L) : ℕ :=
  ⌈64 * (rr G χ Ls i : ℝ) / alphaP Ls ε ϑ ^ 2⌉₊

end AgnosticTNS


