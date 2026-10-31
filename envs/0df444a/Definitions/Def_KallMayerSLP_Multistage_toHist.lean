-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_toHist
-- name    : KallMayerSLP_Multistage_toHist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:42.287555+00:00
-- url     : https://prove2.me/theorems/6a97b6a7-5f28-49b0-a2fe-28ef61ec2ede
-- title:
--   Reading $\widehat\zeta_t$ off a family of realizations
-- statement:
--   From a full family of realizations $w=(w_s)_s$, this is the realization $\widehat\zeta_t=(w_2,\dots,w_t)$ of $\zeta_t$. The recursion (3.15) keeps the family whole and uses its coordinates $s\le t$ at stage $t$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, notation of the proof of Lemma 3.1, p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Hist

namespace KallMayerSLP.Multistage

/-- The realization `ζ̂_t = (ξ̂_2, …, ξ̂_t)` read off a full family of realizations `w`. The recursions
(3.15) keep `w` whole and only use its coordinates `s ≤ t` at stage `t`. -/
def toHist {r : ℕ → ℕ} (t : ℕ) (w : ∀ s, Fin (r s) → ℝ) : Hist r t := fun s => w s

end KallMayerSLP.Multistage


