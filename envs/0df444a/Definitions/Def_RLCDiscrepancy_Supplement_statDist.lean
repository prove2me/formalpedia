-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_statDist
-- name    : RLCDiscrepancy_Supplement_statDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:48:36.90946+00:00
-- url     : https://prove2.me/theorems/de118469-6bbd-4c03-be69-444f452badc3
-- title:
--   Statistical distance $\mathrm{SD}(X,Y)$
-- statement:
--   For random variables $X,Y$ with values in a finite set $S$, driven by uniform coins on a finite coin space $\Omega$, the **statistical distance** is
--   $$
--   \mathrm{SD}(X,Y)=\frac12\sum_{s\in S}\big|\Pr[X=s]-\Pr[Y=s]\big|.
--   $$
--   We write $X\approx_\varepsilon Y$ when $\mathrm{SD}(X,Y)\le\varepsilon$; this measures the leakage error of Definition 6.4.
--
--   **Formalization Note** The probabilities are counting ratios over the uniform coin space (`PunctSketch.coinProb`); the right-hand expression of Definition 6.3 is used.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.3, p.45

import Mathlib
import Definitions.Def_PunctSketch_coinProb

namespace RLCDiscrepancy.Supplement

/-- **Statistical distance** (Definition 6.3). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.3, p.45:
"SD(X, Y) = max_{A⊆S} |Pr[X ∈ A] − Pr[Y ∈ A]| = ½ ∑_{s∈S} |Pr[X = s] − Pr[Y = s]|."

**Formalization Note.** X and Y are random variables `Ω → α` on a finite coin space `Ω` with
uniform coins (`PunctSketch.coinProb`), with values in a finite set `α`; the distance is the
right-hand expression ½ ∑_s |Pr[X = s] − Pr[Y = s]|. -/
noncomputable def statDist {Ω α : Type*} [Fintype Ω] [Fintype α] (X Y : Ω → α) : ℝ :=
  (1 / 2) * ∑ a : α, |PunctSketch.coinProb (fun ω => X ω = a) - PunctSketch.coinProb (fun ω => Y ω = a)|

end RLCDiscrepancy.Supplement


