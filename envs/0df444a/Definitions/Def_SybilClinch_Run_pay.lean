-- Prove2me | Definitions.Def_SybilClinch_Run_pay
-- name    : SybilClinch_Run_pay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:05.591951+00:00
-- url     : https://prove2.me/theorems/71b34eb6-ac78-4ba9-a458-532b342c4969
-- title:
--   Cumulative payment under current-price charging
-- statement:
--   Trade is charged at the current clock price. The cumulative payment of identity $i$ through clock price $p$ is the Stieltjes integral
--   $$y_i(p)=\int_{[p_\star,p]}s\,dx_i(s),$$
--   which covers continuous trade ($dy_i/dp=p\,dx_i/dp$) and fixed-price purchases ($\mathrm{Buy}(i,\delta;p)$ costs $p\delta$).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.3–§3.4, pp.10–11 (PDF pp.12–13); proof of Lemma 4.15, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SybilClinch_TargetMech
import Definitions.Def_SybilClinch_Run

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.3–§3.4, printed pp.10–11 (PDF pp.12–13), and the proof of Lemma 4.15, printed p.22
(PDF p.24): current-price charging. The cumulative payment of identity `i` through clock price `p`
is the Stieltjes integral `yᵢ(p) = ∫_{[p⋆, p]} s dxᵢ(s)`: continuous trade is charged at the clock
price (`dyᵢ/dp = p·dxᵢ/dp`, (18)) and a fixed-price purchase `Buy(i, δ; p)` costs `pδ`. -/
noncomputable def Run.pay (M : TargetMech) (R : Run) (i : ℕ) (p : ℝ) : ℝ :=
  ∫ s in Icc M.pstar p, s ∂(R.x i).measure

end SybilClinch


