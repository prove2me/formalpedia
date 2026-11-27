-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_muBar
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_muBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:19:50.191643+00:00
-- url     : https://prove2.me/theorems/19b993e9-b915-59cb-a531-08764eff8203
-- title:
--   The maximal appreciation rate $\bar{\mu} := \max {\mu _1, \dots , \mu _d, \rho }$
-- statement:
--   **The maximal appreciation rate $\bar{\mu} := \max {\mu _1, \dots , \mu _d, \rho }$** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.284, PDF 294).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.284, PDF 294

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket

namespace BauerleRiederMDP.LQ.Supplement

/-- **The maximal appreciation rate `μ̄ := max{μ_1, …, μ_d, ρ}`** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), p.284, PDF 294). -/
noncomputable def JumpMarket.muBar {d : ℕ} (Mk : JumpMarket d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k : Option (Fin d) => k.elim Mk.ρ Mk.μ)

end BauerleRiederMDP.LQ.Supplement


