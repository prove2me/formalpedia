-- Prove2me | Definitions.Def_GuhaBroadcast_charlieOutput
-- name    : GuhaBroadcast_charlieOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:36.93248+00:00
-- url     : https://prove2.me/theorems/ee7bd0d8-d398-41ee-bc77-8015883e05a1
-- title:
--   Charlie's received state $\hat\rho^{C^n}_{m,k}$
-- statement:
--   For the codeword $x^n(m,k)$ sent through $n$ uses of the beam splitter (6)–(7) with vacuum environment, **Charlie's received state** $\hat\rho^{C^n}_{m,k}=\operatorname{Tr}_{B^n}\hat\rho^{B^nC^n}_{m,k}$ is the partial trace of the joint output over Bob's modes.
--
--   **Formalization Note** The channel is the published `broadcast n eta` and the partial trace is `charlieMarginal`, from `QAlgorithms.Papers.Independent.Next46.P32`.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section II, p.1; Section III, eqs. (6)-(7), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section II, p.1, and Section III, Eqs. (6)–(7), p.2 (PDF pages; the paper prints no page
numbers): Charlie's received n-use state `ρ̂_{m,k}^{Cⁿ} = Tr_{Bⁿ} ρ̂_{m,k}^{BⁿCⁿ}` for the codeword
`x^n(m,k)` of the code `C`.

**Formalization Note.** The channel is the published `broadcast n eta` and the partial trace over Bob is
`charlieMarginal`, both from `QAlgorithms.Papers.Independent.Next46.P32`. -/
noncomputable def charlieOutput {n MB MC : ℕ} {O : Type} [Fintype O] (eta : ℝ)
    (C : BroadcastCode n MB MC O) (m : Fin MB) (k : Fin MC) : FockKernel n :=
  charlieMarginal (broadcast n eta (C.encoder m k).coefficients)

end GuhaBroadcast


