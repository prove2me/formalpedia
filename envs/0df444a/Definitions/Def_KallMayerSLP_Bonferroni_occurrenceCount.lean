-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount
-- name    : KallMayerSLP_Bonferroni_occurrenceCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:01.047292+00:00
-- url     : https://prove2.me/theorems/0713e0e0-0a95-4dc6-8fa5-df0e52ba2f2c
-- title:
--   Number $\nu(\omega)$ of events which occur
-- statement:
--   For events $B_1,\dots,B_r$ and an outcome $\omega$, let $I(\omega)=\{i : \omega\in B_i\}$. The counting variable is
--   $$
--   \nu(\omega)=|I(\omega)|,
--   $$
--   so $\nu$ takes values in $\{0,1,\dots,r\}$, and $\{\nu\ge1\}$ is the union $B_1\cup\dots\cup B_r$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.285 (PDF 294)

import Mathlib

namespace KallMayerSLP.Bonferroni

open Classical in
/-- The counting variable `ν(ω) = |I(ω)|`, where `I(ω) = {i | ω ∈ B i}`: the number of events
out of `B 0, …, B (r-1)` which occur at `ω`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.285 (PDF 294). -/
noncomputable def occurrenceCount {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => ω ∈ B i).card

end KallMayerSLP.Bonferroni


