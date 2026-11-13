-- Prove2me | Definitions.Def_GMRDiversity_genOnly
-- name    : GMRDiversity_genOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:59.311551+00:00
-- url     : https://prove2.me/theorems/d6ef8bd7-b261-4b80-8b10-65b51d57b0d2
-- title:
--   The generate-only policy
-- statement:
--   The **generate-only policy** queries a fresh $\mathrm{Gen}_x$ candidate in every round and keeps an empty pool. It is a live-pool policy for every pool size $w$, and it is the policy of the case $w\le 4$ in the proof of the upper bound.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, p.10

import Mathlib
import Definitions.Def_GMRDiversity_LivePoolPolicy

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **The generate-only policy** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
p.10: "If w ≤ 4, repeatedly generate fresh candidates"): every round is a generation and the pool is
always empty, so it is a live-pool policy for every `w`. -/
noncomputable def genOnly (n w : ℕ) : LivePoolPolicy n w where
  act _ _ := PMF.pure none
  keep _ _ _ _ _ := PMF.pure []
  keep_valid := by
    intro t P a z r P' hP'
    rw [PMF.support_pure, Set.mem_singleton_iff] at hP'
    subst hP'
    simp

end GMRDiversity


