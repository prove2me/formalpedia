-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Consistent
-- name    : SmoothedPlanted_FFK_Consistent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:42.155492+00:00
-- url     : https://prove2.me/theorems/1c6313dd-46c9-4824-8a57-437dd22f690d
-- title:
--   Definition 9 — violations and Δ-consistency
-- statement:
--   For a set $S$ and assignment $\sigma:S\to[q]$, the violation set contains each unordered pair in $S$ whose assigned symbols are forbidden by its constraint. The assignment is $\Delta$-consistent precisely when the cardinality of this set is at most the real number $\Delta$. No consistency guarantee is stored in the instance.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Definition 9 — violations and Δ-consistency, printed p. 15 (PDF p. 17), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_CSP

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def violations {V : Type} [Fintype V] [LinearOrder V] {q : ℕ}
    (Y : CSP V q) (S : Finset V) (σ : S → Fin q) : Finset (Pair S) := by
  classical
  exact Finset.univ.filter (fun e => allows (restrictCSP Y S) e.val.1 e.val.2
    (σ e.val.1) (σ e.val.2) = false)
def Consistent {V : Type} [Fintype V] [LinearOrder V] {q : ℕ}
    (Y : CSP V q) (S : Finset V) (σ : S → Fin q) (Δ : ℝ) : Prop :=
  ((violations Y S σ).card : ℝ) ≤ Δ

end SmoothedPlanted.FFK


