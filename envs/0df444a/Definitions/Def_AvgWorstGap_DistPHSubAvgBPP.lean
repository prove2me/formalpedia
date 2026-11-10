-- Prove2me | Definitions.Def_AvgWorstGap_DistPHSubAvgBPP
-- name    : AvgWorstGap_DistPHSubAvgBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:36.834996+00:00
-- url     : https://prove2.me/theorems/4d93345e-67f4-48d7-8203-d2055807c543
-- title:
--   $\mathrm{DistPH}\subseteq\mathsf{AvgBPP}$, $\mathsf{PH}\subseteq\mathsf{BPP}$ and $\mathsf{NP}\subseteq\mathsf{BPP}$
-- statement:
--   The three class inclusions of the main theorem:
--
--   - $\mathrm{DistPH}\subseteq\mathsf{AvgBPP}$: for every $L\in\mathsf{PH}$ and every $D\in\mathsf{PSAMP}$, $(L,D)\in\mathsf{AvgBPP}$;
--   - $\mathsf{PH}\subseteq\mathsf{BPP}$: every $L\in\mathsf{PH}$ is in $\mathsf{BPP}$;
--   - $\mathsf{NP}\subseteq\mathsf{BPP}$: every $L\in\mathsf{NP}$ is in $\mathsf{BPP}$.
--
--   "PH heuristica" is the world where the first holds and the second fails.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 1.1, p.4; §2.5, p.17; Theorem 3.1, p.19

import Mathlib
import Definitions.Def_AvgWorstGap_AvgBPP
import Definitions.Def_AvgWorstGap_InPSAMP
import Definitions.Def_AvgWorstGap_InSigmaPO

namespace AvgWorstGap

open NKtLB

/-- **`DistPH ⊆ AvgBPP`** (arXiv:2610.19162, version of October 30, 2026, Theorem 1.1, p.4; §2.5,
p.17: "we let DistC denote the set of distributional problems `(L, D)` with `L ∈ C` and
`D ∈ PSAMP`"): for every `L ∈ PH` and every `D ∈ PSAMP`, `(L, D) ∈ AvgBPP`. -/
def DistPHSubAvgBPP : Prop :=
  ∀ L : Set (List Bool), InPH L → ∀ D : ℕ → PMF (List Bool), InPSAMP D → AvgBPP L D

/-- **`PH ⊆ BPP`** (Theorem 1.1, p.4). -/
def PHSubBPP : Prop := ∀ L : Set (List Bool), InPH L → InBPP L

/-- **`NP ⊆ BPP`** (Theorem 3.1, p.19). -/
def NPSubBPP : Prop := ∀ L : Set (List Bool), InNP L → InBPP L

end AvgWorstGap


