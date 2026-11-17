-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SATLowerBound
-- name    : AvoidPlast_Supplement_SATLowerBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:55:31.243685+00:00
-- url     : https://prove2.me/theorems/777398da-eae3-4f61-b252-36c3249ab008
-- title:
--   $\mathrm{DSPACE}[O(n)]\not\subseteq\mathrm{i.o.SIZE}^{\mathrm{SAT}}[2^{\delta n}]$
-- statement:
--   The derandomization hypothesis of Theorems 1.3 and 5.9: for some $\delta>0$ some language decidable in linear space is not in $\mathrm{i.o.SIZE}^{\mathrm{SAT}}[2^{\delta n}]$.
--
--   Following [KvM02], it yields pseudorandom generators fooling SAT-oracle circuits, which derandomize the AM verifiers of the paper into $\Sigma_k$ machines.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.3, 5.9, pp.4, 25

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_InSPACE
import Definitions.Def_AvoidPlast_Supplement_InIoSizeSAT

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The derandomization hypothesis of Theorems 1.3 and 5.9 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), pp.4, 25):
`DSPACE[O(n)] ⊄ i.o.SIZE^SAT[2^{δn}]` for some `δ > 0`. -/
def SATLowerBound : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : Set (List Bool), InSPACE (fun n => (n : ℝ)) L₀ ∧
    ¬ InIoSizeSAT (fun n => (2 : ℝ) ^ (δ * n)) L₀

end AvoidPlast.Supplement


