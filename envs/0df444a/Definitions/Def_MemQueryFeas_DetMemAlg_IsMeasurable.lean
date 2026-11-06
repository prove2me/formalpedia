-- Prove2me | Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable
-- name    : MemQueryFeas_DetMemAlg_IsMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:49.997456+00:00
-- url     : https://prove2.me/theorems/fa0a6763-8d4d-4c0d-874b-caab3a9399a4
-- title:
--   Measurable deterministic algorithm
-- statement:
--   A deterministic $M$-bit algorithm is **measurable** if for every memory state $m$ and query $x$ the update $g\mapsto\psi_{update}(m,x,g)$ is a Borel function of the returned normal $g\in\mathbb R^d$.
--
--   This makes the memory states of the learner against a random instance random variables, as used in the information quantities of §3.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.2, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_MemQueryFeas_DetMemAlg

namespace MemQueryFeas

/-- **Measurable deterministic algorithm.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.2, pp.10–11 (PDF pp.11–12): the memory states
`Mem_v` of a deterministic learner run against the random hard instance are random variables whose
mutual information with the hidden subspaces is bounded (Definition 4). This presupposes that the
memory update is a measurable function of the oracle's response.

`alg.IsMeasurable`: for every memory state `m` and query `x`, the map `g ↦ update m x (some g)` is
Borel measurable. -/
def DetMemAlg.IsMeasurable {d M : ℕ} (alg : DetMemAlg d M) : Prop :=
  ∀ (m : Fin M → Bool) (x : Vec d), Measurable (fun g : Vec d => alg.update m x (some g))

end MemQueryFeas


