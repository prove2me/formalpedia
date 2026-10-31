-- Prove2me | Definitions.Def_CombOpt_Circulation_delta
-- name    : CombOpt_Circulation_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:02.523982+00:00
-- url     : https://prove2.me/theorems/0b24149c-adb6-488f-883f-bab07f3439f4
-- title:
--   The cut $\delta(R)$: arcs leaving a node set
-- statement:
--   For a digraph $G=(V,E)$ and $R\subseteq V$, the **cut** determined by $R$ is the set of arcs leaving $R$,
--
--   $$
--   \delta(R)=\{vw : vw\in E,\ v\in R,\ w\notin R\}.
--   $$
--
--   The arcs entering $R$ are $\delta(\bar R)$, where $\bar R=V\setminus R$. An $(r,s)$-cut is a cut $\delta(R)$ with $r\in R$ and $s\notin R$.
--
--   **Formalization Note** A loop has both ends on the same side and belongs to no cut. Node sets are finsets; $\bar R$ is the finset complement.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 40 (PDF p. 49)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The cut `δ(R) = {vw : vw ∈ E, v ∈ R, w ∉ R}` of Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 40 (PDF p. 49): the arcs
leaving `R`. The set entering `R` is `δ(R̄)`, written `delta G Rᶜ` (`Ā = V \ A`, p. 40).

**Formalization Note** A loop has both ends on one side, so it is in no `delta G R`. -/
def delta (G : MultiDigraph V E) (R : Finset V) : Finset E :=
  Finset.univ.filter fun e => G.tail e ∈ R ∧ G.head e ∉ R

end CombOpt.Circulation


