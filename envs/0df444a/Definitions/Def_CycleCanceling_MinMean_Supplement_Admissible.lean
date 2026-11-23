-- Prove2me | Definitions.Def_CycleCanceling_MinMean_Supplement_Admissible
-- name    : CycleCanceling_MinMean_Supplement_Admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:18:15.550508+00:00
-- url     : https://prove2.me/theorems/d5dc8367-975c-4145-bf3a-34730d8d504a
-- title:
--   Admissible graph, admissible simple cycles and acyclicity
-- statement:
--   For a finite symmetric circulation network $N$, a real arc flow $f$ and real vertex prices $p$, write $u_f(v,w)=u(v,w)-f(v,w)$ and $c_p(v,w)=c(v,w)+p(v)-p(w)$. The admissible graph has arc set
--
--   $$E(f,p)=\{(v,w)\in E:u_f(v,w)>0,\ c_p(v,w)<0\}.$$
--
--   An admissible cycle is a nonempty residual simple cycle every arc of which has negative reduced cost. The graph is acyclic when it contains no such cycle. These definitions provide the graph used in Lemma 3.4 and in Step 1 of cancel-and-tighten.
--
--   **Formalization Note** The published network and cycle conventions are reused. Cycles are vertex lists with no repeated vertices, closed by rotation; acyclicity includes exclusion of length-one cycles. No assumptions on the flow are built into the graph; theorem and run domains supply a genuine circulation.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 878, Section 3, admissible graph definition; p. 880, Section 4

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 3, p. 878: the arcs of the admissible graph G(f,p). -/
noncomputable def admissibleArcs (N : CircNetwork V) (f : V → V → ℝ)
    (p : V → ℝ) : Finset (V × V) :=
  N.E.filter (fun a => 0 < resCap N f a.1 a.2 ∧ reducedCost N p a.1 a.2 < 0)

/-- An admissible cycle is a residual simple cycle all of whose reduced costs are negative. -/
def IsAdmissibleCycle (N : CircNetwork V) (f : V → V → ℝ)
    (p : V → ℝ) (Γ : List V) : Prop :=
  IsResidualCycle N f Γ ∧ ∀ a ∈ cycleArcs Γ, reducedCost N p a.1 a.2 < 0

/-- No simple directed cycle in the admissible graph (including length-one loops). -/
def IsAdmissibleAcyclic (N : CircNetwork V) (f : V → V → ℝ) (p : V → ℝ) : Prop :=
  ∀ Γ : List V, ¬ IsAdmissibleCycle N f p Γ

end CycleCanceling.MinMean.Supplement


