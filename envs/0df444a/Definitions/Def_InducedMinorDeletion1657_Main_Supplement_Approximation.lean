-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Supplement_Approximation
-- name    : InducedMinorDeletion1657_Main_Supplement_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:14:42.179206+00:00
-- url     : https://prove2.me/theorems/420bae10-8d79-48ca-ad24-07e1f550b7dc
-- title:
--   Hereditary MSO deletion and multiplicative approximation
-- statement:
--   Let $\varphi$ be a closed graph MSO sentence. It is **hereditary** when satisfaction is preserved by every induced-subgraph embedding between finite graphs, including the empty graph. This applies the published general hereditary graph-class predicate to the graph class defined by actual MSO satisfaction.
--
--   For a graph $G$, treewidth bound $t$ and real accuracy $\varepsilon$, the output is either failure or a vertex set. Failure occurs exactly when no feasible deletion exists. A returned set $S$ is feasible and satisfies
--   $$|S|\le(1+\varepsilon)|R|\quad\text{for every feasible deletion set }R.$$
--   Feasibility means both $\operatorname{tw}(G-S)\le t$ and $G-S\models\varphi$. Thus the comparison is against the true optimum and includes optimum zero. No optimum value is assigned on infeasible instances.
--
--   The execution bound is
--   $$Q_{C,c}(n)=C\,2^{C(\log_2(n+2))^c}.$$
--   Positive natural constants $C,c$, chosen before the input, describe the quasipolynomial class; $n+2$ makes the bound meaningful at small inputs. This interface expresses the guarantee in Theorem 1.2 without imposing any algorithmic correctness on a machine by definition.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), pp. 3, 10, 33 (PDF pp. 4, 11, 34), Theorem 1.2, basic notions, and Section 7 running time

import Definitions.Def_InducedMinorDeletion1657_Main_Execution
import Definitions.Def_FatFlat_Hereditary_Basic

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main.Supplement

/-- Section 3, printed p.10: hereditary means preserved by induced subgraphs.
The general graph-class notion is published; this only applies it to MSO satisfaction. -/
def hereditary (φ : Sentence) : Prop :=
  FatFlat.Hereditary.IsHereditary (fun _ _ G => models G φ)

/-- Theorem 1.2: explicit failure or a feasible multiplicative approximation,
compared against every feasible set, including the zero optimum. -/
def approxResult (G : InputGraph) (t : ℕ) (φ : Sentence) (ε : ℝ)
    (o : Option (Finset (Fin G.n))) : Prop :=
  (o = none ↔ infeasible G.graph t φ) ∧
  ∀ S, o = some S → feasible G.graph t φ S ∧
    ∀ R, feasible G.graph t φ R → (S.card : ℝ) ≤ (1 + ε) * R.card

/-- Uniform quasipolynomial bound, using n+2 to cover small input sizes.
Section 7, printed p.33, supplies exponent ten; Theorem 1.2 only asserts this class. -/
noncomputable def qpTime (C c n : ℕ) : ℝ :=
  C * (2 : ℝ) ^ ((C : ℝ) * (logTwo ((n : ℝ) + 2)) ^ c)

end InducedMinorDeletion1657.Main.Supplement


