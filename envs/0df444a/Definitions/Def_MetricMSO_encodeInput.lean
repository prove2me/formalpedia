-- Prove2me | Definitions.Def_MetricMSO_encodeInput
-- name    : MetricMSO_encodeInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:26.914389+00:00
-- url     : https://prove2.me/theorems/37db1f4a-36a2-476e-87dd-4fc7e7606441
-- title:
--   The binary input of a task and its length $N$
-- statement:
--   The binary input of a task, whose length is the **total binary input length** $N$: the codes of the task, the graph, the interpretations of the input predicates, the formula, the numbers of free set variables and, for the weighted tasks, the signed binary weights. No decomposition, expression or width is part of the input ("We do not require a tree decomposition or a cliquewidth expression as part of the input", p.29).
--
--   **Formalization Note** The graph is an adjacency matrix preceded by $n$ in binary, and edge predicates are $n\times n$ bit matrices; any two standard graph encodings have polynomially related lengths, so running times $f(k)N^{O(1)}$ do not depend on this choice. Weights of the unweighted tasks (deciding and plain counting) are not in the input.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, p.17 (PDF 19); §5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_CorrectAnswer

namespace MetricMSO

open ExponomialAssortment.FPTAS (encodeNat encodeInt)

open Classical in
/-- Binary code of a graph on `Fin n`: `n` in binary, then the `n²` bits of the adjacency matrix
row by row. -/
noncomputable def encodeGraph {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  encodeNat n ++ (List.ofFn fun a : Fin n => List.ofFn fun b : Fin n => decide (G.Adj a b)).flatten

open Classical in
/-- Binary code of an instance: the graph, then `q` and the `n` membership bits of each vertex
predicate, then `q'` and the `n²` membership bits (pairs `(a, b)`) of each edge predicate. -/
noncomputable def encodeInstance (I : Instance) : List Bool :=
  encodeGraph I.G ++
  encodeNat I.q ++
  (List.ofFn fun j => List.ofFn fun a : Fin I.n => decide (a ∈ I.vpred j)).flatten ++
  encodeNat I.q' ++
  (List.ofFn fun j => (List.ofFn fun a : Fin I.n => List.ofFn fun b : Fin I.n =>
    decide (s(a, b) ∈ I.epred j)).flatten).flatten

open Classical in
/-- Signed binary code of the weights: for each vertex-set variable the codes `encodeInt (w_i(a))`
of the vertices `a = 0, …, n − 1`; for each edge-set variable the codes `encodeInt (w_i(ab))` of the
edges `ab` of `G`, listed once each by the pairs `a < b`. -/
noncomputable def encodeWeights {I : Instance} {rV rE : ℕ} (w : Weights I rV rE) : List Bool :=
  (List.ofFn fun i => (List.ofFn fun a : Fin I.n => encodeInt (w.wV i a)).flatten).flatten ++
  (List.ofFn fun i => (List.ofFn fun a : Fin I.n => (List.ofFn fun b : Fin I.n =>
    if a < b ∧ I.G.Adj a b then encodeInt (w.wE i s(a, b)) else []).flatten).flatten).flatten

open Classical in
/-- **The binary input of a task**, whose length is the total binary input length `N`.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.17 (PDF 19): "we
write N for the total binary input length, including the formula, the interpretations of the input
predicates, and any weights"; p.29 (PDF 31): "We do not require a tree decomposition or a
cliquewidth expression as part of the input."

The concatenation of the codes of the task, the instance (graph and input predicates), the formula,
the numbers `rV`, `rE` of free vertex-set and edge-set variables, and, for the four weighted tasks,
the signed binary weights. Nothing else (no decomposition, no expression, no width) is part of the
input.

**Formalization Note** The graph is written as an adjacency matrix and the edge predicates as
`n × n` bit matrices; any two standard graph encodings have polynomially related lengths, so the
running-time bounds `f(k)·N^{O(1)}` do not depend on this choice. -/
noncomputable def encodeInput (task : Task) (I : Instance) (φ : Formula) (rV rE : ℕ)
    (w : Weights I rV rE) : List Bool :=
  encodeNat task.index ++ encodeInstance I ++ φ.encode ++ encodeNat rV ++ encodeNat rE ++
    (if task.weighted then encodeWeights w else [])

end MetricMSO


