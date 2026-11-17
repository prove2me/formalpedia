-- Prove2me | Definitions.Def_FairReplay_Supplement_activeVertices
-- name    : FairReplay_Supplement_activeVertices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:42:50.639701+00:00
-- url     : https://prove2.me/theorems/a3da0c1d-31c1-42ad-b200-9d00236bc351
-- title:
--   Active vertices $V_+(H)$ of a residual graph
-- statement:
--   For a residual fairness graph $H$ on finitely many vertices, the set of **active vertices** is
--   $$V_+(H)=\{v:\deg_H(v)>0\},$$
--   the vertices incident to at least one residual edge. Its size $n_+=|V_+(H)|$ counts the inputs that a full suite-replay round must execute.
--
--   **Formalization Note** $H$ is a simple graph on $\mathrm{Fin}\,n$ with decidable adjacency.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10 "Observation primitives", p.11 (PDF p.13); §3, p.3 (PDF p.5)

import Mathlib

namespace FairReplay.Supplement

/-- **Active vertices of a residual graph** `V+(H) = {v : deg_H(v) > 0}` (Sah, Zhang, Lian, *Testing
Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, §10 "Observation primitives", p.11 (PDF p.13): "Write V+(H) = {v : degH(v) > 0}";
§3, p.3: "Write V+(H) for vertices incident to a residual edge").

`activeVertices H` is the finite set of vertices of the simple graph `H` on `Fin n` that are incident
to at least one edge of `H`.

**Formalization Note** The residual graph is a `SimpleGraph` on the finite vertex type `Fin n`
(undirected, loopless), with decidable adjacency so that degrees are computable. -/
def activeVertices {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < H.degree v)

end FairReplay.Supplement


