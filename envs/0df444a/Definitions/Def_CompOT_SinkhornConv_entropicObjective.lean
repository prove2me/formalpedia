-- Prove2me | Definitions.Def_CompOT_SinkhornConv_entropicObjective
-- name    : CompOT_SinkhornConv_entropicObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:20:36.204992+00:00
-- url     : https://prove2.me/theorems/cf4cc5a9-7ed2-4455-a490-97611bfe3f92
-- title:
--   Entropic OT objective $\langle P, C\rangle - \varepsilon H(P)$
-- statement:
--   For a cost matrix $C\in\mathbb R^{n\times m}$, a regularization parameter $\varepsilon$ and a matrix $P$, the **entropic objective** is
--   $$\langle P, C\rangle - \varepsilon H(P) = \sum_{i,j} P_{i,j} C_{i,j} - \varepsilon H(P).$$
--
--   Problem (4.2), $L^\varepsilon_C(a,b) = \min_{P\in U(a,b)} \langle P, C\rangle - \varepsilon H(P)$, minimizes this function over the couplings; for $\varepsilon>0$ it has a unique solution.
--
--   **Formalization Note** In the mission, "$P$ solves (4.2)" is written as $P\in U(a,b)$ together with Mathlib's `IsMinOn` of this function on $U(a,b)$ at $P$.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.1, eq. (4.2), p. 425

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_entropy

namespace CompOT.SinkhornConv

/-- **Objective of entropic optimal transport `⟨P, C⟩ − ε H(P)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.1, eq. (4.2), p. 425: "LεC(a, b) := min_{P∈U(a,b)} ⟨P, C⟩ − εH(P)".

`entropicObjective C ε P` is `Σ_{i,j} P i j * C i j − ε · H(P)`, the function minimized over
the couplings `U(a, b)` in problem (4.2).

**Formalization Note.** `⟨P, C⟩` is the Frobenius inner product `Σ_{i,j} P_{i,j} C_{i,j}`
(notation of the paper, p. 360). A solution of (4.2) is expressed in the mission as a
`Q ∈ couplings a b` with `IsMinOn (entropicObjective C ε) (couplings a b) Q`. -/
noncomputable def entropicObjective {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (∑ i, ∑ j, P i j * C i j) - ε * entropy P

end CompOT.SinkhornConv


