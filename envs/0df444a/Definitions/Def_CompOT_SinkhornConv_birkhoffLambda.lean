-- Prove2me | Definitions.Def_CompOT_SinkhornConv_birkhoffLambda
-- name    : CompOT_SinkhornConv_birkhoffLambda
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:54:35.109731+00:00
-- url     : https://prove2.me/theorems/f6903912-b844-4ba8-b545-c73cd633c9c9
-- title:
--   Birkhoff's contraction ratio $\lambda(K)$
-- statement:
--   For an $n\times m$ matrix $K$ with positive entries,
--   $$\lambda(K) = \frac{\sqrt{\eta(K)}-1}{\sqrt{\eta(K)}+1},$$
--   where $\eta(K)$ is Birkhoff's constant.
--
--   Since $\eta(K)\ge 1$, one has $0\le\lambda(K)<1$. Theorem 4.1 states that $K$ contracts the Hilbert projective metric by the factor $\lambda(K)$, and Theorem 4.2 gives Sinkhorn's iterations the linear rate $\lambda(K)^2$ per full iteration.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, Theorem 4.1, p. 440 (definition of λ(K))

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_birkhoffEta

namespace CompOT.SinkhornConv

/-- **Birkhoff's contraction ratio `λ(K) = (√η(K) − 1)/(√η(K) + 1)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), Theorem 4.1, p. 440: "λ(K) := (√η(K) − 1)/(√η(K) + 1)".

`birkhoffLambda K` is `(√η(K) − 1)/(√η(K) + 1)` with `η(K) = birkhoffEta K`.

**Formalization Note.** For entrywise positive `K` with at least one row and one column,
`η(K) ≥ 1` (take `i = j`), so `0 ≤ λ(K) < 1`; this is how every statement of the mission uses it. -/
noncomputable def birkhoffLambda {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (Real.sqrt (birkhoffEta K) - 1) / (Real.sqrt (birkhoffEta K) + 1)

end CompOT.SinkhornConv


