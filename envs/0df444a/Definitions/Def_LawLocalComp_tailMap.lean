-- Prove2me | Definitions.Def_LawLocalComp_tailMap
-- name    : LawLocalComp_tailMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:26.133703+00:00
-- url     : https://prove2.me/theorems/47f4ccf3-df7a-461c-9f68-c6f00be2099f
-- title:
--   Tail-transfer map of Lemma 7.2
-- statement:
--   The map $T_{r,\delta,\rho}$ fixes point masses. For any other law $X=b+R$, with $b$ its least atom and $\nu=\mathbb E[R\mid R>0]$, it partitions the residual into $\{0\}$, $(0,\delta\nu)$, the ratio-$\rho$ intervals in $[\delta\nu,3\nu r)$ and the tail cell $[3\nu r,\infty)$, and replaces the full value $b+R$ by its conditional mean on each cell.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 7.2, p.13

import Mathlib
import Definitions.Def_LawLocalComp_cellReplace
import Definitions.Def_LawLocalComp_cellKey
import Definitions.Def_LawLocalComp_baseline
import Definitions.Def_LawLocalComp_activeMean
open Classical

namespace LawLocalComp

/-- **The tail-transfer map of Lemma 7.2.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 7.2, p.13 ("Partition each residual into {0}, (0, δν), ratio-ρ intervals in [δν, 3νr), and
one tail cell [3νr, ∞). Replace the full value b + R by its cell mean; fix point masses").

`tailMap r δ ρ X` is `X` itself for a point mass; otherwise, with `b` the least atom and `ν` the
active mean, it replaces `X` on each cell of `cellKey r δ ρ b ν` by the cell's conditional mean. -/
noncomputable def tailMap (r : ℕ) (δ ρ : ℝ) (X : Law) : Law :=
  if X.w.support.card ≤ 1 then X
  else cellReplace X (cellKey r δ ρ (baseline X) (activeMean X (baseline X)))

end LawLocalComp


