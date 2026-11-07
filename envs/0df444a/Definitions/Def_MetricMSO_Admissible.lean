-- Prove2me | Definitions.Def_MetricMSO_Admissible
-- name    : MetricMSO_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:20.085344+00:00
-- url     : https://prove2.me/theorems/bbd9c584-567e-4ba2-8996-06faff119776
-- title:
--   Admissible $\mathbb Z_M$-labelings
-- statement:
--   A map $c:V(G)\to\mathbb Z_M$ is an **admissible $\mathbb Z_M$-labeling** if, for every edge $uv$, the difference $c(v)-c(u)$ is congruent to one of $-1,0,1$ modulo $M$.
--
--   Adjacent vertices thus receive equal or cyclically consecutive labels. Such labelings are the finite stand-ins for integer potentials.
--
--   **Formalization Note** `ZMod M` is $\mathbb Z/M\mathbb Z$. The paper fixes $M\ge3$, and every statement using this definition assumes it.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Definition 3.2, p.20 (PDF 22)

import Mathlib

namespace MetricMSO

/-- **Admissible `ℤ_M`-labeling**, Definition 3.2.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), Definition 3.2, p.20
(PDF 22): "A map c: V(G) → ZM is an admissible ZM-labeling if, for every edge uv ∈ E(G), the
difference c(v) − c(u) is congruent to one of −1, 0, and 1 modulo M."

`Admissible G c` holds iff `c v − c u ∈ {−1, 0, 1}` in `ZMod M` for all adjacent `u, v`.

**Formalization Note** `ZMod M` is `ℤ/Mℤ`; the paper fixes `M ≥ 3`, and every statement using this
definition assumes it. -/
def Admissible {V : Type} (G : SimpleGraph V) {M : ℕ} (c : V → ZMod M) : Prop :=
  ∀ u v, G.Adj u v → (c v - c u = -1 ∨ c v - c u = 0 ∨ c v - c u = 1)

end MetricMSO


