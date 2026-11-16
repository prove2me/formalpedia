-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_rerouteWeight
-- name    : AgnosticTNS_Supplement_rerouteWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:22.244727+00:00
-- url     : https://prove2.me/theorems/3cc0575a-87c5-4e83-ac4a-0465906a179d
-- title:
--   Rerouted edge dimensions $w'$
-- statement:
--   With $q:=w(\{x,y\})$ and $w$ extended by $1$ off $E$, the rerouted edge dimensions on $E'$ are
--   $$
--   w'(f) = \begin{cases} q\,w(\{x,z\}), & f=\{x,z\},\\ q\,w(\{y,z\}), & f=\{y,z\},\\ w(f), & \text{otherwise.}\end{cases}
--   $$
--   If $\{x,z\}$ was not an edge of $G$, its new dimension is $q$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.8, Eqs. (6.6), (6.8), p.49

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_rerouteGraph
import Definitions.Def_AgnosticTNS_Supplement_extW

namespace AgnosticTNS.Supplement

/-- **The rerouted edge dimensions** `w′`, Eq. (6.8), Theorem 6.8, p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
with `q = w({x, y})` and `w` extended by `1` off `E`, `w′({x, z}) = q·w({x, z})`,
`w′({y, z}) = q·w({y, z})`, and `w′(f) = w(f)` otherwise. -/
noncomputable def rerouteWeight {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) (x y z : Fin n) :
    (rerouteGraph G x y z).edgeSet → ℕ := fun f =>
  if f.1 = s(x, z) then extW G w s(x, y) * extW G w s(x, z)
  else if f.1 = s(y, z) then extW G w s(x, y) * extW G w s(y, z)
  else extW G w f.1

end AgnosticTNS.Supplement


