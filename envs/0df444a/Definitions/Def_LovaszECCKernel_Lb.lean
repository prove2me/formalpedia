-- Prove2me | Definitions.Def_LovaszECCKernel_Lb
-- name    : LovaszECCKernel_Lb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:38.943456+00:00
-- url     : https://prove2.me/theorems/8b70e851-8308-47ee-b6a2-201528d620ea
-- title:
--   Lovász's bound $\mathrm{Lb}(G)=|\overline E(G)|+s(|\overline E(G)|)$
-- statement:
--   For a finite simple graph $G$ with $\bar m=|\overline E(G)|$ non-edges, **Lovász's bound** is
--   $$\mathrm{Lb}(G)=\bar m+s(\bar m),$$
--   with $s(\bar m)$ the largest integer $t$ with $t^2-t\le\bar m$. Lovász (1968) proved that the edges of every graph can be covered by $\mathrm{Lb}(G)$ cliques; the mission's problem asks for covers with $\mathrm{Lb}(G)-k$ cliques.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 1, p.3 (= PDF p.3)

import Mathlib
import Definitions.Def_LovaszECCKernel_nonEdges
import Definitions.Def_LovaszECCKernel_sMax

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lovász's bound** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets
Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), Theorem 1, p.3 (= PDF p.3)):
"Lb(G) = |E(G̅)| + s(|E(G̅)|)."

**Formalization Note** `|E(G̅)|` is the number of non-edges `(nonEdges G).card`; `s` is `sMax`. -/
noncomputable def Lb {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (nonEdges G).card + sMax (nonEdges G).card

end LovaszECCKernel


