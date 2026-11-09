-- Prove2me | Definitions.Def_AgnosticTNS_TTN_IsOn
-- name    : AgnosticTNS_TTN_IsOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:14.739675+00:00
-- url     : https://prove2.me/theorems/1c13f4ab-1c7e-4cf6-8c18-fa5965f93d81
-- title:
--   TTN on a given tree $T$
-- statement:
--   A TTN description is **on the tree** $T=([n],E)$ if its nodes are the vertices of $T$, qudit $v$ sits at node $v$, the edges $\{k,\mathrm{parent}(k)\}$ are exactly the edges of $T$, and exactly one node is the root.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, p.25; Corollaries 5.1–5.2, pp.39–40

import Mathlib
import Definitions.Def_AgnosticTNS_TTN

namespace AgnosticTNS

/-- **A TTN on a given tree `T`**, Proposition 3.8 (p.25), Corollaries 5.1–5.2 (pp.39–40)
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the nodes are the vertices of `T`, qudit `v` sits at node `v`, the edges `{k, parent k}`
are exactly the edges of `T`, and exactly one node is the root. -/
def TTN.IsOn {n d : ℕ} (D : TTN n n d) (T : SimpleGraph (Fin n)) : Prop :=
  (∀ v, D.site v = v) ∧ (∀ u v, T.Adj u v ↔ (D.parent u = some v ∨ D.parent v = some u)) ∧
    ∃! k, D.parent k = none

end AgnosticTNS


