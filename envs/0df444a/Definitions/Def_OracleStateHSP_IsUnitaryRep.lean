-- Prove2me | Definitions.Def_OracleStateHSP_IsUnitaryRep
-- name    : OracleStateHSP_IsUnitaryRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:17.078461+00:00
-- url     : https://prove2.me/theorems/5f8fe816-595b-44ad-9638-c524fe4b1901
-- title:
--   Unitary representation $R : G \to U(\mathcal H)$
-- statement:
--   A map $R$ from an (additively written) group $G$ to matrices on $\mathcal H$ is a **unitary representation** if every $R(g)$ is unitary, $R(0) = I$, and
--   $$
--   R(g + h) = R(g)\, R(h) \quad \text{for all } g, h \in G .
--   $$
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 1.3, p.6

import Mathlib

namespace OracleStateHSP

/-- `R : G → U(H)` is a unitary representation of the (additive) group `G` on the Hilbert space
with basis `ι`: every `R g` is unitary, `R 0 = I` and `R (g + h) = R g R h` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656,
Definition 1.3, p.6: "a unitary representation `R : G → U(H)`"). -/
def IsUnitaryRep {G ι : Type*} [AddGroup G] [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) : Prop :=
  (∀ g, R g ∈ Matrix.unitaryGroup ι ℂ) ∧ R 0 = 1 ∧ ∀ g h, R (g + h) = R g * R h

end OracleStateHSP


