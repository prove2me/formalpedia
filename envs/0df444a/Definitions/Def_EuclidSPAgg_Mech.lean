-- Prove2me | Definitions.Def_EuclidSPAgg_Mech
-- name    : EuclidSPAgg_Mech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:28.182195+00:00
-- url     : https://prove2.me/theorems/9e1835eb-33c7-414f-9694-864cfd539ecc
-- title:
--   Deterministic mechanism $f:E^n\to E$
-- statement:
--   For $n$ agents, a **mechanism** is a deterministic map $f:E^n\to E$. A profile $x=(x_1,\dots,x_n)\in E^n$ records the reported ideal points, and $f(x)$ is the selected location.
--
--   **Formalization Note** $E=\mathbb R^d$ is the published `RBMSensitivity.E d`, i.e. `EuclideanSpace ℝ (Fin d)`; the standing assumption $d\ge1$ is a hypothesis of every theorem. A profile is a function from $\{0,\dots,n-1\}$ to $E$ (agents are indexed from $0$). Continuity of a mechanism refers to the product topology on $E^n$, which is the Euclidean topology.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- A deterministic mechanism `f : Eⁿ → E` for `n` agents (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)).

**Formalization Note** `E d = ℝᵈ` is the published `RBMSensitivity.E d`, i.e.
`EuclideanSpace ℝ (Fin d)` with coordinates indexed by `Fin d` (0-based); the paper's standing
assumption `d ≥ 1` (p.8) is a hypothesis of every theorem. A profile is a function `Fin n → E d`
(agents 0-based). Determinism is
built in: a mechanism is a function. The topology on profiles is the product topology, which is
the Euclidean topology of `Eⁿ`. -/
abbrev Mech (n d : ℕ) : Type := (Fin n → E d) → E d

end EuclidSPAgg


