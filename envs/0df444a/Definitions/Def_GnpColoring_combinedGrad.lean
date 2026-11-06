-- Prove2me | Definitions.Def_GnpColoring_combinedGrad
-- name    : GnpColoring_combinedGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:43.26976+00:00
-- url     : https://prove2.me/theorems/1f8cc1ae-4319-4ca9-8274-ce3200a77c8a
-- title:
--   The combined gradient $\hat\nabla^c_\sigma f$
-- statement:
--   $\hat\nabla^c_\sigma f\in\mathbb R^V$ equals $\nabla^c_\sigma f(v)$ at singletons $v\in S$, $\tilde\nabla^c_{B,\sigma}f(v)$ at a port $v$ of a block $B$, and $0$ elsewhere.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Corollary 3.26, p.33

import Mathlib
import Definitions.Def_GnpColoring_recolorGrad
import Definitions.Def_GnpColoring_portGrad
import Definitions.Def_GnpColoring_ports
import Definitions.Def_GnpColoring_blockOf

open scoped Classical
open Finset

namespace GnpColoring

/-- **The combined gradient** `∇̂^c_σ f ∈ ℝ^V` (Corollary 3.26): `∇^c_σ f(v)` for `v ∈ S`,
`∇̃^c_{B,σ} f(v)` for `v` a port of a block `B`, and `0` otherwise.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Corollary 3.26, p.33.

**Formalization Note** The block of `v ∉ S` is `blockOf G S v`. -/
noncomputable def combinedGrad {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (S : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) (c : Fin q) (σ : Fin n → Fin q) (v : Fin n) : ℝ :=
  if v ∈ S then recolorGrad G f c σ v
  else if v ∈ ports G (blockOf G S v) then portGrad G q (blockOf G S v) f c σ v
  else 0

end GnpColoring


