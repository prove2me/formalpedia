-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsSpanning
-- name    : AbelianCayleyHDX_IsSpanning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:19.443661+00:00
-- url     : https://prove2.me/theorems/822ec7e7-4e94-4553-82fd-15d745433b34
-- title:
--   Spanning set of directions
-- statement:
--   A set $D \subseteq \mathrm{PG}(t-1, F)$ is **spanning** if its representatives span $V_0 = F^t$.
--
--   **Formalization Note** One chosen representative per direction is used; scaling does not change the span.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11

import Mathlib
import Definitions.Def_AbelianCayleyHDX_PG

namespace AbelianCayleyHDX

/-- **Spanning direction set** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11): "a set `D ⊆ PG(t − 1, F)` is spanning
if its representatives span `V₀ = F^t`".

**Formalization Note** One representative per direction (`Projectivization.rep`) is used; the
span of all representatives is the same. -/
def IsSpanning {t : ℕ} {F : Type*} [Field F] (D : Finset (PG t F)) : Prop :=
  Submodule.span F ((fun d : PG t F => d.rep) '' (D : Set (PG t F))) = ⊤

end AbelianCayleyHDX


