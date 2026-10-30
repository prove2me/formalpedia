-- Prove2me | Definitions.Def_PorteusGenSS_C2Tendsto
-- name    : PorteusGenSS_C2Tendsto
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:48.701987+00:00
-- url     : https://prove2.me/theorems/58147230-c64c-47e9-8c3c-e2bfbcc4b6be
-- title:
--   Limit of the tangent parameters $C_2(z)$
-- statement:
--   The paper assumes that $\lim_{z\downarrow0}C_2(z)=(c_0,K_0)$ and $\lim_{z\to\infty}C_2(z)=(c_\infty,K_\infty)$ exist: the slopes and intercepts of the tangents of $c$ converge at both ends. This predicate says that the sets $C_2(z)$ converge to a point $p$ along a filter: every neighbourhood of $p$ eventually contains $C_2(z)$.
--
--   **Formalization Note** $C_2(z)$ is a singleton for $z>0$, so set convergence is the ordinary limit of its element. The paper notes this rules out costs like $c(z)=z^{1/2}$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412

import Mathlib
import Definitions.Def_PorteusGenSS_C2

open Filter Topology

namespace PorteusGenSS

/-- **Limit of the tangent parameters C₂(z) (§II).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412: "We assume lim_{z↓0} C2(z) and lim_{z→∞} C2(z) exist, denoted,
respectively, by (c0, K0) and (c∞, K∞)."

`C2Tendsto c l p` says that the sets `C₂(z)` converge to the point `p` along the filter `l`:
every neighbourhood `U` of `p` contains `C₂(z)` for all `z` eventually along `l`.

**Formalization Note.** `C₂(z)` is a set (a singleton for concave `c` and `z > 0`, by the paper's
remark that it is nonempty and the uniqueness of `K_c`); its limit is encoded as convergence of
sets to a point. The mission uses `l = 𝓝[>] 0` (`z ↓ 0`) and `l = atTop` (`z → ∞`). -/
def C2Tendsto (c : ℝ → ℝ) (l : Filter ℝ) (p : ℝ × ℝ) : Prop :=
  ∀ U ∈ 𝓝 p, ∀ᶠ z in l, C2 c z ⊆ U

end PorteusGenSS


