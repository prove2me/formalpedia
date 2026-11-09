-- Prove2me | Definitions.Def_CEPolytopeHard_gateMap
-- name    : CEPolytopeHard_gateMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:44.37445+00:00
-- url     : https://prove2.me/theorems/fb7a1752-2951-473f-b75d-1891bf94d447
-- title:
--   Continuous gate maps $h_i$ and their Lipschitz constant $\lambda$
-- statement:
--   Each gate of a generalized circuit is replaced by a continuous map of its inputs $a, b$, clipped to $[0, 1]$ by $\mathrm{clip}_{[0,1]}(x) = \max\{0, \min\{x, 1\}\}$:
--
--   1. constant: $\mathrm{clip}(\beta)$; scaling: $\mathrm{clip}(\beta a)$; copying: $\mathrm{clip}(a)$;
--   2. addition: $\mathrm{clip}(a + b)$; subtraction: $\mathrm{clip}(a - b)$;
--   3. comparison: $h_<(a, b) = \mathrm{clip}_{[0,1]}\big(\tfrac12 + \tfrac{b - a}{2\tau}\big)$.
--
--   On $[0,1]^2$ with $\beta \in [0,1]$ these are $\beta$, $\beta a$, $a$, $\min\{a+b, 1\}$ and $\max\{a - b, 0\}$. Each satisfies $|h(a,b) - h(a',b')| \le \lambda(|a-a'| + |b-b'|)$ with
--   $$
--   \lambda = \max\{1, 1/(2\tau)\} \ge 1 .
--   $$
--
--   **Formalization Note** The paper writes "for a constant $\lambda \ge 1$" without naming it; the value above is the least constant $\ge 1$ valid for all gate maps. The Boolean gates listed on p.20 have no gate type in Section 2.5 and are not represented.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(i), "A polynomial map", p.20

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit

set_option autoImplicit false

namespace CEPolytopeHard

/-- clipping to `[0, 1]`: `clip_{[0,1]}(x) = max{0, min{x, 1}}` -/
noncomputable def clip01 (x : ℝ) : ℝ := max 0 (min x 1)

/-- The **continuous gate maps** `h_i` (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of Theorem 4(i), "A polynomial map", p.20:
"Each gate will be replaced by a continuous function of its inputs. For arithmetic gates, we use
the clipping operation to make sure that the output stays in [0, 1]. … Comparison:
h_<(a, b) = clip_{[0,1]}(1/2 + (b − a)/(2τ))"), for the gates of Section 2.5: constant `β`,
scaling `βa`, copying `a`, addition `a + b`, subtraction `a − b`, each clipped to `[0, 1]`, and
the comparison `h_<`. Arguments a gate does not use are ignored.

**Formalization Note** On `[0, 1]²` with `β ∈ [0, 1]` the clipped addition is `min{a + b, 1}` and
the clipped subtraction is `max{a − b, 0}`, the values of Section 2.5. The Boolean gates listed on
p.20 have no gate type in Section 2.5 and are not represented. -/
noncomputable def gateMap (τ : ℝ) : GGate → ℝ → ℝ → ℝ
  | .const β => fun _ _ => clip01 β
  | .scale β _ => fun a _ => clip01 (β * a)
  | .copy _ => fun a _ => clip01 a
  | .add _ _ => fun a b => clip01 (a + b)
  | .sub _ _ => fun a b => clip01 (a - b)
  | .cmp _ _ => fun a b => clip01 (1 / 2 + (b - a) / (2 * τ))

/-- The **Lipschitz constant `λ`** of the gate maps (p.20: "For a constant λ ≥ 1, each gate map
satisfies |h_i(a, b) − h_i(a′, b′)| ≤ λ(|a − a′| + |b − b′|)"): `λ = max{1, 1/(2τ)}`.

**Formalization Note** The paper leaves `λ` unnamed; the arithmetic maps are 1-Lipschitz and the
comparison map is `1/(2τ)`-Lipschitz, so this is the least constant `≥ 1` that works for every gate. -/
noncomputable def lam (τ : ℝ) : ℝ := max 1 (1 / (2 * τ))

end CEPolytopeHard


