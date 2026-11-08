-- Prove2me | Definitions.Def_AvoidPlast_IsPCPP
-- name    : AvoidPlast_IsPCPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:48:17.656341+00:00
-- url     : https://prove2.me/theorems/b99bee99-ab4d-4b01-adaa-56e7d4dd27a6
-- title:
--   The class PCPP$_{s,\delta}[r,q,t]$
-- statement:
--   A pair language $L$ is in **PCPP$_{s,\delta}[r,q,t]$** with verifier $V$ (read-only tapes for the explicit input $x$, the random string $\rho$, the implicit input $y$ and the proof $\pi$) if:
--
--   1. **Completeness**: if $(x,y)\in L$, some proof is accepted for every $\rho$;
--   2. **Soundness**: if $y$ is $\delta$-far from $\{y':(x,y')\in L\}$, every proof is accepted with probability at most $s$;
--   3. **Verification time**: $V$ halts within $t$ steps on every proof;
--   4. **Queries**: at most $q$ positions of $y$ and $\pi$ are read;
--   5. **Non-adaptivity**: the positions read depend only on $(x,\rho)$ and the lengths.
--
--   The parameters may depend on $x$ and $|y|$.
--
--   **Formalization Note** The paper takes this class from [BGH+05] without defining it; this is the standard definition.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.2, p.17 ([BGH+05])

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_queries
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_IsFar

namespace AvoidPlast

/-- `L ∈ PCPP_{s,δ}[r, q, t]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.2, p.17; the class is that of [BGH+05]), for a pair
language `L`, with `V` a verifier with read-only tapes for the explicit input `x`, the random string
`ρ`, the implicit input `y` and the proof `π`. The parameters may depend on `x` and `K = |y|`.

* Completeness: `(x, y) ∈ L` gives a proof accepted for every `ρ`.
* Soundness: if `y` is `δ`-far from `{y' : (x, y') ∈ L}`, every proof is accepted with probability
  at most `s`.
* Verification time: `V` halts within `t` steps, on every proof.
* Queries: at most `q` positions of `y` and `π` are read.
* Non-adaptivity: the positions read depend on `(x, ρ)` and the lengths only.

**Formalization Note** This paper does not define the class; it is taken from [BGH+05] (reading). -/
structure IsPCPP (V : Machine 4) (L : List Bool → List Bool → Prop)
    (s δ : List Bool → ℕ → ℝ) (r q t : List Bool → ℕ → ℕ) : Prop where
  /-- perfect completeness -/
  completeness : ∀ x y : List Bool, L x y → ∃ π : List Bool, ∀ ρ : List Bool,
    ρ.length = r x y.length → Accepts V ![x, ρ, y, π]
  /-- soundness against strings far from the language -/
  soundness : ∀ x y : List Bool, IsFar (δ x y.length) (L x) y → ∀ π : List Bool,
    prob (r x y.length) (fun ρ => Accepts V ![x, ρ, y, π]) ≤ s x y.length
  /-- verification time -/
  time : ∀ x y π ρ : List Bool, ρ.length = r x y.length →
    HaltsWithin V ![x, ρ, y, π] (t x y.length)
  /-- query complexity -/
  queryBound : ∀ x y π ρ : List Bool, ρ.length = r x y.length →
    (queries V ![x, ρ, y, π] 2).card + (queries V ![x, ρ, y, π] 3).card ≤ q x y.length
  /-- non-adaptivity -/
  nonadaptive : ∀ x y y' π π' ρ : List Bool, ρ.length = r x y.length →
    y'.length = y.length → π'.length = π.length →
    queries V ![x, ρ, y, π] 2 = queries V ![x, ρ, y', π'] 2 ∧
    queries V ![x, ρ, y, π] 3 = queries V ![x, ρ, y', π'] 3

end AvoidPlast


