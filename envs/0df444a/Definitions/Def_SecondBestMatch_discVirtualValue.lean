-- Prove2me | Definitions.Def_SecondBestMatch_discVirtualValue
-- name    : SecondBestMatch_discVirtualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:30.77129+00:00
-- url     : https://prove2.me/theorems/37af6e0f-179c-4260-9e48-b82389e11882
-- title:
--   Discrete virtual value $\phi_i$
-- statement:
--   Let a buyer prior have support $0\le v_1<\dots<v_L\le1$ with $f_\ell = \Pr[v=v_\ell]>0$ and $F_\ell = \sum_{h\le\ell} f_h$. The **virtual value** is
--   $$
--   \phi(v_\ell) := v_\ell - \frac{(v_{\ell+1}-v_\ell)(1-F_\ell)}{f_\ell}\quad(\ell<L),\qquad \phi(v_L) = v_L.
--   $$
--
--   **Formalization Note** $v_{\ell+1}$ is the least atom above $v_\ell$, $1-F_\ell = \mu(v_\ell,\infty)$ and $f_\ell = \mu\{v_\ell\}$. At the top atom $\mu(v_L,\infty)=0$, so the formula gives $\phi(v_L) = v_L$ as printed. Values off the support are never used. This is the unironed discrete virtual value, not the ironed `MatchingGFT.TightE.virtualValue`.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, p.10

import Mathlib
import Definitions.Def_SecondBestMatch_atoms

open MeasureTheory Set

namespace SecondBestMatch

/-- The discrete virtual value of a buyer (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.10): at the support point `v_ℓ`,
`φ(v_ℓ) = v_ℓ − (v_{ℓ+1} − v_ℓ)(1 − F_ℓ)/f_ℓ` for `ℓ < L`, and `φ(v_L) = v_L`.

**Formalization Note** `v_{ℓ+1}` is the least atom above `v`, `1 − F_ℓ = μ(v, ∞)` and
`f_ℓ = μ{v}`. At the top atom `μ(v, ∞) = 0`, so the junk value of `sInf ∅` is multiplied by `0` and
`φ(v_L) = v_L` as printed. Values off the atoms are never used. This is the unironed discrete
virtual value, not `MatchingGFT.TightE.virtualValue`. -/
noncomputable def discVirtualValue (μ : Measure ℝ) (v : ℝ) : ℝ :=
  v - (sInf (atoms μ ∩ Ioi v) - v) * μ.real (Ioi v) / μ.real {v}

end SecondBestMatch


