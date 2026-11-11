-- Prove2me | Definitions.Def_LpBallVI_Affine_Construction
-- name    : LpBallVI_Affine_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:47.822853+00:00
-- url     : https://prove2.me/theorems/5ef80e78-9272-4c11-a5d8-5d1a274442ad
-- title:
--   The affine VI of §4.2: coefficient families, the coordinates (z₀, ζ), node values x_v, affine inputs h_ℓ(ζ) and the operator F of (39)–(40)
-- statement:
--   A **coefficient family** is a length $m$ and reals $\alpha_{\rm gate, j}, a_{\rm gate, j}, \beta_{\rm gate, j}$ for gate $\in \{\mathrm{NOR}, \mathrm{PURIFY}\}$, $j \in [m]$; $H = \sum_j |\alpha_{{\rm NOR},j}| + \sum_j |\alpha_{{\rm PURIFY},j}|$ (45). For a PureCircuit instance with $n$ nodes, the coordinates are an anchor $z_0$ and, for each node $v$, sample $j$ and kind, six auxiliary coordinates $r^-_{v,j}, r^0_{v,j}, r^+_{v,j}, w^-_{v,j}, w^0_{v,j}, w^+_{v,j}$ ($d_{\rm aux} = 6mn$). The node value is $x_v = \varsigma_p \sum_j \alpha_{{\rm gate}(v), j}(w^+_{v,j} + w^-_{v,j} - 2 w^0_{v,j})$ (37). With $s = a_{{\rm gate}(v),j}\, s_v(x) + \beta_{{\rm gate}(v),j}$ and $d_{v,j} = r^+_{v,j} - 2r^0_{v,j} + r^-_{v,j}$, the affine inputs $h_\ell(\zeta)$ of $r^-, r^0, r^+, w^-, w^0, w^+$ are $s - 1, s, s+1, 4 - d_{v,j}/4, 4, 4 + d_{v,j}/4$. The operator is
--   $$F_0(z) = c_R,\qquad F_\ell(z) = h_\ell(\zeta) - \zeta_\ell\quad (\ell \in [d_{\rm aux}]),$$
--   which is affine in $z = (z_0, \zeta)$.
--
--   **Formalization Note** The construction is parametric: in the paper the coefficients come from Lemma 4.6 applied to $\hat\phi_{\rm NOR}, \hat\phi_{\rm PURIFY}$ with $\eta = 1/128$, and $R$, $c_R$ from Lemma 4.10. Coordinates are indexed by `Option (Fin n × Fin m × Fin 6)` (`none` = anchor; kinds $0..5$ = $r^-, r^0, r^+, w^-, w^0, w^+$).
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), pp. 30–31, §4.2.2–4.2.3, (37)–(40); p. 32, (45)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Geometry
import Definitions.Def_LpBallVI_Affine_PureCircuit
import Definitions.Def_LpBallVI_Affine_WeightedApprox

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- The coefficients of the two weighted approximation functions `N^NOR_λ`, `N^PURIFY_λ` of §4.2
(Anagnostides–Panageas–Yan, arXiv:2611.04151, p. 30): one common length `m` and, for each gate
type, coefficients `α_{gate,j}`, `a_{gate,j}`, `β_{gate,j}`, `j ∈ [m]`. In the paper they come from
Lemma 4.6 applied to `ϕ̂_NOR` and `ϕ̂_PURIFY`; here they are a parameter. -/
structure CoeffFamily where
  m : ℕ
  αN : Fin m → ℝ
  aN : Fin m → ℝ
  βN : Fin m → ℝ
  αP : Fin m → ℝ
  aP : Fin m → ℝ
  βP : Fin m → ℝ

/-- `H = ∑_j |α_{NOR,j}| + ∑_j |α_{PURIFY,j}|` ((45), p. 32). -/
noncomputable def CoeffFamily.H (c : CoeffFamily) : ℝ :=
  (∑ j, |c.αN j|) + ∑ j, |c.αP j|

/-- The coordinates of the VI of §4.2.3 (p. 31): `none` is the anchor coordinate `z₀`; `some (v, j, k)`
is the auxiliary coordinate of node `v`, sample `j` and kind `k`, with kinds
`0, 1, 2, 3, 4, 5 = r⁻, r⁰, r⁺, w⁻, w⁰, w⁺` (p. 30). There are `d_aux + 1 = 6mn + 1` coordinates. -/
abbrev Coord (n m : ℕ) := Option (Fin n × Fin m × Fin 6)

/-- The coefficients `(α, a, β)` used for node `v`: the NOR ones if `v` is the output of a NOR gate,
the PURIFY ones otherwise (p. 30). -/
noncomputable def coeffsOf (I : PCInst) (c : CoeffFamily) (v : Fin I.n) :
    (Fin c.m → ℝ) × (Fin c.m → ℝ) × (Fin c.m → ℝ) := by
  classical
  exact if I.IsNorOutput v then (c.αN, c.aN, c.βN) else (c.αP, c.aP, c.βP)

/-- The node value `x_v = ς_p ∑_j α_{gate(v),j} (w⁺_{v,j} + w⁻_{v,j} − 2w⁰_{v,j})` ((37), p. 30),
read off the coordinates `z`. -/
noncomputable def nodeValue (p : ℝ) (I : PCInst) (c : CoeffFamily) (z : Coord I.n c.m → ℝ)
    (v : Fin I.n) : ℝ :=
  realization p (coeffsOf I c v).1 (fun j => z (some (v, j, 3))) (fun j => z (some (v, j, 4)))
    (fun j => z (some (v, j, 5)))

/-- The inverse-mapping input `h_ℓ(ζ)` of auxiliary coordinate `ℓ = (v, j, k)` ((38), p. 31, from
the equations on p. 30): with `s = a_{gate(v),j} s_v(x) + β_{gate(v),j}` and
`d_{v,j} = r⁺_{v,j} − 2r⁰_{v,j} + r⁻_{v,j}`, the inputs are `s − 1, s, s + 1` for `r⁻, r⁰, r⁺` and
`4 − d_{v,j}/4, 4, 4 + d_{v,j}/4` for `w⁻, w⁰, w⁺`. -/
noncomputable def auxInput (p : ℝ) (I : PCInst) (c : CoeffFamily) (z : Coord I.n c.m → ℝ)
    (ℓ : Fin I.n × Fin c.m × Fin 6) : ℝ :=
  let v := ℓ.1
  let j := ℓ.2.1
  let s := (coeffsOf I c v).2.1 j * I.sIn (nodeValue p I c z) v + (coeffsOf I c v).2.2 j
  let dv := z (some (v, j, 2)) - 2 * z (some (v, j, 1)) + z (some (v, j, 0))
  match ℓ.2.2 with
  | 0 => s - 1
  | 1 => s
  | 2 => s + 1
  | 3 => 4 - dv / 4
  | 4 => 4
  | 5 => 4 + dv / 4

/-- **The affine operator of §4.2.3** ((39)–(40), p. 31): `F₀(z) = c_R` on the anchor coordinate
and `F_ℓ(z) = h_ℓ(ζ) − ζ_ℓ` on each auxiliary coordinate, for a `PureCircuit` instance `I`, a
coefficient family `c` and the anchor coefficient `c_R`. It is affine in `z`. -/
noncomputable def vecF (p : ℝ) (I : PCInst) (c : CoeffFamily) (cR : ℝ) (z : Coord I.n c.m → ℝ) :
    Coord I.n c.m → ℝ
  | none => cR
  | some ℓ => auxInput p I c z ℓ - z (some ℓ)

end LpBallVI.Affine


