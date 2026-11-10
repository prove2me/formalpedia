-- Prove2me | Definitions.Def_BilatMatch_typewise
-- name    : BilatMatch_typewise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:50.471391+00:00
-- url     : https://prove2.me/theorems/af148034-fc7c-45ec-8a27-48db043081ff
-- title:
--   Caps, cap-compatible families and the typewise contribution (5)
-- statement:
--   A **cap** is an initial set of seller reports (a down-set of the seller's report domain, possibly empty, open or closed at its top). A family of bilateral rules $z^\kappa(v,c)\in[0,1]$ indexed by caps is **cap-compatible** if each rule vanishes outside its cap, is nondecreasing in the buyer report $v$, nonincreasing in the seller report $c$, and nondecreasing in $\kappa$ under inclusion.
--
--   For a fixed cap the **typewise bilateral Lagrangian contribution** at buyer report $v$ is
--   $$\ell^\kappa_\alpha(v;z^\kappa)=(1+\alpha)v\,z^\kappa_B(v)-\alpha\int_{L_B}^vz^\kappa_B(u)\,du-\mathbb E_c\Big[(1+\alpha)c\,z^\kappa(v,c)+\alpha\int_c^{U_S}z^\kappa(v,u)\,du\Big],$$
--   with $z^\kappa_B(v)=\mathbb E_c[z^\kappa(v,c)]$ under the original seller prior, $L_B$ the lowest buyer and $U_S$ the highest seller report; on finite domains the integrals mean the sums stated below (5).
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.1, pp.8–9 (pdf pp.10–11), eq. (5)

import Mathlib
import Definitions.Def_BilatMatch_envelope

open MeasureTheory

namespace BilatMatch

/-!
# Caps, cap-compatible families and the typewise Lagrangian contribution

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.1, pp.8–9 (pdf pp.10–11), eq. (5).

**Formalization Note**
* A cap is an initial set (down-set) of the seller's report domain `DS`; it may be empty and, on
  an interval domain, open or closed at its top.
* A family `z κ v c ∈ [0,1]` (cap `κ`, buyer report `v`, seller report `c`) is cap-compatible when it
  vanishes outside its cap, is nondecreasing in `v`, nonincreasing in `c`, and nondecreasing in `κ`
  under inclusion (p.8), all for reports in the domains.
* The typewise contribution (5) uses the original seller prior `FS`, the buyer-side trade
  probability `z_B(v) = E_c[z(v, c)]`, the lowest buyer report `inf DB` and the highest seller report
  `sup DS`; on finite domains the integrals mean the discrete sums stated below (5).
-/

/-- `κ` is a cap: an initial set of the seller report domain `DS`. -/
def IsCap (DS κ : Set ℝ) : Prop := κ ⊆ DS ∧ ∀ c ∈ κ, ∀ c' ∈ DS, c' ≤ c → c' ∈ κ

/-- Cap-compatibility of a family of bilateral rules `z κ v c` on the buyer domain `DB` and seller
domain `DS` (p.8). -/
def IsCapCompatible (DB DS : Set ℝ) (z : Set ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ κ, IsCap DS κ →
    (∀ v ∈ DB, ∀ c ∈ DS, 0 ≤ z κ v c ∧ z κ v c ≤ 1) ∧
    (∀ v ∈ DB, ∀ c ∈ DS, c ∉ κ → z κ v c = 0) ∧
    (∀ c ∈ DS, MonotoneOn (fun v => z κ v c) DB) ∧
    (∀ v ∈ DB, AntitoneOn (z κ v) DS) ∧
    (∀ κ', IsCap DS κ' → κ ⊆ κ' → ∀ v ∈ DB, ∀ c ∈ DS, z κ v c ≤ z κ' v c)

/-- The typewise bilateral Lagrangian contribution `ℓ^κ_α(v; z^κ)`, eq. (5) (p.9), of a fixed-cap
rule `z = z^κ` at buyer report `v`:
`(1+α) v z_B(v) − α ∫_{L_B}^v z_B − E_c[(1+α) c z(v,c) + α ∫_c^{U_S} z(v,u) du]`. -/
noncomputable def typewise (α : ℝ) (DB DS : Set ℝ) (FS : Measure ℝ) (z : ℝ → ℝ → ℝ)
    (v : ℝ) : ℝ :=
  (1 + α) * v * (∫ c, z v c ∂FS) - α * buyerRent DB (fun u => ∫ c, z u c ∂FS) v -
    ∫ c, ((1 + α) * c * z v c + α * sellerRent DS (z v) c) ∂FS

end BilatMatch


