-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_RoundTrip
-- name    : StrictTwoGroups_TwoEquiv_RoundTrip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:32.637982+00:00
-- url     : https://prove2.me/theorems/4d894e24-e636-4228-a462-7d6bac19c70b
-- title:
--   §6, pp. 15–16 — the components ξ_G = (id, ϕ⁻¹) and ζ_χ = (id, π₁|ker π₂)
-- statement:
--   The round-trip components (Porst, §6, pp. 15–16). For a strict 2-group $\mathcal G$, $ST\mathcal G=(G_0,\ \ker s\rtimes G_0,\ \pi_2,\ t\pi_1\cdot\pi_2,\ i_2)$ and
--   $$\xi_{\mathcal G}=(\mathrm{id}_{G_0},\varphi^{-1}):ST\mathcal G\to\mathcal G,\qquad \varphi^{-1}(h,g)=h\,ig .$$
--   For a crossed module $\chi$, $TS\chi=(G,\ \ker\pi_2,\ \tau\pi_1|_{\ker\pi_2},\ \mathrm{Ad}_{i_2})$ with $\ker\pi_2\subseteq H\rtimes G$, and
--   $$\zeta_\chi=(\mathrm{id}_G,\ \pi_1|_{\ker\pi_2}):TS\chi\to\chi .$$
--
--   **Formalization Note** The paper writes the domain of $\xi_{\mathcal G}$ as $TS\mathcal G$; the composite applied to a strict 2-group is $ST\mathcal G$ ($T$ first), which is the domain used here (in Lean, `(T.comp S).obj G`).
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 15, §6 (ξ_G); p. 16, §6 (ζ_χ)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- `ξ_G = (id_{G₀}, ϕ⁻¹) : STG → G` (§6, p. 15), where `STG = (G₀, ker s ⋊ G₀, …)` and
`ϕ⁻¹(h, g) = h · i(g)` is the inverse of the isomorphism (11). -/
def xi (G : StrictTwoGroup.{u}) : twoGrp.Hom1 ((T.comp S).obj G) G :=
  (fun g => g, fun x : ↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0 =>
    (x.left : G.G1) * G.i x.right)

/-- `ζ_χ = (id_G, π₁|_{ker π₂}) : TSχ → χ` (§6, p. 16), where `TSχ = (G, ker π₂, …)` and
`ker π₂ ⊆ H ⋊ G`. -/
def zeta (χ : CrossedModule.{u}) : xMod.Hom1 ((S.comp T).obj χ) χ :=
  (fun g => g, fun h : ↥(toTwoGrp χ).s.ker =>
    SemidirectProduct.left (h.1 : χ.H ⋊[χ.α] χ.G))

end StrictTwoGroups.TwoEquiv


