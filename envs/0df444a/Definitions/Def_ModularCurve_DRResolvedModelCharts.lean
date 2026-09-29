-- Prove2me | Definitions.Def_ModularCurve_DRResolvedModelCharts
-- name    : ModularCurve_DRResolvedModelCharts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/979321d0-7841-5022-99ba-356e11ac68c4
-- title:
--   Étale crossing charts on a resolved Deligne–Rapoport model
-- statement:
--   Throughout, $p$ is a prime, $\mathfrak{X}$ is a `DRModelPackage p` (a package of data and properties for the two-chart integral model `DRModel p` of the full modular curve of level $p$ over $\mathbb{Z}$, with its two special-fibre components `compInf`, `compZero` over an algebraically closed field), $O$ is a commutative ring, $\kappa$ an algebraically closed field of characteristic $p$, $\mathrm{to}\kappa : O \to \kappa$ a ring homomorphism, and $\mathfrak{X}^{\mathrm{reg}}$ is a `DRResolvedModelPackage p 𝔛 O κ toκ`, whose carrier is a scheme $Y$ with a proper map `toDR` to $\mathfrak{X}_O := \mathrm{DRModel}\,p \times_{\mathbb{Z}} \operatorname{Spec} O$, a finite type `node` of crossings with widths `width`, a bijection `nodeEquiv` onto the points of $\mathrm{compInf}\,\kappa \times \mathrm{compZero}\,\kappa$, and invertible ideal sheaves `comp` indexed by the subdivided dual graph `X0MqComponents width`.
--
--   First, `crossingPt n` is the point of $\mathfrak{X}_O$ obtained from `nodeEquiv n` by the first projection of that fibre product, followed by $\mathrm{compInf}\,\kappa$ and the base-change map $\mathfrak{X}_\kappa \to \mathfrak{X}_O$.
--
--   Second, for $\varpi \in O$ and a family `Fc` assigning to each $e$ and each $d \in \{0,\dots,e\}$ an ideal sheaf datum on the project's resolution $\mathrm{Res}(\varpi,e)$ of $\operatorname{Spec} O[x,y]/(xy-\varpi^{e})$, the structure `DRResolvedModelCharts` records, for every node $n$ of width $e$: an open $U_n \subseteq \mathfrak{X}_O$ containing `crossingPt n` and no other `crossingPt m`; an étale $O$-morphism $f_n : U_n \to \operatorname{Spec} O[x,y]/(xy-\varpi^{e})$ with $f_n(y)$ in $D(x) \cup D(y)$ exactly when $y \neq$ `crossingPt n`; the requirement that on the fibre product $U_n \times \mathrm{Res}(\varpi,e)$ the second projection be injective on points whose first projection is `crossingPt n`; a morphism $g_n$ from $\mathrm{toDR}^{-1}(U_n)$ to $\mathrm{Res}(\varpi,e)$ and an isomorphism $\Phi_n$ from $U_n \times \mathrm{Res}(\varpi,e)$ to $\mathrm{toDR}^{-1}(U_n)$ carrying the two projections to the restriction of `toDR` and to $g_n$; and, for each $d \in \{0,\dots,e\}$, equality of the restriction to $\mathrm{toDR}^{-1}(U_n)$ of the component ideal sheaf at chain position `chainPos width n d` (position $0$ the first strict transform, $1,\dots,e-1$ the exceptional sheaves attached to $n$, position $e$ the second strict transform) with the pull-back of `Fc e d` along $g_n$. The étaleness field is registered as an instance.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (schemes, fibre products, `Etale`, `Scheme.IdealSheafData`, open subschemes); the crossing scheme $\operatorname{Spec} O[x,y]/(xy-\varpi^{e})$, its resolution `Resolution` with the map `Resolution.toCrossing`, and the Deligne–Rapoport model packages are the project's own definitions, and this chart structure has no Mathlib counterpart.
--
--   **Where it is used.** The structure is a data carrier for the local analysis of the resolved Deligne–Rapoport model of the modular curve at the supersingular crossing points of its fibre at $p$: it presents an étale neighbourhood of each crossing as a standard $\varpi^{e}$-crossing and identifies the resolution over it with the explicit toric resolution, together with the labelling of the components of the special fibre. It is used in the component and divisor-class computations on such models that underlie the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRResolvedModelCharts.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

noncomputable section

namespace ModularCurve

variable {p : ℕ} [Fact p.Prime]

namespace DRResolvedModelPackage

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

def crossingPt (n : 𝔛reg.node) : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) :=
  (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)

structure DRResolvedModelCharts (ϖ : O) (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) where
  U : 𝔛reg.node → (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens
  mem_U : ∀ n, 𝔛reg.crossingPt n ∈ U n
  not_mem_U : ∀ n m, m ≠ n → 𝔛reg.crossingPt m ∉ U n
  f : ∀ n, (U n).toScheme ⟶ crossingScheme (ϖ ^ 𝔛reg.width n)
  etale : ∀ n, Etale (f n)
  f_over : ∀ n, f n ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ 𝔛reg.width n)))) =
    (U n).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  f_mem_Vc_iff : ∀ n (y : U n),
    (f n).base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens)) ↔
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) ≠ 𝔛reg.crossingPt n
  hinj : ∀ n (y y' : ↥(pullback (f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))),
    ((pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y).1 = 𝔛reg.crossingPt n →
      ((pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y').1 = 𝔛reg.crossingPt n →
        (pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y =
          (pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y' → y = y'
  g : ∀ n, (𝔛reg.toDR ⁻¹ᵁ (U n)).toScheme ⟶ Resolution ϖ (𝔛reg.width n)
  Φ : ∀ n, pullback (f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≅ (𝔛reg.toDR ⁻¹ᵁ (U n)).toScheme
  Φ_fst : ∀ n, (Φ n).hom ≫ (𝔛reg.toDR ∣_ U n) = pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
  Φ_snd : ∀ n, (Φ n).hom ≫ g n = pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
  label : ∀ n (d : Fin (𝔛reg.width n + 1)),
    (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).comap (𝔛reg.toDR ⁻¹ᵁ (U n)).ι =
      (Fc (𝔛reg.width n) d).comap (g n)

attribute [instance] DRResolvedModelCharts.etale

end DRResolvedModelPackage

end ModularCurve

end


