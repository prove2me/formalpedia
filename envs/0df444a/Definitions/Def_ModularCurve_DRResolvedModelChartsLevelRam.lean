-- Prove2me | Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
-- name    : ModularCurve_DRResolvedModelChartsLevelRam
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a90793a1-d8b8-5891-9227-3fc7aeb12dc8
-- title:
--   Étale crossing charts on a ramified resolved Deligne–Rapoport model
-- statement:
--   The standing context is a prime $q$, a level $N_0$ with $q \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{X}$ for level $N_0q$, a commutative ring $\mathcal{O}$ with a ring map $\rho_{\mathcal{O}}$ from the base ring `DRLevel.R q` and an element $\varpi \in \mathcal{O}$, an algebraically closed residue field $\kappa$ of characteristic $q$ with $\mathcal{O} \to \kappa$, and a package $\mathfrak{X}^{\mathrm{reg}}$ of type `DRResolvedModelPackageLevelRam` for these data.
--
--   The auxiliary definition `crossingPt` sends a node index $n$ to a point of the base-changed model `DRLevel.XO ρO`: it is the image of $\mathfrak{X}^{\mathrm{reg}}.\mathrm{nodeEquiv}(n)$, a point of the fibre product of the two component maps $\mathfrak{X}.\mathrm{comp}\,\kappa\,0$ and $\mathfrak{X}.\mathrm{comp}\,\kappa\,1$, under the first projection followed by $\mathfrak{X}.\mathrm{comp}\,\kappa\,0$ and then `DRLevel.bcMap`.
--
--   The structure `DRResolvedModelChartsLevelRam`, parametrised by a family $F_c$ assigning to each $e$ and each $d \in \{0,\dots,e\}$ an ideal sheaf on `Resolution ϖ e`, is a pure data carrier: it asserts nothing by itself. Its fields give, for each node $n$ of width $e = \mathrm{width}(n)$: an open $U_n$ of the base-changed model containing $\mathrm{crossingPt}(n)$ and no other $\mathrm{crossingPt}(m)$; an étale morphism $f_n : U_n \to \operatorname{Spec} \mathcal{O}[x,y]/(xy-\varpi^{e})$, commuting with the structure morphisms to $\operatorname{Spec}\mathcal{O}$, such that $f_n(y)$ lies in $D(x) \cup D(y)$ exactly when $y \neq \mathrm{crossingPt}(n)$; injectivity of the second projection of $U_n \times_{\operatorname{Spec}\mathcal{O}[x,y]/(xy-\varpi^{e})} \mathrm{Res}_e$ on points whose first projection is $\mathrm{crossingPt}(n)$; a morphism $g_n$ from $\mathrm{toDR}^{-1}(U_n)$ to $\mathrm{Res}_e$ together with an isomorphism $\Phi_n$ from that fibre product onto $\mathrm{toDR}^{-1}(U_n)$ carrying the two projections to the restriction of $\mathrm{toDR}$ and to $g_n$; and the labelling condition that, for each $d$, the component ideal sheaf of the package at chain position $d$ over $n$, pulled back to $\mathrm{toDR}^{-1}(U_n)$, agrees with the pull-back of $F_c^{(e)}(d)$ along $g_n$. Étaleness of each $f_n$ is registered as an instance.
--
--   **Relation to Mathlib.** The ambient notions (`Etale`, `pullback`, `Scheme.IdealSheafData` and its `comap`) are Mathlib's; the target schemes $\operatorname{Spec}\mathcal{O}[x,y]/(xy-t)$ and their chart-by-chart resolutions `Resolution` are defined in the project, and Mathlib has no notion of étale local charts on a model of a modular curve.
--
--   **Where it is used.** These charts pin down the local structure of a regular model of $X_0(N_0q)$ over a possibly ramified base at each crossing point of its special fibre, identifying a neighbourhood in the resolution with the standard resolution of $xy = \varpi^{e}$ and matching the model's component ideal sheaves with the standard labelled ones. That identification is what makes the component and intersection bookkeeping on the special fibre at $q$ available, as needed for the study of the Jacobian of $X_0(N_0q)$ in characteristic $q$ underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRResolvedModelChartsLevelRam.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

noncomputable section

namespace ModularCurve

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRResolvedModelPackageLevelRam

variable {hqN : ¬ q ∣ N₀} {𝔛 : DRModelPackageLevel N₀ q hqN} {O : Type} [CommRing O] {ρO : DRLevel.R q →+* O} {ϖ : O}
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackageLevelRam N₀ q 𝔛 O ρO ϖ κ toκ)

def crossingPt (n : 𝔛reg.node) : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)

structure DRResolvedModelChartsLevelRam (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) where
  U : 𝔛reg.node → (DRLevel.XO (N₀ := N₀) ρO).Opens
  mem_U : ∀ n, 𝔛reg.crossingPt n ∈ U n
  not_mem_U : ∀ n m, m ≠ n → 𝔛reg.crossingPt m ∉ U n
  f : ∀ n, (U n).toScheme ⟶ crossingScheme (ϖ ^ 𝔛reg.width n)
  etale : ∀ n, Etale (f n)
  f_over : ∀ n, f n ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ 𝔛reg.width n)))) =
    (U n).ι ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
  f_mem_Vc_iff : ∀ n (y : U n),
    (f n).base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens)) ↔
      (y : ↥(DRLevel.XO (N₀ := N₀) ρO)) ≠ 𝔛reg.crossingPt n
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
    (𝔛reg.comp (DRResolvedModelPackageLevel.chainPos 𝔛reg.width n d)).comap (𝔛reg.toDR ⁻¹ᵁ (U n)).ι =
      (Fc (𝔛reg.width n) d).comap (g n)

attribute [instance] DRResolvedModelChartsLevelRam.etale

end DRResolvedModelPackageLevelRam

end ModularCurve

end


