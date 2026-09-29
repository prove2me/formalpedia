-- Prove2me | Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
-- name    : ModularCurve_DRModelPackageLevelCrossingFrame
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/bfb524c8-e216-5520-a920-6464d86017c8
-- title:
--   Crossing-point vocabulary for level-Γ0​(N0​q) Deligne–Rapoport models
-- statement:
--   Throughout, $q$ is a prime, $N_0\ge 1$ with $q\nmid N_0$, and $\mathfrak X$ is a `DRModelPackageLevel N₀ q hqN`, whose underlying scheme is `DRLevel.X N₀ q = IgusaScheme (N₀*q) q` with its structure morphism to $\operatorname{Spec}$ of $R_q=$ `DRLevel.R q`; further data are a ring map $\rho_O\colon R_q\to O$ and a ring map $\mathrm{to}\kappa\colon O\to\kappa$ into an algebraically closed field $\kappa$ of characteristic $q$. Here $X_O=$ `DRLevel.XO ρO` is the base change $X\times_{\operatorname{Spec}R_q}\operatorname{Spec}O$, and `DRLevel.bcMap ρO toκ` is the induced morphism from the geometric fibre `DRLevel.fibre (toκ ∘ ρO)` to $X_O$.
--
--   Five abbreviations are introduced. `DRLevel.XO.toBase ρO` names the second pullback projection $X_O\to\operatorname{Spec}(O)$. For a point $n$ of the fibre product of the two component morphisms $\mathfrak X.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa\circ\rho_O)\,0$ and $\dots\,1$ (each a closed immersion of the level-$N_0$ geometric fibre `fibre0` into the level-$N_0q$ geometric fibre), `crossingPt` is the image of $n$ in the topological space of $X_O$ under the first projection, followed by the component indexed $0$, followed by `bcMap ρO toκ`. `baseGerm ρO x o`, for $x\in X_O$ and $o\in O$, is the germ at $x$ of the global section of $X_O$ obtained by transporting $o$ to a global section of $\operatorname{Spec}(O)$ and pulling it back along the structure morphism; it lies in the stalk $\mathcal O_{X_O,x}$. Finally `ξinf` and `ξzero` are the images in $X_O$ of the generic point of `fibre0` — integral by `DRModelPackageLevel.isIntegral_fibre0` — under the component indexed $0$, respectively $1$, followed by `bcMap ρO toκ`; thus they are the generic points of the images of the two components of the $q$-fibre. Nothing is asserted here: the module only fixes notation.
--
--   **Relation to Mathlib.** The declarations package Mathlib's scheme-theoretic constructions (fibre products, stalks and germs, the $\Gamma$–$\mathrm{Spec}$ isomorphism, generic points of integral schemes) for the project's modular-curve models; the models themselves and the notion of branch ideal of a specialisation are project definitions.
--
--   **Where it is used.** These names provide the shared vocabulary for the local analysis of the level-$\Gamma_0(N_0q)$ Deligne–Rapoport model over $O$ at a crossing point of its $q$-fibre: transversality of the two branches through $x_n$, principality of each branch modulo $q$, and the oriented étale chart $uv=q^{e}$. That local structure is what underlies the Deligne–Rapoport description of $X_0(N_0q)$ in characteristic $q$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRModelPackageLevelCrossingFrame.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

abbrev XO.toBase {O : Type} [CommRing O] (ρO : R q →+* O) : XO (N₀ := N₀) ρO ⟶ Spec (CommRingCat.of O) :=
  pullback.snd _ _

end DRLevel

namespace DRModelPackageLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  {O : Type} [CommRing O] (ρO : DRLevel.R q →+* O)
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)

abbrev crossingPt (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base n

abbrev baseGerm (x : ↥(DRLevel.XO (N₀ := N₀) ρO)) (o : O) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x :=
  (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ x trivial
    ((DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))

abbrev ξinf : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  letI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))

abbrev ξzero : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  letI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))

end DRModelPackageLevel

end ModularCurve

end


