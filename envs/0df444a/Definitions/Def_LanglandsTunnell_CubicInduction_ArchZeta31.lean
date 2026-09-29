-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
-- name    : LanglandsTunnell_CubicInduction_ArchZeta31
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7a440441-cd12-5fed-9ccd-eb4f5eed1e03
-- title:
--   Archimedean zeta integrals for GL(3) Whittaker functions
-- statement:
--   This module sets up the archimedean local counterparts of the adelic $\mathrm{GL}(3)\times\mathrm{GL}(1)$ zeta integrals. The ambient group is $\mathrm{GL}_3$ of the infinite adele ring of $\mathbb{Q}$; the data are a complex-valued function $W$ on that group, a group homomorphism $\sigma$ from the units of the infinite adele ring to $\mathbb{C}^\times$, a complex parameter $s$, and a point $g$. Measures are explicit arguments: a measure $\mu$ on the unit group and, where needed, a measure $\nu$ on the additive ring, with respect to measurable space structures taken from the section context; all integrals are Bochner integrals, hence zero when the integrand fails to be integrable. The norm occurring in the integrands is the norm of the infinite adele underlying a unit $a$.
--
--   `archZeta31` is the double integral $\int (\int W(\iota(\mathrm{diag}(a,1))\,u_{21}(x)\,g)\,d\nu(x))\,\sigma(a)\,\|a\|^{s-1}\,d\mu(a)$, where $u_{21}(x)$ is the lower unipotent element of $\mathrm{GL}_3$ with $(2,1)$-entry $x$ and `iotaGL (diagUnitGL2 a)` is the embedding into $\mathrm{GL}_3$ of the $\mathrm{GL}_2$ diagonal unit attached to $a$. `archZeta30` is the corresponding single integral $\int W(\iota(\mathrm{diag}(a,1))\,g)\,\sigma(a)\,\|a\|^{s-1}\,d\mu(a)$, with no unipotent integration. `archZetaDual31` is not a separate integral but the value of `archZeta31` formed from the dual Whittaker function $h \mapsto W(w_{\mathrm{long}}\cdot {}^t h^{-1})$, the inverse character $\sigma^{-1}$, and the translated point $w'\cdot {}^t g^{-1}$, where $w_{\mathrm{long}}$ is the long Weyl element and $w'$ the transposition interchanging the last two coordinates; these are exactly the elements entering the global definitions `globalZeta31` and `globalZetaDual31`.
--
--   The two remaining items are convergence predicates rather than analytic theorems: `IsArchZeta30ConvergentAbove` asserts that for every $s$ with $\mathrm{Re}(s) > \sigma_0$ the integrand of `archZeta30` is $\mu$-integrable, and `IsArchZeta31ConvergentAbove` asserts that for every such $s$ the integrand of `archZeta31`, regarded as a function of the pair $(a,x)$, is integrable for the product measure $\mu \times \nu$ — so the latter records absolute convergence of the double integral in the strong, Fubini-ready form.
--
--   **Relation to Mathlib.** Mathlib has no Rankin–Selberg or Hecke zeta integrals for $\mathrm{GL}_3$; these are the project's own definitions, built on Mathlib's Bochner integral, `Measure.prod` and `Integrable`, and on its infinite adele ring of a number field.
--
--   **Where it is used.** These archimedean integrals and their abscissa-of-convergence predicates are the local data at the infinite place accompanying the global $\mathrm{GL}(3)\times\mathrm{GL}(1)$ zeta integrals, used in the converse-theorem input to the Langlands–Tunnell theorem, which supplies the modularity of the residual representation at the start of the Frey–Serre–Ribet–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_ArchZeta31.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Archimedean

variable {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} {mA : MeasurableSpace (InfiniteAdeleRing ℚ)}

def archZeta31 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  ∫ a : (InfiniteAdeleRing ℚ)ˣ,
      (∫ x : InfiniteAdeleRing ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) *
        ((σ a : ℂˣ) : ℂ) * ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def archZeta30 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  ∫ a : (InfiniteAdeleRing ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((σ a : ℂˣ) : ℂ) *
        ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def archZetaDual31 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  archZeta31 μ ν (dualWhittakerFn3 W) σ⁻¹ s (weylPrime3 * transposeInv3 g)

def IsArchZeta30ConvergentAbove (μ : Measure (InfiniteAdeleRing ℚ)ˣ)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun a : (InfiniteAdeleRing ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((σ a : ℂˣ) : ℂ) *
        ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) μ

def IsArchZeta31ConvergentAbove (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((σ p.1 : ℂˣ) : ℂ) *
        ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)

end Archimedean

end LanglandsTunnell.CubicInduction

end


