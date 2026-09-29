-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
-- name    : LanglandsTunnell_CubicInduction_AdelicEpstein
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/143fb001-1629-5815-801a-20c87c4b049b
-- title:
--   Adelic Epstein integrals for GL₃ over the rationals
-- statement:
--   Throughout, $\mathbb{A}$ denotes the adele ring of $\mathbb{Q}$ (as the adele ring of $\mathcal{O}_{\mathbb{Q}}$ over $\mathbb{Q}$), and $\widehat{\mathbb{Z}}^{\times}$ denotes [`IsDedekindDomain.FiniteAdeleRing.unitIdeles`](../def/IsDedekindDomain_FiniteUnitIdeles.html#L9), the subgroup of those units of the finite adele ring whose value at every height-one prime, and whose inverse's value at every height-one prime, lies in the corresponding ring of integers. A real number $t$ is transported into the completion of $\mathbb{Q}$ at its (real) infinite place by `ofReal`, the inverse of the ring isomorphism of that completion with $\mathbb{R}$. From this, `archIdele t` is the idele which is $1$ for $t=0$ and otherwise the image of the unit $t$ under `TateGlobal.archUnitHom` at the infinite place, i.e. the idele with archimedean component $t$ and component $1$ elsewhere; dually `finUnitIdele u` sends $u\in\widehat{\mathbb{Z}}^{\times}$ to the idele with finite part $u$ and archimedean part $1$, via `AdelicLevel.finIncl`. A rational row vector $\xi\in\mathbb{Q}^{3}$ is read coordinatewise in $\mathbb{A}^{3}$ by `adelicDiag`, and `point t u g ξ`, for $g\in \mathrm{GL}_3(\mathbb{A})$, is the row vector $\xi g$ with every coordinate multiplied by the adele underlying $\mathrm{archIdele}(t)\cdot\mathrm{finUnitIdele}(u)$.
--
--   `scaleMeasure` is Lebesgue measure on $\mathbb{R}$ restricted to $(0,\infty)$ with density $t^{-1}$, that is $dt/t$. For $\Phi:\mathbb{A}^{3}\to\mathbb{C}$, `latticeSum Φ t u g` is the unconditional sum of $\Phi(\mathrm{point}\ t\,u\,g\,\xi)$ over the subtype of non-zero $\xi\in\mathbb{Q}^{3}$ (hence $0$ when the family fails to be summable). Given a $\sigma$-algebra on $\widehat{\mathbb{Z}}^{\times}$ and a measure $du$ on it, `epstein` is $\|\det g\|^{\sigma}$, where $\|\cdot\|$ is `TateGlobal.ideleNorm` (the idele norm defined through the Haar scaling character), times the Bochner integral over `scaleMeasure` of $t^{3\sigma}$ times the Bochner integral of the lattice sum against $du$; non-integrable integrands contribute $0$. `epsteinPlus` is the $[0,\infty]$-valued analogue, formed with $\|\Phi\|$ and with the sum over non-zero $\xi$ and both integrals taken as lower integrals in $[0,\infty]$. Finally `unitIdeleMeasurableSpace` is the $\sigma$-algebra on $\widehat{\mathbb{Z}}^{\times}$ pulled back along $u\mapsto \mathrm{finUnitIdele}(u)$ from the Borel $\sigma$-algebra [`NumberField.AdelicHaar.adeleBorel`](../def/NumberField_AdelicHaar.html#L132) on $\mathbb{A}$, for which `measurable_finUnitIdele` records that this pullback map is measurable.
--
--   **Relation to Mathlib.** Mathlib supplies the adele and finite adele rings, infinite-place completions and the Haar scaling character `distribHaarChar`; the unit ideles of the finite adeles, the idele norm, and the Epstein-type lattice sums and integrals, the measure $dt/t$ and the pulled-back $\sigma$-algebra on the finite unit ideles are the project's own.
--
--   **Where it is used.** These objects belong to the $\mathrm{GL}_3$-over-$\mathbb{Q}$ part of the Langlands–Tunnell input to the modularity argument, where the relevant $L$-series is studied through adelic integrals of Schwartz-type functions against lattice sums over non-zero rational row vectors. The $[0,\infty]$-valued variant `epsteinPlus` is the form in which absolute convergence of these integrals is stated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_AdelicEpstein.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory LanglandsTunnell.CubicInduction

namespace LanglandsTunnell.CubicInduction.AdelicEpstein

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

def ofReal (t : ℝ) : Rat.infinitePlace.Completion :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm t

def archIdele (t : ℝ) : 𝔸ˣ :=
  if h : t = 0 then 1 else
    TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (by unfold ofReal; exact (map_ne_zero _).mpr h))

def finUnitIdele (u : Ẑˣ) : 𝔸ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

def adelicDiag (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 := fun i => algebraMap ℚ 𝔸 (ξ i)

def point (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 :=
  fun i => ((archIdele t * finUnitIdele u : 𝔸ˣ) : 𝔸) * (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸)) i

def scaleMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹

def latticeSum (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, Φ (point t u g ξ)

def epstein [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ : ℝ) : ℂ) *
    ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ t u g ∂du ∂scaleMeasure

def epsteinPlus [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ENNReal :=
  ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
    ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) *
      ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal) ∂du ∂scaleMeasure

@[reducible] def unitIdeleMeasurableSpace : MeasurableSpace Ẑˣ :=
  MeasurableSpace.comap (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)

theorem measurable_finUnitIdele :
    @Measurable Ẑˣ 𝔸 unitIdeleMeasurableSpace (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) :=
  comap_measurable _

end LanglandsTunnell.CubicInduction.AdelicEpstein

end


