-- Prove2me | Definitions.Def_ModularCurve_UVCrossingChart
-- name    : ModularCurve_UVCrossingChart
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/1714b7a8-7548-53de-8748-c8a792bdad7b
-- title:
--   Symmetric coordinate and chart map for the crossing model
-- statement:
--   Throughout, $W$ is a commutative ring and $\pi \in W$; the crossing model is the quotient $\mathrm{UVCrossingModel}\ W\ \pi = W[[X_0,X_1]]/(X_0X_1 - \pi)$, with $\mathrm{mk}\ \pi$ the quotient ring homomorphism from `MvPowerSeries (Fin 2) W`.
--
--   The module introduces two things. First, `sAmbient W` is the two-variable power series $X_0 + X_1$ in `MvPowerSeries (Fin 2) W`, the symmetric coordinate at the level of the ambient ring, before passing to the quotient; `sAmbient_def` records this description, `constantCoeff_sAmbient` that its constant coefficient is $0$, and `hasSubst_sAmbient` that it therefore satisfies Mathlib's substitutability condition `PowerSeries.HasSubst`, so that one-variable power series may be substituted into it.
--
--   Second, `chartHom π` is the ring homomorphism
--   $$W[[T]] \longrightarrow W[[X_0,X_1]]/(X_0X_1-\pi), \qquad f \longmapsto f(X_0+X_1) \bmod (X_0X_1-\pi),$$
--   defined as the substitution of $X_0+X_1$ for the variable of a one-variable power series, followed by the quotient map $\mathrm{mk}\ \pi$. It is thus a map of rings (not packaged here as a $W$-algebra map), and `chartHom_apply` states the unfolding $\mathrm{chartHom}\ \pi\ f = \mathrm{mk}\ \pi\,(\mathrm{subst}\ (X_0+X_1)\ f)$. In the intended reading, the image of the variable $T$ is the class of $X_0+X_1$, i.e. the element $S\ \pi = U\ \pi + V\ \pi$ of the crossing model, which is invariant under the branch-exchange involution $\mathrm{crossingSwap}\ \pi$ interchanging the two variables. No injectivity, surjectivity onto invariants, or completeness hypothesis is asserted at this stage; only the homomorphism and its defining formula are provided.
--
--   **Relation to Mathlib.** The substitution apparatus (`PowerSeries.HasSubst`, `PowerSeries.substAlgHom`, `PowerSeries.subst`) and the rings `PowerSeries`, `MvPowerSeries` are Mathlib's; the crossing model $W[[X_0,X_1]]/(X_0X_1-\pi)$ and the chart map into it are the project's own.
--
--   **Where it is used.** The crossing model is the local model, at a supersingular point, of a modular curve with $\Gamma_0(p)$-level structure, and the symmetric coordinate $X_0+X_1$ is the coordinate on the quotient by the Atkin–Lehner involution exchanging the two branches. The chart homomorphism defined here is the map used to express that quotient's completed local ring as a power series ring in one variable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_UVCrossingChart.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

namespace UVCrossingModel

section AmbientChart

variable (W : Type u) [CommRing W]

def sAmbient : MvPowerSeries (Fin 2) W :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1

theorem sAmbient_def :
    sAmbient W = MvPowerSeries.X 0 + MvPowerSeries.X 1 :=
  rfl

theorem constantCoeff_sAmbient : MvPowerSeries.constantCoeff (sAmbient W) = 0 := by
  rw [sAmbient, map_add, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
    add_zero]

theorem hasSubst_sAmbient : PowerSeries.HasSubst (sAmbient W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_sAmbient W)

end AmbientChart

variable {W : Type u} [CommRing W]

def chartHom (π : W) : PowerSeries W →+* UVCrossingModel W π :=
  (mk π).comp (PowerSeries.substAlgHom (hasSubst_sAmbient W)).toRingHom

theorem chartHom_apply (π : W) (f : PowerSeries W) :
    chartHom π f = mk π (PowerSeries.subst (sAmbient W) f) := by
  show mk π ((PowerSeries.substAlgHom (hasSubst_sAmbient W)) f) = _
  rw [PowerSeries.coe_substAlgHom]

end UVCrossingModel

end

end ModularCurve


