-- Prove2me | Definitions.Def_Zeta23_Taper_Basic
-- name    : Zeta23_Taper_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:09:00.980033+00:00
-- url     : https://prove2.me/theorems/89aacaa0-bf6e-4506-9b15-f51cabd8e21f
-- title:
--   The taper $\varphi$ and its transforms ([eq:phidef]–[eq:psidef])
-- statement:
--   Definitions of the taper test family of the paper's [subsec:family], for generic parameters: a bump profile $\varrho:\mathbb R\to\mathbb R$ and reals $L$ (window length) and $w$ (taper width).
--
--   **Constants depending only on $\varrho$** [eq:phinorms]: `supDeriv` $=\lVert\varrho'\rVert_\infty$, `l1Deriv2` $=\lVert\varrho''\rVert_1$, and `cRho` $=c_\varrho:=4\lVert\varrho'\rVert_\infty+4\lVert\varrho''\rVert_1\ (\ge4)$.
--
--   **The taper and its integrals.** `phi` is the taper [eq:phidef]
--   $$\varphi(u):=\varrho\Bigl(\frac{L/2-|u|}{w}\Bigr),\qquad u\in\mathbb R,$$
--   a $C_c^3$ even plateau function with $0\le\varphi\le1$, support $[-L/2,L/2]$ and $\varphi=1$ on $[-L/2+w,\,L/2-w]$; `aConst` and `bConst` are the normalised moments $a:=L^{-1}\int\varphi^2$ and $b:=L^{-1}\int\varphi^4$ of [eq:abdef]; `C1` is $C_1:=\lVert\varphi''\rVert_1$ from [prop:tail].
--
--   **Transforms** [eq:PhigA]: `phiHat` is the Fourier transform in the paper's convention with complex argument, $\hat\varphi(z)=\int\varphi(u)\,e^{izu}\,du$, and `phiHatR` its restriction to the real line as a real number; `Phi` is $\Phi:=\widehat{(\varphi^2)}$ (with real restriction `PhiR`); `g` is the autocorrelation $g:=\varphi^2\star\varphi^2$ and `Aphi` is $A_\varphi:=\varphi\star\varphi$, where $(v\star v)(y):=\int v(u)\,v(u+y)\,du$.
--
--   **The majorant** [eq:psidef]: `psi` is $\psi(r):=\min\bigl(L,\ 2/|r|,\ c_\varrho/(wr^2)\bigr)$ for $r\in\mathbb R$. At $r=0$ the value is explicitly $L$ (the other two entries are $+\infty$ in the paper); this is made explicit because in Lean $2/0=0$.
--
--   **Role.** The bodies are literally those of `Zeta23/Defs.lean`, so that the consumer-facing bridges `P.phi T = Taper.phi P.ϱ (P.L T) P.w` etc. hold by `rfl` (`Zeta23/Taper.lean`). The sub-files `Taper/Norms`, `Strip`, `Decay`, `Fourier` develop [eq:phinorms]–[eq:abdef], [eq:hfbound], [eq:gbounds]/[eq:psiints] and the Fourier/Plancherel facts on these definitions; the taper enters both sides of the trace computation and the tail estimate.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Basic.lean, docstring tag [eq:phidef]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23




namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/

/-- `‖ϱ'‖_∞`. -/
noncomputable def supDeriv (ϱ : ℝ → ℝ) : ℝ := ⨆ x : ℝ, |deriv ϱ x|

/-- `‖ϱ''‖₁`. -/
noncomputable def l1Deriv2 (ϱ : ℝ → ℝ) : ℝ := ∫ x : ℝ, |deriv (deriv ϱ) x|

/-- [eq:phinorms]: "`c_ϱ := 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ (≥ 4)`".  Body literally equal to `Params.crho`. -/
noncomputable def cRho (ϱ : ℝ → ℝ) : ℝ :=
  4 * (⨆ x : ℝ, |deriv ϱ x|) + 4 * ∫ x : ℝ, |deriv (deriv ϱ) x|



/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)

/-- [eq:phidef]: "`φ(u) := ϱ((L/2 − |u|)/w)`, `u ∈ ℝ`". -/
noncomputable def phi (u : ℝ) : ℝ := ϱ ((L / 2 - |u|) / w)

/-- [eq:abdef]: "`a := L⁻¹ ∫ φ²`". -/
noncomputable def aConst : ℝ := L⁻¹ * ∫ u : ℝ, (phi ϱ L w u) ^ 2

/-- [eq:abdef]: "`b := L⁻¹ ∫ φ⁴`". -/
noncomputable def bConst : ℝ := L⁻¹ * ∫ u : ℝ, (phi ϱ L w u) ^ 4

/-- `φ̂(z) = h_φ(z) = ∫ φ(u) e^{izu} du` (paper convention, complex argument). -/
noncomputable def phiHat (z : ℂ) : ℂ := paperFT (fun u => (phi ϱ L w u : ℂ)) z

/-- `φ̂` on the real line as a real number. -/
noncomputable def phiHatR (r : ℝ) : ℝ := (phiHat ϱ L w (r : ℂ)).re

/-- [eq:PhigA]: "`Φ := (φ²)^`" (complex argument). -/
noncomputable def Phi (z : ℂ) : ℂ := paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) z

/-- `Φ` on the real line as a real number. -/
noncomputable def PhiR (r : ℝ) : ℝ := (Phi ϱ L w (r : ℂ)).re

/-- [eq:PhigA]: "`g := φ² ⋆ φ²`", `(v ⋆ v)(y) := ∫ v(u) v(u+y) du`. -/
noncomputable def g (y : ℝ) : ℝ := Params.autocorr (fun u => (phi ϱ L w u) ^ 2) y

/-- [eq:PhigA]: "`A_φ := φ ⋆ φ`". -/
noncomputable def Aphi (y : ℝ) : ℝ := Params.autocorr (phi ϱ L w) y

/-- [eq:psidef]: "`ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))` (`r ∈ ℝ`)".  At `r = 0` the paper's
value is `L` (the other two entries are `+∞`); this is made explicit because Lean's
`2 / 0 = 0`. -/
noncomputable def psi (r : ℝ) : ℝ :=
  if r = 0 then L else min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))

/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}












end Basic


/-- `C₁ := ‖φ''‖₁` [prop:tail]. -/
noncomputable def C1 (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ := ∫ u, |deriv (deriv (phi ϱ L w)) u|

end Taper

end Zeta23


