-- Prove2me | Definitions.Def_Zeta23_PrimeSideB_PP
-- name    : Zeta23_PrimeSideB_PP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:20:48.168122+00:00
-- url     : https://prove2.me/theorems/c03a5a3c-95ac-48ea-bf2f-ef6d8c5dc348
-- title:
--   The main-term sum $\sum_{n \le X} \Lambda(n)^2/n \cdot g(\log n)$ of [prop:PP]
-- statement:
--   This bundle defines the arithmetic main-term sum of [prop:PP] (paper §5.4). For a real cutoff $X$ and a weight function $g : \mathbb{R} \to \mathbb{R}$ (the taper's ramp function), `PrimeSide.sumA2g` is
--   $$\sum_{n \le X} \frac{\Lambda(n)^2}{n}\, g(\log n),$$
--   formalized as a sum over `primeRange X` $= (0, \lfloor X \rfloor]$ — the same index set as the mollifier sum `Zeta23.PX` — with $\Lambda$ the von Mangoldt function (zero off prime powers). In the paper's notation this is $\sum_{n \le X} a_n^2\, g(y_n)$ with $a_n = \Lambda(n)/\sqrt{n}$ and $y_n = \log n$.
--
--   Role: [prop:PP], proved in this module, states $\mathcal{M}[P_X, P_X] = (T/\pi) \sum_{n \le X} \Lambda(n)^2/n\; g(\log n) + O(L^2 X)$, and the g-sandwich (from [eq:gbounds] and Chebyshev–Mertens [eq:cheb2]) bounds the sum between $(L - 2w)^3/6 - O(L^2)$ and $L^3/6 + O(L^2)$. Together these give the second form $\mathcal{M}[P_X, P_X] = (TL^3/6\pi)(1 + O(w/L)) + O(L^2 X)$, the $\mathcal{M}[P_X,P_X]$ input to the [thm:traces] assembly in `Zeta23/PrimeSideB.lean`, whose `sumL2g` data field is exactly `sumA2g`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean, docstring tag [prop:PP]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Prime side, part B/PP — paper §5 [prop:PP] (§5.4): the term 𝓜[P_X,P_X]

Consumed by `Zeta23/PrimeSideB.lean` ([thm:traces]) through the three results at the bottom of
this file:

* `prop_PP`        [prop:PP] first form (§5.4):
      𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X);
* `sum_a2g_lower`, `sum_a2g_upper`  (§5.4, the "Finally" step, from [eq:gbounds]+[eq:cheb2]):
      (L−2w)³/6 − C·L² ≤ Σ_{n≤X} Λ(n)²/n · g(log n) ≤ L³/6 + C·L²,
  which give the paper's second form  𝓜[P_X,P_X] = (TL³/6π)(1+O(w/L)) + O(L²X).

Everything is stated in the abstract prime-side layer (Zeta23/PrimeSideA/Defs.lean +
`LocalHyps`/`EventuallyAt` of Zeta23/PrimeSideA.lean): `p : Setting` = (T, λ, w), `F : LocalFun` =
the taper data (φ̂, Φ, A_φ, g, a, b) subject to `LocalHyps cϱ p F` (the facts [eq:psidef],
[eq:abdef], [eq:gbounds], [eq:Phi2FT], …, each a proof obligation of Zeta23/Taper.lean, not an
axiom).  `P_X` is `Zeta23.PX` [eq:Pdef] of Zeta23/Defs.lean and 𝓜[·,·] is
`Zeta23.PrimeSide.Mform` (§5.4).  Analytic inputs: H-cheb = `Zeta23.ChebyshevMertens` [lem:cheb]
and H-MV = `Zeta23.MVHilbert` [lem:MV] from Zeta23/Hypotheses.lean (fields of `PaperInputs`).

## Proof route (paper §5.4, reorganised for Lean; labels as in the paper)
1. Bilinearity:  𝓜[P_X,P_X] = π⁻² Σ_{n,m≤X} a_n a_m 𝓜[cos(·y_n), cos(·y_m)],  a_n = Λ(n)/√n, y_n = log n.
2. Shear `(τ,τ') ↦ (x,τ') := (τ−τ',τ')` (measure-preserving on ℝ²) + Fubini  (§5.4 "Substituting
   τ = τ'+x … τ' ranges over I∩(I−x) = [T+x⁻, 2T−x⁺]"):
      𝓜[u,v] = ∫_{|x|≤T} Φ(x)² ∫_{max(T,T−x)}^{min(2T,2T−x)} u(τ'+x) v(τ') dτ' dx.
3. cos A cos B = ½cos(A−B) + ½cos(A+B): inner integral = ½J(xy_n, y_n−y_m) + ½J(xy_n, y_n+y_m),
   J(c,θ) := ∫_α^β cos(c+θτ')dτ' = (β−α)cos c (θ=0), = [sin(c+θβ)−sin(c+θα)]/θ (θ≠0), |J| ≤ 2/|θ|.
4. 𝒟 (n=m, "−"):  ½∫_{|x|≤T}Φ²(T−|x|)cos(xy_n) = πT g(y_n) + O(∫Φ²|x|)   by [eq:Phi2FT];
   𝒪₂ (all n,m, "+"):  ≤ (∫Φ²)(Σa_n)²/(2π² log 2) ≪ XL                        by [eq:cheb1];
   𝒪₁ (n≠m, "−"):  an explicit combination of 8 sums Σ_{n≠m} x_n conj(z_m)/(y_n−y_m) with
   |x_n| = a_n, |z_m| ≤ a_m ∫Φ², each ≤ C_MV·(∫Φ²)·Σ a_n²/δ_n with δ_n = 1/(2n) [eq:deltan] ≪ L²X by H-MV
   and [eq:cheb1] (Σ Λ(n)² ≪ X log X).
Constants: the paper's O(L²X) constant (and the λ=1 "18/L" sharpness) is not load-bearing;
we prove ∃ C.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

variable {cϱ lam : ℝ}

/-! ## The main-term sum  Σ_{n≤X} a_n² g(y_n) = Σ_{n≤X} Λ(n)²/n · g(log n)   (§5.4) -/

/-- `Σ_{n ≤ X} Λ(n)²/n · g(log n)` — the sum in the first form of [prop:PP] (§5.4), indexed like
`Zeta23.PX` over `primeRange X = Finset.Ioc 0 ⌊X⌋₊` (Λ = 0 off prime powers).  Note `a_n² = Λ(n)²/n`
(§5.4). -/
def sumA2g (X : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n * g (Real.log n)


/-! ## Elementary facts about the index range and `X = e^L` -/

section Basics
variable {p : Setting} {F : LocalFun}





end Basics

/-! ## The g-sandwich  (§5.4)

"Finally, by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n),
  (L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6+O(L²)". -/

section Sandwich
variable {p : Setting} {F : LocalFun}



end Sandwich

/-! ## Assembly of [prop:PP]  (§5.4) -/

section Assembly
variable {Φ : ℝ → ℝ} {T : ℝ}





end Assembly

/-! ## Results consumed by PrimeSideB.lean -/

section Results




end Results


end PrimeSide
end Zeta23


