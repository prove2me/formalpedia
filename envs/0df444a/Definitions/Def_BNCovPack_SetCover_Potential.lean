-- Prove2me | Definitions.Def_BNCovPack_SetCover_Potential
-- name    : BNCovPack_SetCover_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:36:58.648982+00:00
-- url     : https://prove2.me/theorems/433c21c5-33f0-4793-bb87-8ebd7b0f4a65
-- title:
--   The potential $\Phi=\Phi_1+\Phi_2$ and the parameter $\alpha=\max\{1,\ln(rn/OPT)\}$ of Section 5.1
-- statement:
--   This file defines the potential function used in Section 5.1 of Buchbinder and Naor (2009) to round the fractional set cover online.
--
--   Let $X$ be the ground set with $n=|X|$ elements, $\mathcal S$ the family of sets, $w:\mathcal S\to\mathbb R$ the current fractional weights, $\mathcal C\subseteq\mathcal S$ the current family of chosen sets, $C$ the set of elements covered by members of $\mathcal C$, $\alpha$ a real parameter and $OPT$ a natural number (the known optimum value).
--
--   1. For each element $e$,
--   $$f(e)=\min\Big\{1,\ \exp\Big(-\alpha+\alpha\sum_{s\ni e}w(s)\Big)\Big\}.$$
--   2. $\displaystyle\Phi_1=1-\prod_{e\in X,\ e\notin C}\big(1-f(e)\big)$, the product running over **all** elements of the ground set not covered by $\mathcal C$, whether or not they have arrived.
--   3. $\displaystyle\Phi_2=\exp\Big(\sum_{s\in\mathcal S}\big((\ln 2)\,\chi_{\mathcal C}(s)-\alpha w(s)\big)-OPT\Big)$, where $\chi_{\mathcal C}(s)=1$ if $s\in\mathcal C$ and $0$ otherwise.
--   4. $\Phi=\Phi_1+\Phi_2$.
--   5. The constants of the algorithm: $r=e\ln\big(e/(e-1)\big)$ and
--   $$\alpha=\max\Big\{1,\ \ln\frac{rn}{OPT}\Big\}.$$
--
--   The first term forces every arriving element to be covered; the second bounds the number of chosen sets. The potential is the online version of a pessimistic estimator for randomized rounding.
--
--   **Formalization Note** $\Phi$ is defined for an arbitrary real $\alpha$ (Lemma 5.1 (ii) holds for every $\alpha\ge 0$); the algorithm uses `alphaParam n OPT` $=\max\{1,\ln(rn/OPT)\}$ with $n$ = `Fintype.card E`. The page prints $r$ as "$e\ln(e/e-1)$"; the intended value is $e\ln(e/(e-1))$, the constant for which $1-x\ge e^{-rx}$ on $[0,1/e]$. Logarithms are natural (`Real.log`). For $OPT=0$ Lean's division gives $\ln 0=0$; the theorems assume $OPT\ge 1$.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 12, Section 5.1 (f(e_i), Φ = Φ1 + Φ2, χ_C); p. 13, proof of Lemma 5.1 (α = max{1, ln(rn/OPT)}, r = e ln(e/(e−1)))

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- The constant `r = e · ln(e/(e − 1))` of §5.1 (p. 13). -/
noncomputable def rConst : ℝ := Real.exp 1 * Real.log (Real.exp 1 / (Real.exp 1 - 1))

/-- The parameter `α = max {1, ln(r n / OPT)}` (p. 13), where `n` is the number of elements of
the ground set and `OPT` the (known) optimum value. -/
noncomputable def alphaParam (n OPT : ℕ) : ℝ :=
  max 1 (Real.log (rConst * (n : ℝ) / (OPT : ℝ)))

/-- `f(e) = min {1, exp(−α + α ∑_{s ∋ e} w(s))}` (p. 12). -/
noncomputable def fval {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (e : E) : ℝ :=
  min 1 (Real.exp (-α + α * elementWeight inst w e))

open Classical in
/-- `Φ₁ = 1 − ∏_{e ∉ C̄} (1 − f(e))` (p. 12): the product ranges over all elements of the ground
set that are not covered by the current family `C`, whether or not they have arrived. -/
noncomputable def potential1 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) : ℝ :=
  1 - ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e)

/-- `Φ₂ = exp(∑_{s ∈ 𝒮} ((ln 2)·χ_C(s) − α w(s)) − OPT)` (p. 12), with `χ_C(s) = 1` if `s ∈ C`
and `0` otherwise. -/
noncomputable def potential2 {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) : ℝ :=
  Real.exp (∑ s, (Real.log 2 * (if s ∈ C then (1 : ℝ) else 0) - α * w s) - (OPT : ℝ))

/-- The potential function `Φ = Φ₁ + Φ₂` of §5.1 (p. 12). -/
noncomputable def potential {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) : ℝ :=
  potential1 inst α w C + potential2 α OPT w C

end BNCovPack.SetCover


