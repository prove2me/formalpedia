-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_Basic
-- name    : Zeta23_PrimeSideA_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:15:01.765971+00:00
-- url     : https://prove2.me/theorems/d098dfce-cf45-46c6-bf3d-cd21a97f113d
-- title:
--   Taper hypothesis packages (`LocalHyps`) and the majorant $\psi$ for the prime side
-- statement:
--   This bundle sets up the hypothesis layer of the prime-side computation (paper §5): all §5 results are proved for abstract taper data subject to a short, explicitly listed set of facts, later discharged for the concrete taper.
--
--   The members: `PrimeSide.psiA` is the majorant $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ of [eq:psidef] (with a guard value at $r = 0$), which dominates both $\hat\varphi$ and $\Phi$. `PrimeSide.LocalHyps` is the structure collecting the facts about the test family at parameters $p$ used in §5 — [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT], the Poisson identity [lem:poisson], the $\Pi_X$ facts, the parameter regime [eq:wrange] — each field tagged with its paper label, where $c_\varrho = 4\|\varrho'\|_\infty + 4\|\varrho''\|_1 \ge 4$ is the profile constant of [eq:phinorms]. These facts are *proved* elsewhere in the repository (Taper.lean, Poisson.lean, PiFacts.lean), not assumed. `LocalHypsCore` is the core sub-package, and `LocalHypsCoreW` is a purely additive variant dropping the bandwidth cap $\lambda \le 1$ (for the family regime $\lambda \in (1,2)$, used only by family-average statements). Finally, `EventuallyAt` (and the stronger `EventuallyAtCore`) formalizes the uniformity quantifier of §5: a property $P$ holds "for $T \ge T_0$, uniformly" if it holds for every parameter set $p$ at bandwidth ratio $\lambda$ with $T_0 \le p.T$ and every functional datum $F$ satisfying the local hypotheses.
--
--   Role: every §5 estimate ([prop:trace], [lem:ends], [prop:mumu], [prop:cross], [prop:PP]) is stated in the shape $\exists C,\ \mathtt{EventuallyAt}\ (|\mathrm{lhs} - \mathrm{main}| \le C \cdot \mathrm{err})$ over this hypothesis layer, and the bridge file instantiates `LocalHyps` for the concrete taper.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean, docstring tags [eq:psidef], [eq:phinorms]

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
import Definitions.Def_Zeta23_PrimeSideA_Defs

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/

/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²)) [eq:psidef], with the r = 0 guard
(= `Zeta23.Params.psi` / `Taper.psi'` by `rfl` under the bridge).  Majorant for both `φ̂` and `Φ`. -/
def psiA (cϱ : ℝ) (p : Setting) (r : ℝ) : ℝ :=
  if r = 0 then p.L else min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2)))

/-- The facts about the test family at parameters `p` used in §5, each tagged with
its paper label; `cϱ` is the profile constant `c_ϱ = 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ ≥ 4` of [eq:phinorms]
(= `Zeta23.Params.crho`).  These facts are supplied by Taper.lean / Poisson.lean and
PiFacts.lean: this structure is instantiated elsewhere in the repository (a theorem
`LocalHyps P.crho ⟨T, P.lam, P.w⟩ ⟨P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T⟩` for
valid `P` and large `T`), not assumed. -/
structure LocalHyps (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ ≤ 1` [Notation]. -/
  lam_pos : 0 < p.lam
  lam_le_one : p.lam ≤ 1
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- [eq:gbounds] `(L−2w−|y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L−|y|)₊`. -/
  g_lower : ∀ y, max (p.L - 2 * p.w - |y|) 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- [eq:abdef] `1 − 2w/L ≤ b ≤ a ≤ 1`. -/
  b_lower : 1 - 2 * p.w / p.L ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — via `PiX_bound` (holds for all `X ≥ 1`) and `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)

/-- "For `T ≥ T₀`, uniformly": `P p F` holds for every parameter set `p` at bandwidth ratio `lam`
with `T₀ ≤ p.T` and every functional datum `F` satisfying the local hypotheses. -/
def EventuallyAt (cϱ lam : ℝ) (P : Setting → LocalFun → Prop) : Prop :=
  ∃ T₀ : ℝ, ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHyps cϱ p F → P p F

/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}








end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}



end SupBound


/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}












/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/

structure LocalHypsCore (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ ≤ 1` [Notation]. -/
  lam_pos : 0 < p.lam
  lam_le_one : p.lam ≤ 1
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- window-generic remnant of [eq:gbounds]: `g ≥ 0` and `g ≤ A_φ ≤ (L−|y|)₊`
  (the flat-top plateau lower bound `(L−2w−|y|)₊ ≤ g` is NOT here — see §7.1). -/
  g_nonneg : ∀ y, 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- window-generic remnant of [eq:abdef]: `1/2 ≤ b ≤ a ≤ 1` (the flat-top `1 − 2w/L ≤ b`
  is NOT here; 1/2 suffices for every positivity/division use and holds for the
  Montgomery–Taylor window). -/
  b_ge_half : 1 / 2 ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — see `PiX_bound` (holds for all `X ≥ 1`) and `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)



/-- "uniformly for T ≥ T₀", Core-quantified: stronger than EventuallyAt
(fewer hypotheses on F). -/
def EventuallyAtCore (cϱ lam : ℝ) (P : Setting → LocalFun → Prop) : Prop :=
  ∃ T₀ : ℝ, ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F → P p F


/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/










/-- Window-generic taper facts without the bandwidth cap λ ≤ 1 — the family regime is
λ = L/l ∈ (1, 2) (family window L = log(qT/2π), so L > l).
This regime goes beyond the paper: §5's statements all assume λ ≤ 1; nothing Core-typed is
re-typed here — this is a purely additive split: fields = LocalHypsCore's minus lam_le_one, and
LocalHypsCore.toCoreW below.  Consumed only by the family-average statements. -/
structure LocalHypsCoreW (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ` [Notation] (no upper cap here). -/
  lam_pos : 0 < p.lam
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- window-generic remnant of [eq:gbounds]: `g ≥ 0` and `g ≤ A_φ ≤ (L−|y|)₊`
  (the flat-top plateau lower bound `(L−2w−|y|)₊ ≤ g` is NOT here — see §7.1). -/
  g_nonneg : ∀ y, 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- window-generic remnant of [eq:abdef]: `1/2 ≤ b ≤ a ≤ 1` (the flat-top `1 − 2w/L ≤ b`
  is NOT here; 1/2 suffices for every positivity/division use and holds for the
  Montgomery–Taylor window). -/
  b_ge_half : 1 / 2 ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — see `PiX_bound` (holds for all `X ≥ 1`) / `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)












end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}






















end TraceAnalytic

end PrimeSide
end Zeta23


