-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_EndsCore
-- name    : Zeta23_PrimeSideA_EndsCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:15:53.397664+00:00
-- url     : https://prove2.me/theorems/a0c39eef-500e-400f-b2e5-a522a83aec58
-- title:
--   Kernels $K$, $K_\infty$, $\rho$ and the error terms $\mathcal{E}_1$, $\mathcal{E}_2$ for [lem:ends]
-- statement:
--   This bundle sets up the objects of [lem:ends] ("end effects", paper §5.3), the estimate $\operatorname{tr}\tilde G^2 = \mathcal{M} + O(L\, l \log l\, (l^2 + X))$ feeding [thm:traces].
--
--   **Kernels.** `Kfun` is the finite Gabor kernel $K(\tau, \tau') := \sum_{0 \le k < d} \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau' - \tau_k)$ [eq:Kdef]; `Kinf` is its full-lattice value $K_\infty(\tau, \tau') = L\, \Phi(\tau - \tau')$ (the value of $\sum_{k \in \mathbb{Z}}$, by [lem:poisson]); `rho` is the tail $\rho(\tau) := aL^2 - \sum_{k<d} \hat\varphi(\tau - \tau_k)^2$, which equals $\sum_{k \notin [0,d)} \hat\varphi(\tau - \tau_k)^2$ by the Poisson diagonal.
--
--   **Decomposition.** With $I = [T, 2T]$ and `sqI` $= I \times I$, the difference $\sum_{k,l} G_{kl}^2 - L^2 \mathcal{M}$ splits into
--   $$\mathcal{E}_1 := \iint_{I \times I} (K^2 - K_\infty^2)\, \nu\, \nu', \qquad \mathcal{E}_2 := \iint_{(I \times I)^c} K^2\, \nu\, \nu',$$
--   spelled `calE1`, `calE2`, with integrands `trG2integrand` ($K^2 \nu \nu'$) and `KinfIntegrand` ($K_\infty^2 \nu \nu' = L^2 \Phi(\tau-\tau')^2 \nu\nu'$), and the one-variable pieces `gkl` ($g_{kl}(\tau) := \hat\varphi(\tau - \tau_k)\hat\varphi(\tau - \tau_l)\nu_X(\tau)$, so $G_{kl} = \int g_{kl}$).
--
--   **Density bound.** `Bconst` is $B := l + 4\sqrt{X}$ [eq:Bdef], and `NuBound` packages the pointwise bound on the density: $|\nu_X(\tau)| \le B + \log^{+}(|\tau|/4T)$ on $\mathbb{R}$ and $|\nu_X(\tau)| \le B$ for $|\tau| \le 4T$, valid for $T \ge T_0$ (discharged by `nuX_abs_le` from H-$\Gamma$ + H-cheb). `GentryNu` and `MtotalNu` are the Gram entry and $\mathcal{M}$ for an abstract density $\nu$, agreeing definitionally with `GentryA`/`MtotalA` at $\nu = \nu_X$.
--
--   Role: the bounds $|\mathcal{E}_1| \ll L^3 B^2 l$ (EndsE1) and the $\mathcal{E}_2$ bound (EndsE2, via the one-dimensional estimates of EndsNu) assemble in `Ends.lean` into [lem:ends], one of the five §5 inputs to [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean, docstring tags [eq:Kdef], [eq:Bdef]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/

/-- [eq:Bdef] pointwise bound on ν_X (Zeta23/PiFacts.lean `nuX_abs_le`):
"`|ν_X(τ)| ≤ B + log⁺(|τ|/4T)` (τ ∈ ℝ), `|ν_X(τ)| ≤ B` (|τ| ≤ 4T), `B := l + 4√X`" for T ≥ T₀. -/
def NuBound (p : Setting) (B : ℝ) (ν : ℝ → ℝ) : Prop :=
  ∀ τ : ℝ, |ν τ| ≤ B + max (Real.log (|τ| / (4 * p.T))) 0

/-- `B := l + 4√X` [eq:Bdef]. -/
def Bconst (p : Setting) : ℝ := p.l + 4 * Real.sqrt p.X

variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/

/-- `G_{kl}` for an abstract density ν (`GentryA p F k l = GentryNu (Zeta23.nuX p.X) p F k l`, rfl). -/
def GentryNu (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) (k l : ℤ) : ℝ :=
  ∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * ν τ

/-- `𝓜` for an abstract density (`MtotalA p F = MtotalNu (Zeta23.nuX p.X) p F`, rfl). -/
def MtotalNu (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) : ℝ := Mform F.Phi p.T ν ν



/-! ## [eq:Kdef] -/

/-- `K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k) φ̂(τ'−τ_k)` [eq:Kdef]. -/
def Kfun (τ τ' : ℝ) : ℝ := ∑ k : Fin p.d, F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)

/-- `K_∞(τ,τ') = L Φ(τ−τ')` (the value of `Σ_{k∈ℤ}`, [lem:poisson]). -/
def Kinf (τ τ' : ℝ) : ℝ := p.L * F.Phi (τ - τ')

/-- `ρ(τ) := aL² − Σ_{k<d} φ̂(τ−τ_k)²`  (`= Σ_{k∉[0,d)} φ̂(τ−τ_k)²` by the Poisson diagonal). -/
def rho (τ : ℝ) : ℝ := F.a * p.L ^ 2 - ∑ k : Fin p.d, F.phiHat (τ - p.tau k) ^ 2

/-! All double integrals below are integrals over `ℝ × ℝ` w.r.t. `volume` (= `volume.prod
volume`), restricted to `I ×ˢ I` or its complement where indicated — the same spelling as
`Mform` in Zeta23/PrimeSideA/Defs.lean. -/

/-- the square `I × I`, `I = [T,2T]`. -/
def sqI : Set (ℝ × ℝ) := p.I ×ˢ p.I

/-- the integrand of [eq:trG2int]: `K(τ,τ')² ν(τ) ν(τ')`. -/
def trG2integrand (q : ℝ × ℝ) : ℝ := Kfun p F q.1 q.2 ^ 2 * ν q.1 * ν q.2

/-- the integrand `K_∞(τ,τ')² ν(τ) ν(τ')` (`= L² Φ(τ−τ')² νν'`). -/
def KinfIntegrand (q : ℝ × ℝ) : ℝ := Kinf p F q.1 q.2 ^ 2 * ν q.1 * ν q.2

/-- `𝓔₁ := ∬_{I×I} (K² − K_∞²) ν ν'` (§5.3). -/
def calE1 : ℝ := ∫ q in sqI p, (trG2integrand p F ν q - KinfIntegrand p F ν q)

/-- `𝓔₂ := ∬_{(I×I)ᶜ} K² ν ν'` (§5.3). -/
def calE2 : ℝ := ∫ q in (sqI p)ᶜ, trG2integrand p F ν q

variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/








/-- the one-variable pieces `g_{kl}(τ) := φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ)` of `G_{kl} = ∫ g_{kl}`. -/
def gkl (p : Setting) (F : LocalFun) (ν : ℝ → ℝ) (k l : ℤ) (τ : ℝ) : ℝ :=
  F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * ν τ










end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}























end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}









/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/





end Kbounds


end PrimeSide
end Zeta23


