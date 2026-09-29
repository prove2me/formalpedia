-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_Defs
-- name    : Zeta23_PrimeSideA_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:14:11.039846+00:00
-- url     : https://prove2.me/theorems/39c50694-d74c-4679-a772-272f9b6128db
-- title:
--   Abstract prime-side layer: parameters, taper data, Gram entries, traces, and the bilinear form $\mathcal{M}$
-- statement:
--   This bundle is the shared definitional layer of the prime side (paper §5): the abstract objects over which both PrimeSideA (trace estimates) and PrimeSideB ([prop:PP], [thm:traces]) are stated.
--
--   **Parameters.** `PrimeSide.Setting` packages the free scalars: height $T$, bandwidth ratio $\lambda$ ($0 < \lambda \le 1$), and ramp width $w$ ([eq:wrange]: $1 \le w \le L/8$). From these are derived $l := \log(T/2\pi)$, $\ell_1 := l + 2\log 2 - 1$ (note $\ell_1 \neq l$), $L := \lambda l$, $X := e^L = (T/2\pi)^\lambda$, the grid spacing $h := 2\pi/L$, the grid size $d := \lfloor T/h \rfloor = \lfloor LT/2\pi \rfloor$ [§2.2], the grid points $\tau_k := T + kh$ [eq:fk], and the window $I := [T, 2T]$; all agree definitionally with their `Zeta23.Params` counterparts under the bridge.
--
--   **Arithmetic and taper data.** `acoef` is $a_n := \Lambda(n)\, n^{-1/2}$ and `ycoef` is $y_n := \log n$ [§1.4]; `primeRange X` is the index set of prime powers $n \le X$, spelled as $(0, \lfloor X \rfloor]$ (with $\Lambda = 0$ off prime powers). `PrimeSide.LocalFun` is the abstract $T$-dependent taper datum $(\hat\varphi, \Phi, A_\varphi, g, a, b)$ [eq:PhigA, eq:abdef].
--
--   **Gram matrix and traces.** `GentryA` is the prime-side Gram entry $G_{kl} = \int_{\mathbb{R}} \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau - \tau_l)\, \nu_X(\tau)\, d\tau$ (second expression in [eq:Gdef], with the concrete density $\nu_X$ of [eq:nudef]); `trGtA` and `trGt2A` are $\operatorname{tr}\tilde G = L^{-1}\sum_{k<d} G_{kk}$ and $\operatorname{tr}\tilde G^2 = L^{-2}\sum_{k,l<d} G_{kl}^2$ [§5; eq:trG2int]. The **seam object** between the two prime-side halves is the symmetric bilinear form
--   $$\mathcal{M}[u_1, u_2] \;:=\; \iint_{I \times I} \Phi(\tau - \tau')^2\, u_1(\tau)\, u_2(\tau')\, d\tau\, d\tau' \qquad(\S 5.4),$$
--   spelled `Mform`, with $\mathcal{M} := \mathcal{M}[\nu_X, \nu_X]$ spelled `MtotalA` [lem:ends].
--
--   Role: every statement of §5 — [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross], [prop:PP], [thm:traces] — is expressed in these definitions; the bridge file identifies them with the concrete objects of `Zeta23/Defs.lean` by `rfl`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Defs.lean, docstring tags [eq:Gdef], [eq:fk], [eq:nudef]

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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side (paper §5 [sec:prime]) — ABSTRACT LAYER & SHARED DEFINITIONS
for PrimeSideA.lean / PrimeSideB.lean.

Bracketed labels and section numbers (§5.2, …) are as in the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".

SEAM between PrimeSideA.lean and PrimeSideB.lean:
  * The seam object is the symmetric bilinear form
        𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ',   I = [T,2T]          (§5.4)
    spelled here LITERALLY as `Mform Φ T u₁ u₂` below, and 𝓜 := 𝓜[ν_X,ν_X] = `MtotalA`.
  * PrimeSideA.lean : [prop:trace] tr G̃ = aL·N(T,2T)+O(L√X);
      [eq:trG2int]+[eq:Kbounds]+[lem:ends] tr G̃² = 𝓜 + O(L·l·log l·(l²+X));
      [eq:Msplit] (6-term expansion of 𝓜); [prop:mumu]; [prop:cross] (four bounds).
  * PrimeSideB.lean : [prop:PP] incl. 𝒟/𝒪₁/𝒪₂ and the g-sandwich via H-cheb [eq:cheb2];
      [thm:traces] = [eq:tr1],[eq:tr2],[eq:ratio] assembling A's five results + prop:PP + H-Γ [eq:muints] + H-RvM.
  * Error-term shape everywhere: ∃ C T₀ (allowed to depend on the profile constants and on λ),
      ∀ T ≥ T₀, |lhs − main| ≤ C·(error expression).  No filters / IsBigO until the final liminf wrapper.

ABSTRACT LAYER.  §5 is a computation about the functions φ̂, Φ, μ, Π_X, P_X on the REAL line
using only a short list of facts about them ([eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
[lem:poisson], [eq:mufacts], [eq:PiPfacts], [lem:cheb]).  We therefore prove §5 for ABSTRACT data
(`Setting` = the scalars T, λ, w;  `LocalFun` = the taper data φ̂, Φ, A_φ, g, a, b) subject
to exactly those facts (hypothesis structures in PrimeSideA.lean), and a thin bridge
(Zeta23/PrimeSideA/Bridge.lean) instantiates it with the
concrete objects of Zeta23/Defs.lean: `Zeta23.Params.phiHatR`, `.PhiR`, `.a`, `.b`, `.g`, `.Aphi`,
so that `trGtA` below becomes `Zeta23.Params.trGtilde` etc.  Names in this
layer carry a trailing `A` (abstract) where they would otherwise clash with Zeta23/Defs.lean.
The closed-form, ζ-free objects `Zeta23.l`, `Zeta23.ell1`, `Zeta23.mu` [eq:mudef], `Zeta23.PiX` [eq:Pidef],
`Zeta23.PX` [eq:Pdef], `Zeta23.nuX` [eq:nudef] are used DIRECTLY from Zeta23/Defs.lean, and the analytic
inputs H-Γ / H-cheb are Zeta23/Hypotheses.lean's `GammaFacts` / `ChebyshevMertens` verbatim, so the
statements here are literally about the official objects of Zeta23/Defs.lean; only the taper enters
abstractly.

The prime side is ζ-free: N(T,2T) enters only as an abstract real together
with [eq:RvM].

FOURIER CONVENTION: paper f̂(τ) := ∫ f(u) e^{iτu} du (§1.4) = `Zeta23.paperFT`.  On
this side we only meet φ̂ and Φ := (φ²)^ on ℝ, where they are real and even; we carry them as
functions ℝ → ℝ (= `phiHatR`, `PhiR` of Defs.lean).
-/


noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Scalars of the abstract setting  [§1 Notation, §1.4; eq:wrange; eq:fk] -/

/-- The free scalar parameters: height `T`, bandwidth ratio `λ` (`0<λ≤1`), ramp width `w`
([eq:wrange] `1 ≤ w ≤ L/8`; §6 takes `w = 1`).  (Zeta23/Defs.lean's `Params` = (ϱ, λ, w) with `T`
separate; the bridge is `fun (P : Zeta23.Params) T => ⟨T, P.lam, P.w⟩` and then `L, X, d, tau, h`
below agree with `P.L T, P.X T, P.d T, P.tau T, P.hgrid T` by `rfl`.) -/
structure Setting where
  T : ℝ
  lam : ℝ
  w : ℝ

namespace Setting
variable (p : Setting)

/-- `l := log(T/2π)` [Notation] — this IS `Zeta23.l p.T`. -/
abbrev l : ℝ := Zeta23.l p.T
/-- `ℓ₁ := l + 2 log 2 − 1` [Notation] — this IS `Zeta23.ell1 p.T`.  NOTE ℓ₁ ≠ l. -/
abbrev ell1 : ℝ := Zeta23.ell1 p.T
/-- `L := λ l` [Notation] (same body as `Zeta23.Params.L`). -/
def L : ℝ := p.lam * Zeta23.l p.T
/-- `X := e^L = (T/2π)^λ` [Notation] (same body as `Zeta23.Params.X`). -/
def X : ℝ := Real.exp p.L
/-- Grid spacing `h := 2π/L` [§2.2] (= `Zeta23.Params.hgrid`). -/
def h : ℝ := 2 * Real.pi / p.L
/-- `d := ⌊T/h⌋ = ⌊LT/2π⌋` [§2.2] (= `Zeta23.Params.d`). -/
def d : ℕ := ⌊p.L * p.T / (2 * Real.pi)⌋₊
/-- Grid points `τ_k := T + k h  (k ∈ ℤ)` [eq:fk] (= `Zeta23.Params.tau`). -/
def tau (k : ℤ) : ℝ := p.T + k * p.h
/-- The window `I := [T, 2T]` [Notation] (= `Zeta23.Iwin p.T`). -/
abbrev I : Set ℝ := Zeta23.Iwin p.T

end Setting

/-! ## The prime-power sum: notation of §5 for `Zeta23.PX` [eq:Pdef, §2.1] -/

/-- `a_n := Λ(n) n^{-1/2}` [Notation, §1.4]. -/
def acoef (n : ℕ) : ℝ := (Λ n : ℝ) / Real.sqrt n
/-- `y_n := log n` [Notation, §1.4]. -/
def ycoef (n : ℕ) : ℝ := Real.log n
/-- The index set "prime powers `n ≤ X`": all `0 < n ≤ ⌊X⌋` weighted by Λ (zero off prime powers);
spelled `Finset.Ioc 0 ⌊X⌋₊` as in Zeta23/Defs.lean's `PX` and Mathlib's `Chebyshev.psi`. -/
def primeRange (X : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊X⌋₊


/-! ## Abstract functional data

In the concrete instantiation `phiHat, Phi, Aphi, g, a, b` are Zeta23/Defs.lean's `P.phiHatR T`,
`P.PhiR T`, `P.Aphi T`, `P.g T`, `P.a T`, `P.b T` ([eq:phidef], [eq:abdef], [eq:PhigA]). -/

/-- The T-dependent taper data [eq:PhigA, eq:abdef] (abstract; see the bridge). -/
structure LocalFun where
  /-- `φ̂` restricted to ℝ (real-valued: φ is real and even) [§2.2]. -/
  phiHat : ℝ → ℝ
  /-- `Φ := (φ²)^` restricted to ℝ (real, even, entire) [eq:PhigA]. -/
  Phi : ℝ → ℝ
  /-- `A_φ := φ ⋆ φ`, `(v⋆v)(y) := ∫ v(u)v(u+y)du` [eq:PhigA]. -/
  Aphi : ℝ → ℝ
  /-- `g := φ² ⋆ φ²` [eq:PhigA]. -/
  g : ℝ → ℝ
  /-- `a := L⁻¹ ∫ φ²` [eq:abdef]. -/
  a : ℝ
  /-- `b := L⁻¹ ∫ φ⁴` [eq:abdef]. -/
  b : ℝ

variable (p : Setting) (F : LocalFun)

/-- The prime-side matrix entry (second expression in [eq:Gdef], §2.2):
`G_{kl} = ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ`, with `ν_X = Zeta23.nuX X` [eq:nudef] CONCRETE
(same shape as `Zeta23.Params.Gentry`, which is the case `F.phiHat := P.phiHatR T`). -/
def GentryA (k l : ℤ) : ℝ :=
  ∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * Zeta23.nuX p.X τ


/-- `tr G̃ = L⁻¹ Σ_{k<d} G_{kk}` [§5.2 "L tr G̃ = Σ_{k<d} G_kk"] (same shape as
`Zeta23.Params.trGtilde`: `L⁻¹ * Σ_{k : Fin d}`). -/
def trGtA : ℝ := (p.L)⁻¹ * ∑ k : Fin p.d, GentryA p F k k

/-- `tr G̃² = Σ_{k,l<d} G̃_{kl}² = L⁻² Σ_{k,l<d} G_{kl}²` [§5; eq:trG2int] (same shape as
`Zeta23.Params.trGtildeSq`). -/
def trGt2A : ℝ := (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryA p F k l ^ 2

/-! ## The seam: the bilinear form 𝓜[·,·]  [§5 "Evaluation of 𝓜", §5.4] -/

/-- `𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ'`, `I = [T,2T]` (§5.4).
This literal spelling is shared between PrimeSideA.lean and PrimeSideB.lean. -/
def Mform (Φ : ℝ → ℝ) (T : ℝ) (u₁ u₂ : ℝ → ℝ) : ℝ :=
  ∫ q in (Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T)), (Φ (q.1 - q.2)) ^ 2 * u₁ q.1 * u₂ q.2

/-- `𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'` [lem:ends statement, §5.3]. -/
def MtotalA : ℝ := Mform F.Phi p.T (Zeta23.nuX p.X) (Zeta23.nuX p.X)

end PrimeSide
end Zeta23


