-- Prove2me | Definitions.Def_Zeta23_Tail
-- name    : Zeta23_Tail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:11:41.003772+00:00
-- url     : https://prove2.me/theorems/6046a5c4-6a73-463e-8be1-3a1a1c799bb9
-- title:
--   Assembly of the tail bound ([prop:tail])
-- statement:
--   Definitions for the assembly of Proposition [prop:tail] (the paper's §4.2, "The tail") for the concrete objects of `Defs.lean`. Here $E:=G-A$ is the contribution to the zero-side matrix of the zeros with ordinate $\gamma\notin I':=(T-D_0,\,2T+D_0]$, $D_0:=T^{1/2}$ [eq:D0] (including all zeros with $\gamma\le0$), and $\tilde E:=E/L$, $\hat E:=E/(aL^2)$ [eq:hatunits]. The proposition asserts $\lVert\tilde E\rVert\le\theta_0$ and $\lVert\hat E\rVert_1\le\theta_0/(aL)$.
--
--   **Members.**
--   - `theta0` — the bound $\theta_0:=4A_0C_1^2X^{1/2}\log(4T)/D_0^2$ of [prop:tail], written with $K:=e^{L/4}C_1=X^{1/4}C_1$ (so $K^2=C_1^2X^{1/2}$) and $D_0^2=T$:
--   $$\theta_0(A_0,K,T)=\frac{4\,A_0\,K^2\log(4T)}{T}.$$
--   - `uvec` — the evaluation vectors $u_\rho:=(\hat\varphi(\gamma_\rho-\tau_k))_{0\le k<d}\in\mathbb C^d$ from the proof of [prop:tail] (also [prop:block]'s $u_\rho$).
--   - `TailHyp` — the standing hypotheses of [prop:tail] bundled to keep signatures short (the local count from `PaperInputs.RvM.local`, the decay bound [eq:hfbound] for $\hat\varphi$, and Hermitian-ness of $\tilde E$, $\hat E$ from the $\rho\mapsto1-\bar\rho$ symmetry), with the derived quantities `TailHyp.K` ($K:=e^{L/4}C_1$) and `TailHyp.sA` (the zeros of the window $\mathcal Z(I')$ as a `Finset` of the carrier subtype).
--   - `finite_notTail` — the set of zeros in the window $I'$ (the complement of the tail) is finite.
--
--   **Role.** Together with the sub-files `Tail/RankOne.lean` (rank-one eigenvalue bounds), `Tail/Grid.lean` ($\sum_k|\gamma-\tau_k|^{-4}\le L\,\mathrm{dist}(\gamma,I)^{-3}$) and `Tail/Count.lean` (the tail zero-count sums), this module delivers the two conclusions in exactly the shapes consumed by `Zeta23/Assembly.lean` (`Assembly.TailInputs`): $\forall i,\ |\lambda_i(\tilde E)|\le\theta_0$ and $\mathrm{traceNorm}\,\hat E\le\theta_0/(aL)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean, docstring tag [prop:tail]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/

/-- θ₀ := 4 A₀ C₁² X^{1/2} log(4T)/D₀²  [prop:tail], written with K := e^{L/4}·C₁ = X^{1/4}C₁
(so K² = C₁² X^{1/2}) and D₀² = T:  theta0 A₀ K T = 4·A₀·K²·log(4T)/T. -/
def theta0 (A₀ K T : ℝ) : ℝ := 4 * A₀ * K ^ 2 * Real.log (4 * T) / T




/-! ### The local count from PaperInputs.RvM.local -/


/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d} ∈ ℂ^d (proof of [prop:tail]; also prop:block's u_ρ). -/
def uvec (ρ : ℂ) : Fin (P.d T) → ℂ := fun k => P.phiHat T (gammaOf ρ - P.tau T k)



variable {P T}




variable {Z}



end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

/-- Standing hypotheses of [prop:tail], bundled to keep signatures short. -/
structure TailHyp (Z : ZeroConfig) (P : Params) (T A₀ C₁ : ℝ) : Prop where
  hT : T₀ ≤ T
  hL : 2 ≤ P.L T
  hA₀ : 1 ≤ A₀
  /-- PaperInputs.RvM.local (two-sided unit-window local count). -/
  hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
  hC₁ : 0 ≤ C₁
  /-- [eq:hfbound] for f = φ, shape of Zeta23.Params.norm_phiHat_sub_I_mul_le with C₁ := P.C1 T. -/
  hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2

/-- The set of zeros in the window I' (complement of the tail) is finite (as a subset of the
carrier subtype). -/
lemma finite_notTail (Z : ZeroConfig) (T : ℝ) :
    {ρ : Z.carrier | ¬ InTail T (ρ : ℂ).im}.Finite := by
  have hfin : (Z.ZIprime T).Finite := Z.finite_window _ _
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  simp only [Set.mem_setOf_eq, InTail, not_or, not_le, not_lt] at hρ
  exact ⟨ρ.2, hρ.1, hρ.2⟩

namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H


/-- sA := the zeros of 𝒵(I') as a Finset of the carrier subtype. -/
def sA (_ : TailHyp Z P T A₀ C₁) : Finset Z.carrier := (finite_notTail Z T).toFinset


/-- K := e^{L/4} C₁. -/
def K (_ : TailHyp Z P T A₀ C₁) : ℝ := Real.exp (P.L T / 4) * C₁









end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian




variable {P : Params} {T : ℝ}


variable {Z : ZeroConfig} {A₀ C₁ : ℝ}





end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}







end Export

end Tail
end Zeta23


