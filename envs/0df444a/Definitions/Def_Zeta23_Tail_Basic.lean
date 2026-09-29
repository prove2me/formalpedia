-- Prove2me | Definitions.Def_Zeta23_Tail_Basic
-- name    : Zeta23_Tail_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:10:58.446497+00:00
-- url     : https://prove2.me/theorems/f5fa9cb4-a3e5-4b10-8fd1-2af8da6efd97
-- title:
--   Basic definitions for the tail estimate ([prop:tail])
-- statement:
--   Shared elementary definitions for Proposition [prop:tail] (the paper's §4.2).
--
--   **Members.**
--   - `distI T γ` — the distance $D:=\mathrm{dist}(\gamma,I)$ from an ordinate $\gamma$ to the interval $I=[T,2T]$: it equals $0$ for $\gamma\in I$, $T-\gamma$ for $\gamma<T$, and $\gamma-2T$ for $\gamma>2T$.
--   - `InTail T γ` — the tail predicate: $\gamma\notin I':=(T-D_0,\,2T+D_0]$ with $D_0:=T^{1/2}$ [eq:D0]. The tail is the part of the zero-side sum [eq:Gdef] whose ordinate lies outside the enlarged window $I'$ — this includes **all** zeros with $\gamma\le0$.
--   - `T₀` — an explicit absolute threshold standing in for "$T\ge T_0$" in [prop:tail], chosen $\ge256\ge16\pi^2$ (using only $\pi\le4$) so that $\log(4T)\le2\log(T/2\pi)=2l$; any larger absolute constant would do.
--   - `LocalCount` — the local zero-count hypothesis of [prop:tail]: "let $A_0\ge1$ be an absolute constant with $N(t+1)-N(t)\le A_0\log(t+3)$ for all $t\ge0$" [Tit86, Thm 9.2], stated in the two-sided unit-window form
--   $$N(t,\,t+1] \;\le\; A_0\log(|t|+3)\qquad\text{for all real } t,$$
--   for an abstract family of ordinates $\gamma:\iota\to\mathbb R$ with multiplicities $m:\iota\to\mathbb N$, and for finite sub-families only, so that no summability is presupposed. The two-sided form covers the zeros with $\gamma\le0$ with no separate seam fact.
--
--   **Role.** These definitions are consumed by `Zeta23/Tail/Grid.lean`, `Tail/Count.lean` and the assembly `Zeta23/Tail.lean`, where `LocalCount` is instantiated from the zero configuration and `PaperInputs.RvM.local` (`LocalCount.ofWindowCount`); the resulting tail bounds $\lVert\tilde E\rVert\le\theta_0$, $\lVert\hat E\rVert_1\le\theta_0/(aL)$ feed the assembly of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Basic.lean, docstring tag [prop:tail]

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail

/-- Distance from γ to the interval I = [T, 2T] (paper: D := dist(γ, I) in the proof of
[prop:tail]); equals 0 for γ ∈ I, T − γ for γ < T, γ − 2T for γ > 2T. -/
def distI (T γ : ℝ) : ℝ := max 0 (max (T - γ) (γ - 2 * T))




/-- The tail predicate: ordinate γ ∉ I' := (T − D₀, 2T + D₀], D₀ := T^{1/2} [eq:D0].
(Paper: "split the sum [eq:Gdef] over distinct zeros according to whether the ordinate
γ = Re γ_ρ lies in I'"; E is the part with γ ∉ I' [eq:AE]. Note: this includes all
zeros with γ ≤ 0.) -/
def InTail (T γ : ℝ) : Prop := γ ≤ T - Real.sqrt T ∨ 2 * T + Real.sqrt T < γ



/-- Explicit absolute threshold standing in for "T ≥ T₀" in [prop:tail]. Chosen ≥ 256 ≥ 16π²
(using only π ≤ 4) so that log(4T) ≤ 2·log(T/2π) = 2l (used in the "so that
θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1}" clause); the zero-count estimate needs far less. Any larger
absolute constant would also do. -/
def T₀ : ℝ := 300


/-- Local zero-count hypothesis of [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such
that N(t+1) − N(t) ≤ A₀ log(t+3) for all t ≥ 0" [Tit86, Thm 9.2], for an abstract family of
ordinates γ : ι → ℝ with multiplicities m : ι → ℕ. We use the two-sided unit-window form
(all real t, bound A₀·log(|t|+3)) as in PaperInputs.RvM.local: it is
equally classical and covers the zeros with γ ≤ 0 — which are in the tail
(paper: "zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³",
silently using the γ ↦ −γ symmetry and ζ(σ) ≠ 0 for 0<σ<1) — with no separate seam fact.
Stated for finite sub-families so that no summability is presupposed; instantiated from
ZeroConfig + PaperInputs.RvM.local in Zeta23/Tail.lean (LocalCount.ofWindowCount). -/
structure LocalCount {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ) (A₀ : ℝ) : Prop where
  one_le : 1 ≤ A₀
  window : ∀ t : ℝ, ∀ s : Finset ι, (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
    (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (|t| + 3)


end Tail
end Zeta23


