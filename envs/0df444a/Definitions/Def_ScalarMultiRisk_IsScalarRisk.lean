-- Prove2me | Definitions.Def_ScalarMultiRisk_IsScalarRisk
-- name    : ScalarMultiRisk_IsScalarRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:56.53575+00:00
-- url     : https://prove2.me/theorems/1f2f00cf-4982-4bb2-b6a8-3e7eb6363e19
-- title:
--   Definition 3.1 — scalarized conditional convex risk measure
-- statement:
--   Let $E$ be $\mathbb R^d$ with cash direction $e=e_1$, or $\mathbb R$ with $e=1$. A map $\rho_t:L^\infty(E)\to L^\infty_t(\mathbb R)$ is a **scalarized conditional convex risk measure** if for all $X,Y\in L^\infty(E)$ and $m\in L^\infty_t(\mathbb R)$:
--
--   1. (conditional cash invariance) $\rho_t(X+me)=\rho_t(X)-m$;
--   2. (monotonicity) $Y-X\in L^\infty(E_+)$ implies $\rho_t(X)\ge\rho_t(Y)$;
--   3. (conditional convexity) $\rho_t(\lambda X+(1-\lambda)Y)\le\lambda\rho_t(X)+(1-\lambda)\rho_t(Y)$ for every $\lambda\in L^\infty_t([0,1])$;
--   4. (finite at zero) $\rho_t(0)\in L^\infty_t(\mathbb R)$.
--
--   With $E=\mathbb R$ this is the paper's univariate scalar risk measure.
--
--   **Formalization Note** The map is on a.e.-classes in the paper, so it is required to respect a.e. equality. Finiteness at zero is part of the requirement that $\rho_t$ maps into $L^\infty_t(\mathbb R)$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.1, p.7

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **Scalarized conditional convex risk measure.** arXiv:1807.10694v5, Definition 3.1, p.7: a
map `ρ_t : L∞(E) → L∞_t(ℝ)` with, for all `X, Y ∈ L∞(E)`, `m ∈ L∞_t(ℝ)`:
conditional cash invariance `ρ_t(X + m e) = ρ_t(X) − m`; monotonicity
`Y − X ∈ L∞(E₊) ⇒ ρ_t(X) ≥ ρ_t(Y)`; conditional convexity
`ρ_t(λX + (1−λ)Y) ≤ λρ_t(X) + (1−λ)ρ_t(Y)` for `λ ∈ L∞_t([0,1])`; finite at zero.

**Formalization Note.** The definition is written for a general ordered normed space `E` with a
cash direction `e`: `E = Fin d → ℝ` with `e = e₁` is Definition 3.1, and `E = ℝ` with `e = 1` is
the paper's "univariate scalar risk measure" (Prop 4.9, p.22). The paper's map is on equivalence
classes, so `congr` is part of the definition. "Finite at zero" is the instance `X = 0` of
`maps`. -/
structure IsScalarRisk {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    (B : FilteredSpace Ω T) (t : Fin (T + 1)) (e : E) (r : (Ω → E) → Ω → ℝ) : Prop where
  /-- `ρ_t` maps `L∞(E)` into `L∞_t(ℝ)`. -/
  maps : ∀ X ∈ LinftyFull B (Fin.last T), r X ∈ LinftyFull B t
  /-- `ρ_t` is a map on a.e.-classes. -/
  congr : ∀ X ∈ LinftyFull B (Fin.last T), ∀ Y ∈ LinftyFull B (Fin.last T),
    X =ᵐ[B.P] Y → r X =ᵐ[B.P] r Y
  /-- Conditional cash invariance. -/
  cash : ∀ X ∈ LinftyFull B (Fin.last T), ∀ m ∈ LinftyFull B t,
    r (fun ω => X ω + m ω • e) =ᵐ[B.P] fun ω => r X ω - m ω
  /-- Monotonicity. -/
  mono : ∀ X ∈ LinftyFull B (Fin.last T), ∀ Y ∈ LinftyFull B (Fin.last T),
    (∀ᵐ ω ∂B.P, 0 ≤ Y ω - X ω) → r Y ≤ᵐ[B.P] r X
  /-- Conditional convexity. -/
  convex : ∀ X ∈ LinftyFull B (Fin.last T), ∀ Y ∈ LinftyFull B (Fin.last T),
    ∀ l ∈ Linfty B t (fun _ => Set.Icc (0 : ℝ) 1),
      r (fun ω => l ω • X ω + (1 - l ω) • Y ω) ≤ᵐ[B.P]
        fun ω => l ω * r X ω + (1 - l ω) * r Y ω

end ScalarMultiRisk


