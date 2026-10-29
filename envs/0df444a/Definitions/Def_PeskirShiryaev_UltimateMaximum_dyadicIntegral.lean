-- Prove2me | Definitions.Def_PeskirShiryaev_UltimateMaximum_dyadicIntegral
-- name    : PeskirShiryaev_UltimateMaximum_dyadicIntegral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:33.5927+00:00
-- url     : https://prove2.me/theorems/23086bc3-a2a3-4ffd-b723-210fffb1360f
-- title:
--   Unit-interval stochastic sums and their $L^2$ limit
-- statement:
--   For processes $B,H$ indexed by nonnegative time, use the left-endpoint sums
--   $$I_n(H,B)=\sum_{k=0}^{2^n-1}H_{k/2^n}(B_{(k+1)/2^n}-B_{k/2^n}).$$
--   The relation $\operatorname{HasUnitDyadicIntegral}(P,B,H,X)$ means that $X$ and each $I_n(H,B)$ belong to $L^2(P)$ and
--   $$\|I_n(H,B)-X\|_{L^2(P)}\longrightarrow0.$$
--   This gives a concrete, independent meaning to the unit-interval stochastic integral in the maximum representation: the theorem proves that its centered maximum is this limit.
--
--   **Formalization Note** This relation is used for the specified bounded Brownian integrand, continuous before time $1$. It does not purport to define an integral for every predictable process by left sampling. Measurability and square integrability are explicit in $L^2$ membership, and the norm is extended nonnegative real. No existence, Brownian law, or adaptedness is assumed by this definition itself.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 442 (PDF p. 458), Eqs. (30.1.7)–(30.1.8), concrete left-step realization of the stated Itô integral

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace PeskirShiryaev.UltimateMaximum

noncomputable def dyadicSum {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), H ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) ω *
    (B (((k : ℝ≥0) + 1) / (2 : ℝ≥0) ^ n) ω - B ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) ω)

/-- Unit-horizon left-step L² integral relation. Its use below is for the explicit
bounded integrand, continuous on [0,1); it is not a definition for arbitrary predictable H. -/
def HasUnitDyadicIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B H : ℝ≥0 → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  MemLp X 2 P ∧ (∀ n, MemLp (dyadicSum B H n) 2 P) ∧
    Tendsto (fun n => eLpNorm (fun ω => dyadicSum B H n ω - X ω) 2 P)
      atTop (𝓝 0)

end PeskirShiryaev.UltimateMaximum


