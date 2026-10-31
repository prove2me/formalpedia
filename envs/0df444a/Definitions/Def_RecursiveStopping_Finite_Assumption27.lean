-- Prove2me | Definitions.Def_RecursiveStopping_Finite_Assumption27
-- name    : RecursiveStopping_Finite_Assumption27
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:56.394827+00:00
-- url     : https://prove2.me/theorems/1f70c6a4-9568-4618-9145-5495016e2266
-- title:
--   Assumption 2.7, finite-horizon reading
-- statement:
--   The finite-horizon set-up of §2.2 with Assumption 2.7 "understood to hold for $t\in[0,T]$", condition (i) applying "only to the spatial part". For a space-time flow $Z$ on $\mathbb R\times\mathbb R^m$ ($m=d-1$), horizon $T$, rate $r$ and payoffs $\varphi,\psi$:
--
--   1. the time coordinate moves at unit speed: $Z^{(t,x)}_s=(t+s,X^{(t,x)}_s)$;
--   2. for each $s\ge0$, $z\mapsto Z^z_s$ is $\mathsf P$-a.s. continuous on $[0,T]\times\mathbb R^{d-1}$;
--   3. there is $\rho\in(0,1)$ such that $e^{-2r(1-\rho)s}(1+|X^z_s|_{d-1}^2)$ is an $\mathbb F$-supermartingale for every $z\in[0,T]\times\mathbb R^{d-1}$;
--   4. for every compact $K\subseteq[0,T]\times\mathbb R^{d-1}$, $\sup_{z\in K}\mathsf E[\sup_{s\ge0}e^{-rs}|Z^z_s|]<\infty$;
--   5. for $z_n\to z$ in $[0,T]\times\mathbb R^{d-1}$, $\mathsf E[\sup_{s\ge0}e^{-rs}|Z^{z_n}_s-Z^z_s|]\to0$;
--   6. $\varphi,\psi$ belong to the finite-horizon $\mathcal A_d$ and $\varphi\le\psi$ on $[0,T]\times\mathbb R^{d-1}$.
--
--   **Formalization Note** The flow is defined for all starting points and all $s\ge0$ (the proof of Lemma 3.4, Step 2, uses it after $T-t$). The norm on $\mathbb R\times\mathbb R^m$ in 4–5 is the product (max) norm, equivalent to $|\cdot|_d$, so these conditions are unchanged.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2.2, pp.9–10, with Assumption 2.7, p.8

import Mathlib
import Definitions.Def_RecursiveStopping_Finite_InA

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- The finite-horizon set-up of Colaneri & De Angelis, arXiv:1905.02650v4, §2.2, pp.9–10, with
Assumption 2.7 (p.8) in its finite-horizon reading.

The space-time flow `Z : ℝ × ℝ^m → ℝ≥0 → Ω → ℝ × ℝ^m` (`m = d − 1`) has time coordinate
`(Z^z_s)_1 = t + s` for `z = (t, x)` ("`X_s = (t + s, X^1_s, …, X^{d−1}_s)`", p.9). Then
"Assumption 2.7 and the subsequent discussion are understood to hold for `t ∈ [0, T]`.
Moreover, condition (i) in that assumption only applies to the 'spatial' part of the process"
(pp.9–10):
* the flow `z ↦ Z^z_s` is `P`-a.s. continuous on `[0, T] × ℝ^m`, for each `s ≥ 0`;
* (i) there is `ρ ∈ (0, 1)` with `e^{−2r(1−ρ)s}(1 + |X^z_s|_{d−1}²)` (spatial part) an
  `𝔽`-supermartingale under `P` for every `z ∈ [0, T] × ℝ^m`;
* (ii) for every compact `K ⊂ [0, T] × ℝ^m`, `sup_{z∈K} E[sup_{s≥0} e^{−rs}|Z^z_s|] < ∞`;
* (iii) for `z_n → z` in `[0, T] × ℝ^m`, `E[sup_{s≥0} e^{−rs}|Z^{z_n}_s − Z^z_s|] → 0`;
* (iv) `ϕ, ψ ∈ A_d` (finite-horizon `A_d`) with `ϕ ≤ ψ` on `[0, T] × ℝ^m`.

**Formalization Note** The norm on `ℝ × ℝ^m` in (ii)–(iii) is the product (max) norm, which is
equivalent to the Euclidean norm `|·|_d`; finiteness in (ii) and the limit `0` in (iii) do not
depend on the choice. The flow is defined for every starting point and all `s ≥ 0` (the proof
of Lemma 3.4, Step 2, p.14, evaluates it after `T − t`). -/
structure Assumption27 {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ)
    (Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m)) (T r : ℝ)
    (ϕ ψ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  time : ∀ z s ω, (Z z s ω).1 = z.1 + s
  flow_cont : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ContinuousOn (fun z => Z z s ω) (Dom m T)
  supermart : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ z ∈ Dom m T,
    Supermartingale
      (fun (s : ℝ≥0) ω => Real.exp (-2 * r * (1 - ρ) * (s : ℝ)) * (1 + ‖(Z z s ω).2‖ ^ 2)) 𝔽 P
  growth : ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin m)), IsCompact K → K ⊆ Dom m T →
    (⨆ z ∈ K, ∫⁻ ω, ⨆ s : ℝ≥0, ENNReal.ofReal (Real.exp (-r * (s : ℝ)) * ‖Z z s ω‖) ∂P) < ⊤
  stab : ∀ z ∈ Dom m T, ∀ zs : ℕ → ℝ × EuclideanSpace ℝ (Fin m), (∀ n, zs n ∈ Dom m T) →
    Tendsto zs atTop (𝓝 z) →
    Tendsto (fun n => ∫⁻ ω, ⨆ s : ℝ≥0,
      ENNReal.ofReal (Real.exp (-r * (s : ℝ)) * ‖Z (zs n) s ω - Z z s ω‖) ∂P) atTop (𝓝 0)
  phi_mem : InA T ϕ
  psi_mem : InA T ψ
  phi_le_psi : ∀ z ∈ Dom m T, ϕ z ≤ ψ z

end RecursiveStopping.Finite


