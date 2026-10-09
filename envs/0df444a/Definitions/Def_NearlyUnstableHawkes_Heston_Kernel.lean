-- Prove2me | Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
-- name    : NearlyUnstableHawkes_Heston_Kernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:21.943192+00:00
-- url     : https://prove2.me/theorems/8d4da6ef-ad86-4ec7-b2c5-3a1087c8f917
-- title:
--   Assumptions 3–4, pp. 13–14 — kernels φ₁, φ₂, convolution powers, the resolvents ψ^T and ψ^T_+, Ψ^T, ρ^T and ‖φ‖₁ = ∫(φ₁ − φ₂)
-- statement:
--   This file fixes the deterministic objects of the Hawkes-based price model of Jaisson and Rosenbaum (§3.2 and §4.4).
--
--   1. **Convolution on $\mathbb R_+$.** For $f,g:\mathbb R_+\to\mathbb R$, $(f*g)(t)=\int_0^t f(t-s)\,g(s)\,ds$, and $f^{*1}=f$, $f^{*(k+1)}=f^{*k}*f$.
--   2. **Resolvents.** For a kernel $f$, the resolvent is $\sum_{k\ge1} f^{*k}(t)$. With $\phi^T_i=a_T\phi_i$ and the signed kernel $\phi^T=\phi^T_1-\phi^T_2$ (p. 26),
--   $$\psi^T=\sum_{k\ge1}(\phi^T)^{*k},\qquad \Psi^T(x)=\int_0^x\psi^T(s)\,ds,$$
--   and, for Assumption 4, $\psi^T_+=\sum_{k\ge1}\big(a_T(\phi_1+\phi_2)\big)^{*k}$ and $\rho^T(x)=T\,\psi^T_+(Tx)/\|\psi^T_+\|_1$.
--   3. **The constant $\|\phi\|_1$ of Theorem 3.1**, for $\phi=\phi_1-\phi_2$, is the signed integral
--   $$\|\phi\|_1=\int_0^{\infty}\big(\phi_1(s)-\phi_2(s)\big)\,ds .$$
--   4. **Assumption 3** (p. 13). $(a_T)$ is a sequence of positive numbers converging to one with $a_T<1$; $\phi_1,\phi_2$ are nonnegative measurable functions on $\mathbb R_+$ with
--   $$\int_0^{\infty}\big(\phi_1(s)+\phi_2(s)\big)\,ds=1,\qquad \int_0^{\infty}s\big(\phi_1(s)+\phi_2(s)\big)\,ds=m<\infty;$$
--   the support of $\phi_2$ has nonzero Lebesgue measure; and each $\phi_i$ is differentiable with a derivative $\phi_i'$ such that $\|\phi_i'\|_\infty<\infty$ and $\|\phi_i'\|_1<\infty$.
--   5. **Assumption 4** (pp. 13–14). There is $K_\rho>0$ such that $|\rho^T(x)|\le K_\rho$ for all $x\ge0$ and all $T$.
--
--   These are shared by every statement of the mission: the goal (Theorem 3.1), display (11), Lemmas 4.12–4.17 and the decomposition of Step 6.
--
--   **Formalization Note** Kernels are functions $\mathbb R\to\mathbb R$ of which only the values on $[0,\infty)$ enter. Convolution powers are indexed with a shift (`convPow f k` is $f^{*(k+1)}$), so the resolvent is `∑' k, convPow f k t`. It is a real `tsum`; under Assumption 3 the series converges absolutely for every $t\ge0$ ($\phi_i$ is bounded, since $\phi_i'$ is integrable, and $|(\phi^T)^{*k}|\le(a_T(\phi_1+\phi_2))^{*k}\le a_T^{k-1}\|a_T(\phi_1+\phi_2)\|_\infty$), so no default value occurs. $\|\psi^T_+\|_1$ is $\int_0^\infty\psi^T_+$ ($\psi^T_+\ge0$), which equals $a_T/(1-a_T)\in(0,\infty)$, so $\rho^T$ has no division by zero. $\|\phi\|_1$ is deliberately the **signed** integral $\int(\phi_1-\phi_2)$, not the $L^1$ norm $\int|\phi_1-\phi_2|$: the proof of Theorem 3.1 (Step 6, p. 31) uses $1+\int_0^\infty\psi^T=1/(1-a_T\int\phi)$, and the two readings agree when $\phi_1\ge\phi_2$. Under Assumption 3, $\|\phi\|_1=1-2\int\phi_2\in[-1,1)$. Differentiability is one-sided at $0$ (`HasDerivWithinAt` on $[0,\infty)$); $\|\phi_i'\|_\infty<\infty$ is a pointwise bound on $[0,\infty)$, which for a derivative is equivalent to an essential bound. The sequence index $n$ stands for $T_n\to\infty$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 13, Assumption 3; pp. 13–14, Assumption 4; p. 14, Theorem 3.1 (‖φ‖₁); pp. 26–27, §4.4 (φ^T, ψ^T, Ψ^T)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

open MeasureTheory Filter
open scoped Topology

namespace NearlyUnstableHawkes.Heston

/-- The resolvent `Σ_{k ≥ 1} f^{∗k}(t)`, a real `tsum` over `k ≥ 1` (written with the shift
`convPow f k = f^{∗(k+1)}`). -/
noncomputable def resolvent (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, NearlyUnstableHawkes.Deterministic.convPow f k t

/-- The signed kernel of §4.4, p. 26: `φ^T = φ^T_1 − φ^T_2 = a_T φ₁ − a_T φ₂`. -/
noncomputable def phiSignedT (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * φ₁ t - a * φ₂ t

/-- `ψ^T = Σ_{k ≥ 1} (φ^T)^{∗k}` with the signed kernel `φ^T = a_T φ₁ − a_T φ₂` (§4.4, p. 26). -/
noncomputable def psiSigned (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  resolvent (phiSignedT a φ₁ φ₂) t

/-- `Ψ^T(x) = ∫_0^x ψ^T(s) ds` (p. 27). -/
noncomputable def PsiSigned (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, psiSigned a φ₁ φ₂ s

/-- `ψ^T_+ = Σ_{k ≥ 1} (a_T(φ₁ + φ₂))^{∗k}` (Assumption 4, p. 13). -/
noncomputable def psiPlus (a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  resolvent (fun s => a * (φ₁ s + φ₂ s)) t

/-- `ρ^T(x) = T ψ^T_+(Tx) / ‖ψ^T_+‖₁` (Assumption 4, p. 13), with `‖ψ^T_+‖₁ = ∫_0^∞ ψ^T_+`
(`ψ^T_+ ≥ 0`). -/
noncomputable def rhoPlus (T a : ℝ) (φ₁ φ₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  T * psiPlus a φ₁ φ₂ (T * x) / ∫ s in Set.Ioi (0 : ℝ), psiPlus a φ₁ φ₂ s

/-- `‖φ‖₁` of Theorem 3.1 for `φ = φ₁ − φ₂`, read as the **signed** integral
`∫_0^∞ (φ₁(s) − φ₂(s)) ds = ∫φ₁ − ∫φ₂` (the value the proof uses on p. 31; see the
mission's notes). It is not the L¹ norm `∫|φ₁ − φ₂|`. -/
noncomputable def phiMass (φ₁ φ₂ : ℝ → ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), (φ₁ s - φ₂ s)

/-- The conditions Assumption 3 (p. 13) places on the kernels `φ₁, φ₂` (everything except the
sequence `a_T`): nonnegative and measurable on `ℝ₊`, `∫_0^∞ (φ₁ + φ₂) = 1`,
`∫_0^∞ s(φ₁(s) + φ₂(s)) ds = m < ∞`, the support of `φ₂` has nonzero Lebesgue measure, and each
`φ_i` is differentiable on `ℝ₊` (one-sided at `0`) with a bounded and integrable derivative. -/
structure KernelAssumption3 (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) : Prop where
  nonneg₁ : ∀ s, 0 ≤ s → 0 ≤ φ₁ s
  nonneg₂ : ∀ s, 0 ≤ s → 0 ≤ φ₂ s
  meas₁ : Measurable φ₁
  meas₂ : Measurable φ₂
  integrable : IntegrableOn (fun s => φ₁ s + φ₂ s) (Set.Ici 0)
  mass_eq_one : ∫ s in Set.Ici (0 : ℝ), (φ₁ s + φ₂ s) = 1
  integrable_mean : IntegrableOn (fun s => s * (φ₁ s + φ₂ s)) (Set.Ici 0)
  mean_eq : ∫ s in Set.Ici (0 : ℝ), s * (φ₁ s + φ₂ s) = m
  support₂ : 0 < volume {s : ℝ | 0 ≤ s ∧ φ₂ s ≠ 0}
  deriv₁ : ∃ φ₁' : ℝ → ℝ, (∀ s, 0 ≤ s → HasDerivWithinAt φ₁ (φ₁' s) (Set.Ici 0) s) ∧
    (∃ C : ℝ, ∀ s, 0 ≤ s → |φ₁' s| ≤ C) ∧ IntegrableOn φ₁' (Set.Ici 0)
  deriv₂ : ∃ φ₂' : ℝ → ℝ, (∀ s, 0 ≤ s → HasDerivWithinAt φ₂ (φ₂' s) (Set.Ici 0) s) ∧
    (∃ C : ℝ, ∀ s, 0 ≤ s → |φ₂' s| ≤ C) ∧ IntegrableOn φ₂' (Set.Ici 0)

/-- **Assumption 3** (p. 13): `φ^T_i = a_T φ_i` where `(a_T)` is a sequence of positive numbers
with `a_T < 1` converging to one, and `φ₁, φ₂` satisfy `KernelAssumption3`. The index `n` runs
along the sequence `T_n → ∞`. -/
def Assumption3 (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) : Prop :=
  (∀ n, 0 < a n) ∧ (∀ n, a n < 1) ∧ Tendsto a atTop (𝓝 1) ∧ KernelAssumption3 φ₁ φ₂ m

/-- **Assumption 4** (pp. 13–14): there is `K_ρ > 0` with `|ρ^T(x)| ≤ K_ρ` for all `x ≥ 0` and all
`T` (along the sequence `T_n`). -/
def Assumption4 (T a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) : Prop :=
  ∃ Kρ : ℝ, 0 < Kρ ∧ ∀ n, ∀ x : ℝ, 0 ≤ x → |rhoPlus (T n) (a n) φ₁ φ₂ x| ≤ Kρ

end NearlyUnstableHawkes.Heston


