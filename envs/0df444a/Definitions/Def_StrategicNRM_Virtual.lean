-- Prove2me | Definitions.Def_StrategicNRM_Virtual
-- name    : StrategicNRM_Virtual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:31.337911+00:00
-- url     : https://prove2.me/theorems/c6d9952f-920f-49e0-ab39-b9afb3fa2b9f
-- title:
--   The virtual-value problem (12) and its value $\tilde J^\chi$
-- statement:
--   For $B\in[0,\infty]$ let the truncated virtual value be
--
--   $$
--   \psi_j^B(v)=\begin{cases} v-\bar F_j(v)/f_j(v), & v<B,\\ B, & v\ge B.\end{cases}
--   $$
--
--   $\tilde J^\chi_B$ is the optimal value of the problem of maximizing $\lambda T\,E_\mu[\sum_j\psi_j^B(v^j_\phi)\tilde b^j_\phi]$ over measurable $\tilde b:\Phi\to[0,1]^n$ with
--
--   $$
--   \sum_{j=1}^n\tilde b^j_\phi\le\chi\quad\forall\phi,\qquad \lambda T\,E_\mu\Big[\sum_{j=1}^n A_{ij}\tilde b^j_\phi\Big]\le x_0^i\quad\forall i.
--   $$
--
--   The printed problem (12) is $B=\infty$; (11) is $\chi=1$. The truncation is what makes Lemma 4 true without a tail condition.
--
--   **Formalization Note** "$E[\sum_j\tilde b^j_\phi]\le\chi$, $\forall\phi$" is read pointwise in $\phi$: $\tilde b$ is a function of $\phi$ alone, and the proof of Lemma 6 uses $\tilde b^j\le\chi$ termwise. The sum over $\mathcal H_T$ is written by Campbell's formula, $E[\sum_{\phi\in\mathcal H_T}g(\phi)]=\lambda T\,E_\mu[g(\phi)]$. Lean has $\bar F/0=0$ where $f_j=0$; those points carry no mass. The objective is required to be integrable, so that a non-integrable $\tilde b$ does not count as $0$.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, p.16, problems (11)–(12)

import Mathlib
import Definitions.Def_StrategicNRM_Fluid

open MeasureTheory
open scoped ENNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- The virtual value truncated at `B ∈ [0,∞]`: `ψⱼᴮ(v) = v − F̄ⱼ(v)/fⱼ(v)` for `v < B`, and `B` for
`v ≥ B`. At `B = ∞` it is the virtual value of (11)–(12), p.16.

**Formalization Note.** Lean has `F̄/0 = 0` at `fⱼ(v) = 0`; those `v` carry no mass. -/
noncomputable def Instance.virtualB (I : Instance n m) (B : ℝ≥0∞) (j : Fin n) (v : ℝ) : ℝ :=
  open Classical in
  if ENNReal.ofReal v < B then v - I.FbarR j v / I.f j v else B.toReal

/-- The constraints of problem (12), p.16, with virtual value `ψᴮ`, on measurable `b̃ : Φ → ℝⁿ`:

* `b̃ʲ_φ ∈ [0,1]`;
* `Σⱼ b̃ʲ_φ ≤ χ` for every `φ`;
* `λT E_μ[Σⱼ A_{ij} b̃ʲ_φ] ≤ xⁱ₀` for every `i`.

**Formalization Note (reading).** "`E[Σⱼ b̃ʲ_φ] ≤ χ, ∀ φ`" is read pointwise in `φ`: `b̃` is a
function of `φ` alone, so the expectation is vacuous there, and the proof of Lemma 6 uses
`b̃ʲ ≤ χ` termwise. The sum over `H_T` is written by Campbell's formula,
`E[Σ_{φ ∈ H_T} g(φ)] = λT E_μ[g(φ)]`. `integrable` says that the objective is defined. -/
structure Instance.IsVirtualFeasible (I : Instance n m) (B : ℝ≥0∞) (χ : ℝ)
    (b : CType n → Fin n → ℝ) : Prop where
  meas : ∀ j, Measurable fun φ => b φ j
  mem : ∀ φ j, b φ j ∈ Set.Icc (0 : ℝ) 1
  sum_le : ∀ φ, ∑ j, b φ j ≤ χ
  inventory : ∀ r, I.lam * I.T * ∫ φ, ∑ j, (I.A r j : ℝ) * b φ j ∂I.typeLaw ≤ I.x0 r
  integrable : Integrable (fun φ => ∑ j, I.virtualB B j (φ.2.1 j) * b φ j) I.typeLaw

/-- The objective of (12): `λT E_μ[Σⱼ ψⱼᴮ(vʲ_φ) b̃ʲ_φ]`. -/
noncomputable def Instance.objVirtual (I : Instance n m) (B : ℝ≥0∞) (b : CType n → Fin n → ℝ) : ℝ :=
  I.lam * I.T * ∫ φ, ∑ j, I.virtualB B j (φ.2.1 j) * b φ j ∂I.typeLaw

/-- `J̃^χ`, the optimal value of problem (12), p.16, for the virtual value truncated at `B`. The
printed problem is `B = ∞`. -/
noncomputable def Instance.Jtilde (I : Instance n m) (B : ℝ≥0∞) (χ : ℝ) : EReal :=
  ⨆ b : {b // I.IsVirtualFeasible B χ b}, ((I.objVirtual B b.1 : ℝ) : EReal)

end StrategicNRM


