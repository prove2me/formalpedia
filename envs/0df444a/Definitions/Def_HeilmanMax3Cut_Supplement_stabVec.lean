-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_stabVec
-- name    : HeilmanMax3Cut_Supplement_stabVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:00:58.803819+00:00
-- url     : https://prove2.me/theorems/60bc7a4c-5fbc-4615-8d2f-edfe3ceedc8c
-- title:
--   Noise stability $\mathrm{Stab}_\rho(f)$ of a ball-valued function
-- statement:
--   For a bounded measurable $f:\mathbb R^n\to B_k$, where $B_k=\{x\in\mathbb R^k:\|x\|\le1\}$, the noise stability with correlation parameter $\rho$ is
--
--   $$\mathrm{Stab}_\rho(f)=\int_{\mathbb R^n}\langle f(x),T_\rho f(x)\rangle\,\gamma_n(x)\,dx .$$
--
--   Equivalently $\mathrm{Stab}_\rho(f)=\mathbb E\langle f(X),f(Y)\rangle$ for $\rho$-correlated standard Gaussians $X,Y$. It is the quantity bounded by the vector-valued Borell inequalities.
--
--   **Formalization Note** The value is defined for every $f$; the theorems assume $f$ measurable with $\|f(x)\|\le1$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2, p.9

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Supplement_ouOpVec
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut.Supplement

/-- **Noise stability `Stab_ρ(f)` of a ball-valued function.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2, p.9: "For a
bounded measurable `f : ℝⁿ → B_k`, where `B_k = {x ∈ ℝᵏ : ‖x‖ ≤ 1}`, define the noise stability with
correlation parameter `ρ` to be `Stab_ρ(f) := ∫_{ℝⁿ} ⟨f(x), T_ρ f(x)⟩ γₙ(x) dx`."

**Formalization Note.** `⟨·, ·⟩` is the Euclidean inner product of `EuclideanSpace ℝ (Fin k)` and
`T_ρ` is `ouOpVec`. The value is defined for every `f`; the theorems assume `f` measurable with
`‖f x‖ ≤ 1` for all `x` (the paper's `f : ℝⁿ → B_k`), where the integrand is bounded by `1` and the
Bochner integral is that of an integrable function. -/
noncomputable def stabVec (n k : ℕ) (ρ : ℝ) (f : Space n → EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∫ x, inner ℝ (f x) (ouOpVec n k ρ f x) ∂(gaussian n)

end HeilmanMax3Cut.Supplement


