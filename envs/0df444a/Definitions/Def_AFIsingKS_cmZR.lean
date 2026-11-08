-- Prove2me | Definitions.Def_AFIsingKS_cmZR
-- name    : AFIsingKS_cmZR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:12.78131+00:00
-- url     : https://prove2.me/theorems/dd855164-e0a9-4b32-8a2f-942fdfe191e6
-- title:
--   Partition functions of a matching at real $\beta$, and $Z^{(3)}_{G,<\varepsilon}$
-- statement:
--   For real $\beta$ the quantities $Z_{G,<\varepsilon}(\beta)$, $Z_{G,\ge\varepsilon}(\beta)$ and $Z^{(2)}_{G,<\varepsilon}(\beta)$ are real and the conjugate plays no role. The real-$\beta$ statements of the paper compare them by inequalities. In addition,
--   $$Z^{(3)}_{G,<\varepsilon}(\beta)=\sum_{\sigma^1,\sigma^2,\sigma^3\in\Sigma_n(\varepsilon)}\mathbf 1\{\max(|R(\sigma^1,\sigma^2)|,|R(\sigma^1,\sigma^3)|,|R(\sigma^2,\sigma^3)|)<\varepsilon\}\,e^{\beta\mathcal H_G(\sigma^1)+\beta\mathcal H_G(\sigma^2)+\beta\mathcal H_G(\sigma^3)}.$$
--
--   **Formalization Note** These are real-valued sums; their casts to the complex numbers are the complex versions at a real argument.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, pp.11–12, Remark 4, p.12, and eq. (17), p.18

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical

namespace AFIsingKS

/-- `Z_{G,<ε}(β)` at a real `β`, as a real number (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.11, and Remark 4, p.12).

**Formalization Note.** The real-`β` statements of the paper compare these quantities by `≤`, which
needs real values. Casting this to `ℂ` gives `cmZlt ε M β` (by `push_cast`), and likewise for `cmZgeR`
and `cmZ2ltR`. -/
noncomputable def cmZltR {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℝ) : ℝ :=
  ∑ σ ∈ balanced n ε, Real.exp (β * (cmCut M σ : ℝ))

/-- `Z_{G,≥ε}(β)` at a real `β`, as a real number (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.11). -/
noncomputable def cmZgeR {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℝ) : ℝ :=
  ∑ σ ∈ unbalanced n ε, Real.exp (β * (cmCut M σ : ℝ))

/-- `Z^{(2)}_{G,<ε}(β)` at a real `β`, where the conjugate plays no role, as a real number
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.12, and Remark 4, p.12). -/
noncomputable def cmZ2ltR {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℝ) : ℝ :=
  ∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε,
    if |overlap σ₁ σ₂| < ε then
      Real.exp (β * (cmCut M σ₁ : ℝ) + β * (cmCut M σ₂ : ℝ))
    else 0

/-- `Z^{(3)}_{G,<ε}(β) = ∑_{σ¹,σ²,σ³ ∈ Σ_n(ε)} 1{max(|R(σ¹,σ²)|, |R(σ¹,σ³)|, |R(σ²,σ³)|) < ε}
exp(β H_G(σ¹) + β H_G(σ²) + β H_G(σ³))` for a real `β` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (17), p.18). -/
noncomputable def cmZ3ltR {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℝ) : ℝ :=
  ∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε, ∑ σ₃ ∈ balanced n ε,
    if max (max |overlap σ₁ σ₂| |overlap σ₁ σ₃|) |overlap σ₂ σ₃| < ε then
      Real.exp (β * (cmCut M σ₁ : ℝ) + β * (cmCut M σ₂ : ℝ) + β * (cmCut M σ₃ : ℝ))
    else 0

end AFIsingKS


