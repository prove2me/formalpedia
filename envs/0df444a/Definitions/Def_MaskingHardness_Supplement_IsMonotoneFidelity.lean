-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsMonotoneFidelity
-- name    : MaskingHardness_Supplement_IsMonotoneFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:14.218963+00:00
-- url     : https://prove2.me/theorems/ac9026fe-0d49-4f19-8746-c5483b0370a7
-- title:
--   Monotone fidelity functions (Definition 1.19)
-- statement:
--   Let $\mathcal Y=\{e_1,\dots,e_k\}$. A function $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$ is **monotone** if there is a nondecreasing $h_0:\mathbb R\to\overline{\mathbb R}$ with
--
--   $$
--   h(y,z)=\begin{cases}h_0(\langle y,z\rangle)&\text{if }z\in\Delta_k,\\-\infty&\text{otherwise.}\end{cases}
--   $$
--
--   Examples are $h(y,z)=\langle y,z\rangle$ (Example 1.6). For such $h$ one post-processing serves all fidelity functions at once (Theorem 6.6).
--
--   **Formalization Note** $\langle e_i,z\rangle=z_i$. The predicate asks only for this form; it does not require $h$ to be closed, proper and concave (the paper's standing requirement on fidelity functions, Definition 1.5).
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.19, p.10 (PDF p.12)

import Mathlib
open Classical

namespace MaskingHardness.Supplement

/-- **Monotone fidelity function** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.19, printed p.10 = PDF p.12):
`h : Y × Δ_k → ℝ̄` is monotone if there is a nondecreasing `h0 : ℝ → ℝ̄` with
`h(y, z) = h0(⟨y, z⟩)` for `z ∈ Δ_k` and `h(y, z) = −∞` otherwise.

**Formalization Note** `Y = {e_1, …, e_k}` is `Fin k` and `⟨e_i, z⟩ = z_i`; ℝ̄ is `EReal`. The
paper's fidelity functions are also closed, proper and concave in `z` (Definition 1.5); the
predicate does not require this. -/
def IsMonotoneFidelity {k : ℕ} (h : Fin k → (Fin k → ℝ) → EReal) : Prop :=
  ∃ h0 : ℝ → EReal, Monotone h0 ∧
    ∀ i z, h i z = if z ∈ stdSimplex ℝ (Fin k) then h0 (z i) else ⊥

end MaskingHardness.Supplement


