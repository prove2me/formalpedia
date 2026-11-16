-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsMonotoneMixingFidelity
-- name    : MaskingHardness_Supplement_IsMonotoneMixingFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:26.502609+00:00
-- url     : https://prove2.me/theorems/9b8b0f1f-c60a-4aa5-824f-b45b94f071a2
-- title:
--   Monotone mixing fidelity functions (Definition 1.19)
-- statement:
--   A function $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$ is **monotone mixing** if for some nondecreasing $h_0:\mathbb R\to\overline{\mathbb R}$,
--
--   $$
--   h(y,z)=\begin{cases}h_0(\mu)&\text{if }z=\mu y+(1-\mu)\,\vec1/k\in\Delta_k\text{ for some }\mu\in[0,1],\\-\infty&\text{otherwise.}\end{cases}
--   $$
--
--   Such functions only reward noisy labels that mix the original label with uniform noise (Example 1.8).
--
--   **Formalization Note** The first case is stated for every $\mu\in[0,1]$ with $z=\mu e_i+(1-\mu)\vec1/k$. For $k\ge2$ the $\mu$ is unique; for $k=1$ every $\mu$ gives $z=1$, and the definition then forces $h_0$ to be constant on $[0,1]$. Closedness, properness and concavity are not required.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.19, pp.10–11 (PDF pp.12–13)

import Mathlib

namespace MaskingHardness.Supplement

/-- **Monotone mixing fidelity function** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.19, printed pp.10–11 = PDF
pp.12–13): `h : Y × Δ_k → ℝ̄` is monotone mixing if for some nondecreasing `h0 : ℝ → ℝ̄`,
`h(y, z) = h0(µ)` if `z = µ y + (1 − µ) 1⃗/k ∈ Δ_k` for some `µ ∈ [0, 1]`, and `h(y, z) = −∞`
otherwise.

**Formalization Note** `y = e_i` is `Pi.single i 1`; ℝ̄ is `EReal`. The first clause is stated for
every such `µ` (for `k ≥ 2` the `µ` is unique; for `k = 1` every `µ` gives `z = 1`, and the clause
forces `h0` to be constant on `[0, 1]`, which is what "`h0(µ)` for some `µ`" must mean there). The
points `µ e_i + (1 − µ)1⃗/k` with `µ ∈ [0,1]` always lie in `Δ_k`. Closedness, properness and
concavity (Definition 1.5) are not required. -/
def IsMonotoneMixingFidelity {k : ℕ} (h : Fin k → (Fin k → ℝ) → EReal) : Prop :=
  ∃ h0 : ℝ → EReal, Monotone h0 ∧
    ∀ i z,
      (∀ μ ∈ Set.Icc (0 : ℝ) 1,
        z = μ • (Pi.single i (1 : ℝ) : Fin k → ℝ) + (1 - μ) • (fun _ => (k : ℝ)⁻¹) →
          h i z = h0 μ) ∧
      ((¬ ∃ μ ∈ Set.Icc (0 : ℝ) 1,
        z = μ • (Pi.single i (1 : ℝ) : Fin k → ℝ) + (1 - μ) • (fun _ => (k : ℝ)⁻¹)) →
          h i z = ⊥)

end MaskingHardness.Supplement


