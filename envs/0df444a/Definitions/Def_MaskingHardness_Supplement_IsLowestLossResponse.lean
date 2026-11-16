-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsLowestLossResponse
-- name    : MaskingHardness_Supplement_IsLowestLossResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:30:26.966555+00:00
-- url     : https://prove2.me/theorems/f8d69f09-eaa1-4e41-9ed6-e9fab876cea7
-- title:
--   $\gamma$-optimal lowest-loss response $\hat c_g$ (Definition 1.17)
-- statement:
--   Given a loss $g:\mathcal Y\times\mathbb R^k\to\mathbb R$ with $\mathcal Y=[k]$ and $\gamma\in\mathbb R$, a map $\hat c_g:\Delta_k\to\mathbb R^k$ is a **$\gamma$-optimal lowest-loss response** if for every $z\in\Delta_k$ (with $y\sim z$)
--
--   1. $\langle\hat c_g(z),\vec1\rangle=0$, and
--   2. $\displaystyle \mathbb E\big[g(y,\hat c_g(z))\big]\ \le\ \inf_{c\in\mathbb R^k,\ \langle c,\vec1\rangle=0}\mathbb E\big[g(y,c)\big]+\gamma .$
--
--   With $\gamma=0$ this says $\hat c_g(z)$ attains the minimum. It is the post-processing used in omniprediction.
--
--   **Formalization Note** $\mathbb E_{y\sim z}[g(y,c)]=\sum_i z_i g(e_i,c)$; the infimum is taken in `EReal`, so if it is $-\infty$ no response is $\gamma$-optimal. The map is a function on $\mathbb R^k$ constrained only at points of $\Delta_k$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.17, p.10 (PDF p.12); recalled p.28 (PDF p.30)

import Mathlib

namespace MaskingHardness.Supplement

/-- **`γ`-optimal lowest-loss response** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.17, printed p.10 = PDF p.12; recalled
p.28 = PDF p.30): `ĉ_g : Δ_k → ℝᵏ` such that for every `z ∈ Δ_k` (with `y ∼ z`), `ĉ_g(z)` is
feasible, `⟨ĉ_g(z), 1⃗⟩ = 0`, and achieves loss within `γ` of the infimum:
`E[g(y, ĉ_g(z))] ≤ inf_{c ∈ ℝᵏ, ⟨c, 1⃗⟩ = 0} E[g(y, c)] + γ`.

**Formalization Note** `E_{y∼z}[g(y, c)] = ∑_i z_i g(e_i, c)`; the infimum is taken in `EReal`
(it may be `−∞`, in which case no response is `γ`-optimal). `ĉ_g` is a function on `ℝᵏ`
constrained only at `z ∈ Δ_k`. An exact lowest-loss response is the case `γ = 0`. -/
def IsLowestLossResponse {k : ℕ} (g : Fin k → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (chat : (Fin k → ℝ) → (Fin k → ℝ)) : Prop :=
  ∀ z ∈ stdSimplex ℝ (Fin k), (∑ j, chat z j = 0) ∧
    (((∑ i, z i * g i (chat z) : ℝ)) : EReal) ≤
      (⨅ c : {c : Fin k → ℝ // ∑ j, c j = 0}, (((∑ i, z i * g i c.1 : ℝ)) : EReal)) + (γ : EReal)

end MaskingHardness.Supplement


