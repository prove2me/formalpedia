-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsHighestFidelityResponse
-- name    : MaskingHardness_Supplement_IsHighestFidelityResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:30:55.052049+00:00
-- url     : https://prove2.me/theorems/53fda5b5-0782-4ff0-9b51-0b21b98c47bb
-- title:
--   $\gamma$-optimal highest-fidelity response $\widehat W_h$ (Definition 1.18)
-- statement:
--   Given a fidelity function $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$ and $\gamma\in\mathbb R$, a map $\widehat W_h:\Delta_k\to\Delta_k^k$ is a **$\gamma$-optimal highest-fidelity response** if for every $z\in\Delta_k$ (with $y\sim z$)
--
--   1. $\widehat W_h(z)\in\Delta_k^k$ and $\widehat W_h(z)z=\vec1/k$, and
--   2. $\displaystyle \sup_{W\in\Delta_k^k,\ Wz=\vec1/k}\mathbb E\big[h(y,Wy)\big]\ \le\ \mathbb E\big[h(y,\widehat W_h(z)y)\big]+\gamma .$
--
--   With $\gamma=0$, $\widehat W_h(z)$ attains the maximum: it is a (best-)fidelity response, $\widehat W_h(z)\in\operatorname{argmax}$.
--
--   **Formalization Note** The supremum and the comparison are in `EReal`. The map is a function on $\mathbb R^k$ constrained only at points of $\Delta_k$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.18, p.10 (PDF p.12); recalled p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MaskingHardness_Supplement_IsUniformizing
import Definitions.Def_MaskingHardness_Supplement_responseFidelity

namespace MaskingHardness.Supplement

/-- **`γ`-optimal highest-fidelity response** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.18, printed p.10 = PDF p.12;
recalled p.28 = PDF p.30): `Ŵ_h : Δ_k → Δ_k^k` such that for every `z ∈ Δ_k` (with `y ∼ z`),
`Ŵ_h(z)` is feasible (`Ŵ_h(z) ∈ Δ_k^k` and `Ŵ_h(z) z = 1⃗/k`) and achieves fidelity within `γ`
of the maximum: `E[h(y, Ŵ_h(z) y)] ≥ sup_{W ∈ Δ_k^k, W z = 1⃗/k} E[h(y, W y)] − γ`.

**Formalization Note** The supremum is taken in `EReal` and the comparison is written
`sup ≤ E[h(y, Ŵ_h(z)y)] + γ`. With `γ = 0` this says that `Ŵ_h(z)` attains the maximum, i.e.
is an (exact) highest-fidelity response, `Ŵ_h(z) ∈ argmax`. `Ŵ_h` is a function on `ℝᵏ`
constrained only at `z ∈ Δ_k`. -/
def IsHighestFidelityResponse {k : ℕ} (h : Fin k → (Fin k → ℝ) → EReal) (γ : ℝ)
    (What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ z ∈ stdSimplex ℝ (Fin k), IsUniformizing z (What z) ∧
    (⨆ W : {W : Matrix (Fin k) (Fin k) ℝ // IsUniformizing z W}, responseFidelity h z W.1) ≤
      responseFidelity h z (What z) + (γ : EReal)

end MaskingHardness.Supplement


