-- Prove2me | Definitions.Def_MaskingHardness_Supplement_responseFidelity
-- name    : MaskingHardness_Supplement_responseFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:30:10.54553+00:00
-- url     : https://prove2.me/theorems/ad3b1622-477a-4908-9e1e-59a6156315f2
-- title:
--   Fidelity $\mathbb E_{y\sim z}[h(y,Wy)]$ of a response channel
-- statement:
--   For a fidelity function $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$, a label distribution $z$ and a $k\times k$ matrix $W$,
--
--   $$
--   \mathbb E_{y\sim z}\big[h(y,Wy)\big]=\sum_{i\in[k]} z_i\,h(e_i,We_i),
--   $$
--
--   the objective of Definition 1.18.
--
--   **Formalization Note** The sum is in `EReal` with $0\cdot(-\infty)=0$, so a label of probability $0$ contributes nothing; $h$ is given on $\mathbb R^k$ and equals $-\infty$ off $\Delta_k$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.18, p.10 (PDF p.12)

import Mathlib

namespace MaskingHardness.Supplement

/-- **Fidelity of a response channel at `z`** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.18, printed p.10 = PDF p.12):
`E_{y ∼ z}[h(y, W y)] = ∑_i z_i h(e_i, W e_i)` for a fidelity function `h : Y × Δ_k → ℝ̄`, a
label distribution `z ∈ Δ_k` and a matrix `W`.

**Formalization Note** ℝ̄ is `EReal` (`0 · (−∞) = 0`, so a label of probability `0` contributes
nothing); `W e_i` is column `i`, `fun j => W j i`; `h` is given on `ℝᵏ` and is `−∞` off
`Δ_k`. -/
noncomputable def responseFidelity {k : ℕ} (h : Fin k → (Fin k → ℝ) → EReal) (z : Fin k → ℝ)
    (W : Matrix (Fin k) (Fin k) ℝ) : EReal :=
  ∑ i, ((z i : ℝ) : EReal) * h i (fun j => W j i)

end MaskingHardness.Supplement


