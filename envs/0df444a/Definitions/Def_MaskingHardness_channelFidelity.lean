-- Prove2me | Definitions.Def_MaskingHardness_channelFidelity
-- name    : MaskingHardness_channelFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:41.42244+00:00
-- url     : https://prove2.me/theorems/797ac0e6-82e3-4860-8984-ea4fdda287f0
-- title:
--   Fidelity $\mathbb E[h(y,W(x)y)]$ of a channel
-- statement:
--   Given a distribution $\mathcal D$ on $\mathcal X\times[k]$, a fidelity function $h:[k]\times\Delta_k\to\overline{\mathbb R}$ and a noisy channel $W$, the **fidelity** of $W$ is
--
--   $$
--   \mathbb E_{(x,y)\sim\mathcal D}\bigl[h\bigl(y,W(x)y\bigr)\bigr]\in\overline{\mathbb R}.
--   $$
--
--   The right-hand side of the main theorem is the largest fidelity of a $(\mathcal C,\varepsilon)$-masking channel.
--
--   **Formalization Note** The expectation is $\sum_{x,y}\mathcal D(x,y)\,h(y,W(x)y)$ computed in `EReal`, where $0\cdot(-\infty)=0$ (a pair of probability zero contributes nothing) and $r\cdot(-\infty)=-\infty$ for $r>0$. $W(x)y$ is the $y$-th column of $W(x)$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.5, p.5 (PDF p.7); Theorem 1.9, p.6 (PDF p.8)

import Mathlib

namespace MaskingHardness

/-- **Fidelity of a channel** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking
Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.5 and Theorem 1.9,
printed pp.5–6 = PDF pp.7–8): `E_D[h(y, W(x)y)]` for a fidelity function `h : Y × Δ_k → ℝ̄`.

**Formalization Note** ℝ̄ is `EReal`; the expectation is `∑ₓ ∑_y D(x, y) · h(y, W(x)y)` in
`EReal`, where `0 · (−∞) = 0` (a zero-probability pair contributes nothing) and
`r · (−∞) = −∞` for `r > 0`. `W(x)y` is the `y`-th column of `W(x)`. -/
noncomputable def channelFidelity {X : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ)
    (h : Fin k → (Fin k → ℝ) → EReal) (W : X → Matrix (Fin k) (Fin k) ℝ) : EReal :=
  ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (fun i => W x i y)

end MaskingHardness


