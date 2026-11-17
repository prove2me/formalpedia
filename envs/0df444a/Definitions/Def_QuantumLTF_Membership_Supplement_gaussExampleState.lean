-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_gaussExampleState
-- name    : QuantumLTF_Membership_Supplement_gaussExampleState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:35:27.491425+00:00
-- url     : https://prove2.me/theorems/787949b8-d2a7-4424-ae0e-deb9eaafe8ed
-- title:
--   Continuous quantum example state $\mathsf{QEX}(f_w,\gamma_n)|0\rangle$
-- statement:
--   The continuous quantum example state of $f_w(x)=\mathrm{sign}(\langle w,x\rangle)$ under the standard Gaussian $\gamma_n$ is
--   $$\psi_w=\int_{\mathbb R^n}\sqrt{\gamma_n(x)}\,|x\rangle|\bar f_w(x)\rangle\,dx,\qquad \gamma_n(x)=(2\pi)^{-n/2}e^{-\|x\|^2/2},$$
--   the function on $\mathbb R^n\times\{0,1\}$ equal to $\sqrt{\gamma_n(x)}$ when $b=\bar f_w(x)$ and $0$ otherwise. It is a unit vector of $L^2(\mathbb R^n\times\{0,1\})$.
--
--   **Formalization Note** $\mathrm{sign}(0)=+1$; the label bit $1$ means $f_w(x)=-1$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §1.5, Eq. (6), p. 10 (PDF p. 11); p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- **The continuous quantum example state of `f_w` under `γ_n`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §1.5, Eq. (6), p. 10
(PDF p. 11), and p. 11 (PDF p. 12): `QEX(f_w, γ_n)|0⟩ = ∫_{ℝⁿ} √γ_n(x) |x⟩|f̄_w(x)⟩ dx`, with
`f̄_w := (1 − f_w)/2` and `γ_n(x) = (2π)^{−n/2} e^{−‖x‖²/2}` (p. 16, PDF p. 17). As a function on
`ℝⁿ × {0,1}`: `ψ_w(x, b) = √γ_n(x)` if `b = f̄_w(x)` and `0` otherwise; it is a unit vector of
`L²(ℝⁿ × {0,1}, dx ⊗ counting)`.

**Formalization Note.** `f_w = ltf w 0` (sign with `sign(0) = +1`); `b = true` is the label `1`, i.e.
`f_w(x) = −1`. Given as a plain function: an oracle's output is compared with it almost everywhere
(`IsQEXCont`). -/
noncomputable def gaussExampleState {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × Bool) : ℂ :=
  if p.2 = decide (ltf w 0 p.1 = -1) then
    (Real.sqrt ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖p.1‖ ^ 2 / 2)) : ℂ)
  else 0

end QuantumLTF.Membership.Supplement


