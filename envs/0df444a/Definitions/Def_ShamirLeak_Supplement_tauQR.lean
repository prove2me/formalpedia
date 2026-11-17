-- Prove2me | Definitions.Def_ShamirLeak_Supplement_tauQR
-- name    : ShamirLeak_Supplement_tauQR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:55:57.427205+00:00
-- url     : https://prove2.me/theorems/b400b878-d1f6-4e8d-9606-f9e10a89cf66
-- title:
--   The quadratic-residue bit $\tau_{\mathrm{QR}}$ and quadratic-residue leakage with affine shifts
-- statement:
--   Let $p$ be a prime. The **quadratic-residue bit** is the map $\tau_{\mathrm{QR}}:\mathbb F_p\to\{0,1\}$ with
--
--   $$\tau_{\mathrm{QR}}(x)=\begin{cases}1 & \text{if } x=r^2 \text{ for some } r\in\mathbb F_p,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   Zero counts as a square, so $\tau_{\mathrm{QR}}(0)=1$.
--
--   Given shifts $a=(a_1,\dots,a_n)$ and $b=(b_1,\dots,b_n)$ in $\mathbb F_p^n$, the **quadratic-residue leakage with affine shifts** is the one-bit local leakage function $\tau=(\tau_1,\dots,\tau_n)$ with
--
--   $$\tau_i(x)=\tau_{\mathrm{QR}}(a_i x+b_i),\qquad x\in\mathbb F_p .$$
--
--   Party $i$ thus reveals whether $a_iP(\alpha_i)+b_i$ is a square. This is the structured leakage family of Theorem 7(1) (and Theorem 3(1)), where the paper takes $a_i\in\mathbb F_p^*$.
--
--   **Formalization Note** The bit is `true` exactly when `IsSquare x` holds in `ZMod p`; decidability is classical. The condition $a_i\neq 0$ is not built into the definition: the statements that use it assume it.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §5, sentence before Theorem 7, p.22 (PDF 24); Theorem 7(1), p.22; footnote 4, p.1 (PDF 3)

import Mathlib

namespace ShamirLeak.Supplement

/-- The **quadratic-residue bit** `τ_QR : 𝔽_p → {0,1}` (§5, p.22 (PDF p.24); footnote 4, p.1):
`τ_QR(x) = 1` if `x` is a square in `𝔽_p`, including zero, and `τ_QR(x) = 0` otherwise.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §5, sentence before Theorem 7,
p.22 (PDF p.24).

**Formalization Note.** The bit is `true` exactly when `IsSquare x` (`∃ r, x = r * r`) holds in
`ZMod p`; since `0 = 0 * 0`, `τ_QR(0) = true`, as the paper says. Decidability is classical. -/
noncomputable def tauQR {p : ℕ} (x : ZMod p) : Bool := by
  classical
  exact decide (IsSquare x)

/-- The **quadratic-residue leakage with affine shifts** (Theorem 7(1), p.22 (PDF p.24)): the
one-bit local leakage function `τ = (τ₁, …, τₙ)` with `τᵢ(x) = τ_QR(aᵢ x + bᵢ)`.
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Theorem 7(1), p.22 (PDF p.24).

**Formalization Note.** The shifts `a, b : Fin n → ZMod p` are arbitrary here; the condition
`aᵢ ∈ 𝔽_p^*` (`a i ≠ 0`) is a hypothesis of the statements that use this leakage. -/
noncomputable def qrLeak {p n : ℕ} (a b : Fin n → ZMod p) : Fin n → ZMod p → Bool :=
  fun i x => tauQR (a i * x + b i)

end ShamirLeak.Supplement


