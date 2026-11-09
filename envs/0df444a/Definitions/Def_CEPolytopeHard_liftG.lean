-- Prove2me | Definitions.Def_CEPolytopeHard_liftG
-- name    : CEPolytopeHard_liftG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:28.252461+00:00
-- url     : https://prove2.me/theorems/9567499e-8c02-4bb9-901f-2342691c69d5
-- title:
--   Multi-scale lift $g$ and the parameters $r$, $b$, $\zeta$ of (12)
-- statement:
--   For a support bound $K \ge 2$, a Lipschitz constant $L$, an accuracy $\delta$ and a constant $\lambda$, (12) sets
--   $$
--   r := (1 + \lceil \log_2 K\rceil)\,\lceil 128(L+1)^2/\delta^2\rceil, \qquad b := \lceil \max\{2,\ 2\lambda + 1,\ 2^{14}(L+1)^2/\delta^3\}\rceil, \qquad \zeta := \frac{\delta}{16\, r\, b^r}.
--   $$
--   For $f : [0,1]^d \to [0,1]^d$ the **lift** $g : [0,1]^{dr} \to [0,1]^{dr}$ acts on the $r$ layers $x^{(1)}, \dots, x^{(r)} \in [0,1]^d$ by
--   $$
--   g(x^{(1)}, \dots, x^{(r)}) = \Big((1 - b^{-\ell})x^{(\ell)} + b^{-\ell} f(x^{(\ell)})\Big)_{\ell=1}^r .
--   $$
--
--   **Formalization Note** Vectors of $\mathbb R^{dr}$ are indexed by pairs (layer, coordinate). Layers are 0-based in Lean, so Lean's layer $\ell$ is the paper's layer $\ell + 1$ with weight $b^{-(\ell+1)}$. $\lceil\log_2 K\rceil$ is `Nat.clog 2 K`.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Eq. (12), p.21

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- the number of layers `r := (1 + ⌈log₂ K⌉)⌈128(L + 1)²/δ²⌉` of (12) (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Eq. (12), p.21);
`⌈log₂ K⌉` is `Nat.clog 2 K` -/
noncomputable def liftR (K : ℕ) (L δ : ℝ) : ℕ :=
  (1 + Nat.clog 2 K) * ⌈128 * (L + 1) ^ 2 / δ ^ 2⌉₊

/-- the base `b := ⌈max{2, 2λ + 1, 2^{14}(L + 1)²/δ³}⌉` of (12), p.21 -/
noncomputable def liftB (lam L δ : ℝ) : ℕ :=
  ⌈max (max 2 (2 * lam + 1)) (2 ^ 14 * (L + 1) ^ 2 / δ ^ 3)⌉₊

/-- the accuracy `ζ := δ/(16 r b^r)` (p.21) -/
noncomputable def liftZeta (r b : ℕ) (δ : ℝ) : ℝ := δ / (16 * r * (b : ℝ) ^ r)

/-- layer `ℓ` (a `d`-dimensional block `x^{(ℓ)}`) of a lifted vector in `ℝ^{dr}` -/
def layer {r d : ℕ} (x : Fin r × Fin d → ℝ) (ℓ : Fin r) : Fin d → ℝ := fun i => x (ℓ, i)

/-- The **multi-scale lift `g : [0, 1]^{dr} → [0, 1]^{dr}`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.21: "define
g : [0, 1]^{dr} → [0, 1]^{dr} by g(x^{(1)}, . . . , x^{(r)}) = ((1 − b^{−ℓ})x^{(ℓ)} + b^{−ℓ}f(x^{(ℓ)}))_{ℓ=1}^r";
Section 3.2, p.15, with `α_ℓ = b^{−ℓ}`, p.18).

**Formalization Note** Vectors of `ℝ^{dr}` are indexed by `Fin r × Fin d` (layer, coordinate).
Layers are 0-based in Lean: Lean's layer `ℓ` is the paper's layer `ℓ + 1` and uses the weight
`b^{−(ℓ+1)}`. -/
noncomputable def liftG {r d : ℕ} (b : ℕ) (f : (Fin d → ℝ) → Fin d → ℝ) (x : Fin r × Fin d → ℝ) :
    Fin r × Fin d → ℝ :=
  fun ℓi => (1 - (b : ℝ) ^ (-((ℓi.1.val : ℤ) + 1))) * x ℓi +
    (b : ℝ) ^ (-((ℓi.1.val : ℤ) + 1)) * f (layer x ℓi.1) ℓi.2

end CEPolytopeHard


