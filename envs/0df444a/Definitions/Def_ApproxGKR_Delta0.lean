-- Prove2me | Definitions.Def_ApproxGKR_Delta0
-- name    : ApproxGKR_Delta0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:01.664311+00:00
-- url     : https://prove2.me/theorems/46c2595d-6b65-42e2-ae20-5b87c291b632
-- title:
--   The parameter choice $\vartheta$, $N$, $\Gamma$, $\Delta_0$ of (C.17)–(C.18)
-- statement:
--   For $0<\varepsilon<1$ and $\Delta>0$ the paper sets
--   $$\vartheta=\frac{\varepsilon}{4(kD+L)},\quad \alpha=\vartheta^D,\quad\beta=\vartheta,$$
--   takes $N$ to be the least power of two at least $1/\vartheta$, and
--   $$\Gamma=6\Big(\frac{5(1+K)}{\beta}\Big)^L\Big(\frac{9h}{\alpha}\Big)^k,\qquad \Delta_0=2^{-\max\{0,\lceil\log_2(\Gamma/\Delta)\rceil\}}.$$
--   These are the choices of $N$ and $\Delta_0$ that Theorem C.1 asserts exist.
--
--   **Formalization Note** $N=2^{\lceil\log_2\lceil1/\vartheta\rceil\rceil}$; logarithms are to base two (p.5).
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, eqs. (C.17)–(C.18), p.39

import Mathlib

namespace ApproxGKR

/-- `ϑ = ε/(4(kD + L))` (eq. (C.17), p.39).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.3, eq. (C.17), p.39. -/
noncomputable def theta (ε : ℝ) (k D L : ℕ) : ℝ := ε / (4 * ((k : ℝ) * D + L))

/-- "take `N` to be the least power of two at least `1/ϑ`" (p.39): `N = 2^{⌈log₂ ⌈1/ϑ⌉⌉}`. -/
noncomputable def Npar (θ : ℝ) : ℕ := 2 ^ Nat.clog 2 ⌈1 / θ⌉₊

/-- `Γ = 6(5(1 + K)/β)^L (9h/α)^k` (eq. (C.18), p.39). -/
noncomputable def Gamma (L k h : ℕ) (K α β : ℝ) : ℝ :=
  6 * (5 * (1 + K) / β) ^ L * (9 * (h : ℝ) / α) ^ k

/-- `∆₀ = 2^{−max{0, ⌈log(Γ/∆)⌉}}` (eq. (C.18), p.39), logarithm to base two (p.5:
"Logarithms use base two"). -/
noncomputable def Delta0 (Γ Δ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(max 0 ⌈Real.logb 2 (Γ / Δ)⌉))

end ApproxGKR


