-- Prove2me | Definitions.Def_SymNormLoad_phiBar
-- name    : SymNormLoad_phiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:17.202229+00:00
-- url     : https://prove2.me/theorems/953818e0-0c4a-45fb-9427-47e8ff529ea6
-- title:
--   Piecewise-linear extension of $\varphi$ to $[0,M]$
-- statement:
--   The function $\varphi$ is extended from $\{0,\dots,M\}$ to $[0,M]$ by linear interpolation between consecutive integers: for $s\in[0,M]$ and $k=\lfloor s\rfloor$,
--   $$
--   \varphi(s)=\varphi(k)+(s-k)\bigl(\varphi(k+1)-\varphi(k)\bigr),
--   $$
--   which gives $\varphi(M)$ at $s=M$. In particular $\varphi(s)=s\,\varphi(1)$ on $[0,1]$. This continuous function is the one in the differential equation (2.2).
--
--   **Formalization Note** Outside $[0,M]$ the argument is clamped to $[0,M]$; every use in the paper has its argument in $[0,M]$.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.1, p.9

import Mathlib
import Definitions.Def_SymNormLoad_phi

namespace SymNormLoad

/-- **Piecewise-linear extension `φ(s)` of `φ`.** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), §2.1.1, p.9: "Extend φ by linear
interpolation between consecutive integers, giving a continuous function on [0, M]."

For `s ∈ [0, M]` with `k = ⌊s⌋`, `φ̄(s) = φ(k) + (s − k)(φ(k+1) − φ(k))`; at `s = M` this is
`φ(M)`.

**Formalization Note** Outside `[0, M]` the argument is clamped to `[0, M]`
(`φ̄(s) = φ̄(max 0 (min s M))`). Every use in the paper has its argument in `[0, M]`, so the
clamp changes no instance. -/
noncomputable def phiBar {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) (s : ℝ) : ℝ :=
  let s' : ℝ := max 0 (min s (M : ℝ))
  let k : ℕ := ⌊s'⌋₊
  phi Ψ k + (s' - k) * (phi Ψ (k + 1) - phi Ψ k)

end SymNormLoad


