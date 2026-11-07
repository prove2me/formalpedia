-- Prove2me | Definitions.Def_AvgValueAlloc_Phi
-- name    : AvgValueAlloc_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:21.708591+00:00
-- url     : https://prove2.me/theorems/d12fa7e7-0b96-4eec-b898-206bb5bcc1b0
-- title:
--   Rate functions $\psi,\Phi,\Psi,\Lambda$ of (3)
-- statement:
--   With natural logarithms,
--   $$
--   \psi(x)=\max\Bigl\{1,\frac{x}{\log(2+x)}\Bigr\},\quad \Phi(d,T,S)=\min\Bigl\{T,\ \psi\Bigl(\frac{\log(2+d)}{1+S/T}\Bigr)\Bigr\},\quad \Psi(d,T)=\Phi(d,T,0),\quad \Lambda(d,T)=\min\{T,\log(2+d)\}.\tag{3}
--   $$
--   These are the approximation factors of Table 1.
--
--   **Formalization Note** $S/T$ is real division; every statement using $\Phi$ assumes $T\ge1$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.2, p.2, eq. (3)

import Mathlib

namespace AvgValueAlloc

/-- **The rate functions `ψ`, `Φ`, `Ψ`, `Λ` of (3).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.2, p.2, (3): "With natural logarithms, put
ψ(x) = max{1, x/ log(2 + x)}, Φ(d, T, S) = min{T, ψ(log(2 + d)/(1 + S/T))}, Ψ(d, T) = Φ(d, T, 0),
Λ(d, T) = min{T, log(2 + d)}."

**Formalization Note.** Natural logarithm `Real.log`; `S/T` is real division. Every statement
using `Φ` assumes `T ≥ 1`. -/
noncomputable def psi (x : ℝ) : ℝ := max 1 (x / Real.log (2 + x))

/-- `Φ(d, T, S) = min{T, ψ(log(2 + d)/(1 + S/T))}`. -/
noncomputable def Phi (d : ℝ) (T S : ℕ) : ℝ :=
  min (T : ℝ) (psi (Real.log (2 + d) / (1 + (S : ℝ) / (T : ℝ))))

/-- `Ψ(d, T) = Φ(d, T, 0)`. -/
noncomputable def Psi (d : ℝ) (T : ℕ) : ℝ := Phi d T 0

/-- `Λ(d, T) = min{T, log(2 + d)}`. -/
noncomputable def Lam (d : ℝ) (T : ℕ) : ℝ := min (T : ℝ) (Real.log (2 + d))

end AvgValueAlloc


