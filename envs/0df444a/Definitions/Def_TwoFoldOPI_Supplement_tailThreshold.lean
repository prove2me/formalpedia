-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_tailThreshold
-- name    : TwoFoldOPI_Supplement_tailThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:51:12.435771+00:00
-- url     : https://prove2.me/theorems/7754ead5-32d0-4fa4-b7cf-d06143c4bfbc
-- title:
--   Tail thresholds $\tau_r$ and the weighted tail threshold $\tau$
-- statement:
--   For a set $B\subseteq\mathbb Z_{\ge0}$ the **tail threshold** is
--   $$\tau(B)=\min\{t\in\mathbb Z_{\ge0}:\{t,t+1,\dots\}\subseteq B\},$$
--   with $\tau(B)=\infty$ if no such $t$ exists. For load data $B_1,\dots,B_R$ with weights $\alpha_1,\dots,\alpha_R$ the **weighted tail threshold** is $\tau=\sum_r\alpha_r\tau(B_r)\in[0,\infty]$.
--
--   The weighted tail threshold bounds the rates for which classical provers fail (Theorems 11.9, 11.10).
--
--   **Formalization Note** $\tau(B)\in\mathbb N\cup\{\infty\}$ and $\tau\in[0,\infty]$; one infinite $\tau(B_r)$ with $\alpha_r>0$ makes $\tau=\infty$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.2, Definition 11.5, p. 59

import Mathlib

namespace TwoFoldOPI

namespace Supplement

open Classical in
/-- **Tail thresholds `τ_r` and the weighted tail threshold `τ`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.2, Definition 11.5, p.59: "For load data B_1, …, B_R and α_1, …, α_R, the tail
threshold of B_r is τ_r := min{t ∈ Z_{≥0} : {t, t + 1, …} ⊆ B_r}, with τ_r = ∞ if the set on the
right is empty. The weighted tail threshold is τ = Σ_{r∈[R]} α_r τ_r ∈ [0, ∞]."

`tailThreshold B` is the least `t` with `{t, t+1, …} ⊆ B`, or `⊤ = ∞` if there is none.

**Formalization Note.** `τ_r ∈ ℕ∞`; the weighted threshold `weightedTail` is computed in
`[0, ∞] = ℝ≥0∞` with weights `α_r` (positive in every use), so one infinite `τ_r` makes `τ = ∞`. -/
noncomputable def tailThreshold (B : Set ℕ) : ℕ∞ :=
  if h : ∃ t : ℕ, ∀ k : ℕ, t ≤ k → k ∈ B then (Nat.find h : ℕ∞) else ⊤

/-- The weighted tail threshold `τ = Σ_r α_r τ_r ∈ [0, ∞]` (Definition 11.5, p.59). -/
noncomputable def weightedTail {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) : ENNReal :=
  ∑ r, ENNReal.ofReal (α r) * ((tailThreshold (B r) : ℕ∞) : ENNReal)

end Supplement

end TwoFoldOPI


