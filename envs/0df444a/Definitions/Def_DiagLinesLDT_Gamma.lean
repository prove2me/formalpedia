-- Prove2me | Definitions.Def_DiagLinesLDT_Gamma
-- name    : DiagLinesLDT_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:59.97086+00:00
-- url     : https://prove2.me/theorems/1f08ddb7-8ca3-42ad-8eb1-1a3c6b59eee1
-- title:
--   Maximally entangled state $|\Phi\rangle$ and commutator energy $\Gamma(u,v)$
-- statement:
--   On $\mathbb C^\iota\otimes\mathbb C^\iota$, the **maximally entangled state** is
--
--   $$|\Phi\rangle=\frac{1}{\sqrt{\dim\mathcal H}}\sum_{z\in\iota}|z\rangle\otimes|z\rangle.$$
--
--   For a family $\{A^u_a\}$ of operators on $\mathbb C^\iota$,
--
--   $$\Gamma(u,v):=\sum_{a,b}\big\|([A^u_a,A^v_b]\otimes I)|\Phi\rangle\big\|^2$$
--
--   measures how far the families $A^u$ and $A^v$ are from commuting. Its average over $u,v$ controls the distance from global consistency.
--
--   **Formalization Note** The source has $\iota=\mathbb F_q^3$ and its own point measurements. The definition is stated for any family, since the inequality of Theorem 6.4 is about any projective family.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4.1, p.6, and §6, p.16

import Mathlib

open scoped Kronecker

namespace DiagLinesLDT

/-- The maximally entangled state `|Φ⟩ = (dim H)^{-1/2} Σ_z |z⟩ ⊗ |z⟩` on `ℂ^ι ⊗ ℂ^ι`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §4.1, p.6. -/
noncomputable def maxEnt (ι : Type*) [Fintype ι] [DecidableEq ι] : ι × ι → ℂ :=
  fun z => if z.1 = z.2 then ((Real.sqrt (Fintype.card ι) : ℝ) : ℂ)⁻¹ else 0

/-- `Γ(u, v) := Σ_{a,b} ‖([A^u_a, A^v_b] ⊗ I) |Φ⟩‖²` for a family `A` of operators on `ℂ^ι`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §6, p.16.

**Formalization Note** The source defines `Γ` for its point measurements on `ℂ^{𝔽_q³}`; the definition
is stated for any family, with `U` the question set and `Ans` the answer set. -/
noncomputable def Gamma {U Ans ι : Type*} [Fintype Ans] [Fintype ι] [DecidableEq ι]
    (A : U → Ans → Matrix ι ι ℂ) (u v : U) : ℝ :=
  ∑ a, ∑ b, ∑ x : ι × ι,
    ‖(((A u a * A v b - A v b * A u a) ⊗ₖ (1 : Matrix ι ι ℂ)).mulVec (maxEnt ι)) x‖ ^ 2

end DiagLinesLDT


