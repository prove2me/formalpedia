-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_logVolSdp
-- name    : MinVolEllipsoid_Supplement_logVolSdp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:31:23.17834+00:00
-- url     : https://prove2.me/theorems/13de4c6c-e5fd-5347-b218-c789f9772059
-- title:
--   Optimal value of the SDP (12), $\log\mathrm{Vol}(\mathcal E_{\mathrm{sdp}})$
-- statement:
--   For the polytope data $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, the SDP (12) is
--
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & -\log\det(A)\\
--   \text{subject to}\quad & A\in\mathbb S^K,\ b\in\mathbb R^K,\ N\in\mathbb R^{J\times J}_+,\ F\in\mathbb S^K,\ g\in\mathbb R^K,\ h\in\mathbb R,\\
--   & \text{(11) holds.}
--   \end{aligned}
--   $$
--
--   This definition is its optimal value, an extended real number, with $A$ ranging over positive definite matrices (the domain of $-\log\det$). If $(A,b,\dots)$ is optimal, the paper sets $\mathcal E_{\mathrm{sdp}}=\mathcal E(A,b)$; with the volume convention $\mathrm{Vol}(\mathcal E(A,b))=1/\det A$ of p.5, this value is $\log\mathrm{Vol}(\mathcal E_{\mathrm{sdp}})$.
--
--   **Formalization Note** The value lives in `EReal`: an infeasible problem gives $+\infty$ and an unbounded one $-\infty$, so no junk value of a real infimum enters. The constraints (11) are `MinVolEllipsoid.Supplement.Cond11`.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, display (12) and the definition of ℰ_sdp, p.11; Vol convention, p.5

import Mathlib
import Definitions.Def_MinVolEllipsoid_Supplement_Cond11

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The optimal value of the SDP (12), `log Vol(ℰ_sdp)`** (Mittal & Hanasusanto,
arXiv:1807.07507v4, display (12), p.11; volume convention `Vol(ℰ(A, b)) = 1/det(A)`, p.5).

`logVolSdp S t` is

`inf { −log det(A) : A ∈ 𝕊ᴷ, b ∈ ℝᴷ, N ∈ ℝ^{J×J}_+, F ∈ 𝕊ᴷ, g ∈ ℝᴷ, h ∈ ℝ, (11) holds }`,

the infimum taken over `A` positive definite (the domain of `−log det`). For an optimal solution
`(A, b, …)` of (12), `ℰ_sdp = ℰ(A, b)` and `log Vol(ℰ_sdp) = −log det(A)` is this value.

**Formalization Note** The value is in `EReal`, so an empty feasible set gives `⊤` and an unbounded
one `⊥`; no junk value of a real `sInf` enters. `A ∈ 𝕊ᴷ` together with the domain of `−log det` is
`A.PosDef` (Mathlib's `PosDef` includes symmetry). The constraints (11) are `Cond11`. -/
noncomputable def logVolSdp {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ) : EReal :=
  ⨅ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (N : Matrix (Fin m) (Fin m) ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (h : ℝ)
    (_ : A.PosDef ∧ Cond11 S t A b N F g h), ((-Real.log A.det : ℝ) : EReal)

end MinVolEllipsoid.Supplement


