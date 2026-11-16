-- Prove2me | Definitions.Def_DecDynMatch_Supplement_confSet
-- name    : DecDynMatch_Supplement_confSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:32.236706+00:00
-- url     : https://prove2.me/theorems/f45017e7-1bb8-4f20-9b8e-66d918d3b314
-- title:
--   Empirical means, confidence radii and the confidence set $C_a(Q)$ (47)–(48)
-- statement:
--   An owner (a player comparing arms, or an arm comparing proposers) with local clock $a$, sample counts $N_x$ and utility sums $U_x$ computes
--   $$
--   \hat\theta_x=\begin{cases}U_x/N_x,&N_x>0,\\0,&N_x=0,\end{cases}\qquad B(a)=5\log_2(a+2),\qquad \beta_a(x,z)=\sqrt{\frac{B(a)}{2}\Bigl(\frac1{N_x}+\frac1{N_z}\Bigr)},
--   $$
--   with $\beta_a(x,z)=+\infty$ if either count is zero. For a finite set $Q$, the options not ruled out as best are
--   $$
--   C_a(Q)=\{x\in Q:\ \hat\theta_z-\hat\theta_x\le\beta_a(z,x)\ \text{for every } z\in Q\}.
--   $$
--
--   **Formalization Note** The logarithm is base two (`Real.logb 2`), as in the appendix. The infinite radius is encoded by the disjunction "$N_z=0$ or $N_x=0$ or the inequality holds".
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, eqs. (47)–(48), p.31

import Mathlib

namespace DecDynMatch.Supplement

/-- The confidence level `B(a) = 5 log₂(a + 2)` of eq. (47), p.31 ("We use base-two logarithms
throughout this appendix"). -/
noncomputable def Bconf (a : ℕ) : ℝ := 5 * Real.logb 2 ((a : ℝ) + 2)

/-- The empirical mean `θ̂ₓ = Uₓ/Nₓ` if `Nₓ > 0` and `0` if `Nₓ = 0` (eq. (47), p.31). -/
noncomputable def thetaHat {α : Type*} (N : α → ℕ) (U : α → ℝ) (x : α) : ℝ :=
  if N x = 0 then 0 else U x / (N x : ℝ)

/-- The pairwise comparison of `x` against `z` does not rule `x` out:
`θ̂_z − θ̂_x ≤ β_a(z, x)`, with `β_a(z, x) = √(B(a)/2 · (1/N_z + 1/N_x))` and
`β_a(z, x) = +∞` if either count is zero (eq. (47), p.31). -/
def NotRuledOut {α : Type*} (a : ℕ) (N : α → ℕ) (U : α → ℝ) (z x : α) : Prop :=
  N z = 0 ∨ N x = 0 ∨
    thetaHat N U z - thetaHat N U x ≤
      Real.sqrt (Bconf a / 2 * (1 / (N z : ℝ) + 1 / (N x : ℝ)))

open Classical in
/-- **The confidence set `C_a(Q)`.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), App. C.1, eqs. (47)–(48), p.31: "Using its own local
clock a and observations through the previous round, each side computes θ̂ₓ = Uₓ/Nₓ (Nₓ > 0), 0
(Nₓ = 0), B(a) = 5 log(a + 2), β_a(x, z) = √(B(a)/2 (1/Nₓ + 1/N_z)). … If either count is zero,
set β_a(x, z) = +∞. For a nonempty set Q, the options that the pairwise confidence comparisons
have not ruled out as best are C_a(Q) = {x ∈ Q : θ̂_z − θ̂ₓ ≤ β_a(z, x) for every z ∈ Q}."

`confSet a N U Q` is computed from an owner's local clock `a`, its sample counts `N` and its
utility sums `U` (a player over arms, or an arm over proposers).

**Formalization Note.** The logarithm in `B(a)` is `Real.logb 2` (base two, as the appendix
states). On an empty `Q` the set is empty (the protocol only uses nonempty `Q`). -/
noncomputable def confSet {α : Type*} (a : ℕ) (N : α → ℕ) (U : α → ℝ) (Q : Finset α) :
    Finset α :=
  Q.filter (fun x => ∀ z ∈ Q, NotRuledOut a N U z x)

end DecDynMatch.Supplement


