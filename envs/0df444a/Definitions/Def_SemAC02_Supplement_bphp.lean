-- Prove2me | Definitions.Def_SemAC02_Supplement_bphp
-- name    : SemAC02_Supplement_bphp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:42:30.72006+00:00
-- url     : https://prove2.me/theorems/b4e5c747-638e-4ad8-8831-94cf2c422ee8
-- title:
--   The bit pigeonhole principle BPHP^m_n
-- statement:
--   Let $n=2^\ell$ and $m>n$. The **bit pigeonhole principle** $\mathrm{BPHP}^m_n$ has variables $y_{u,t}$ for pigeons $u\in[m]$ and bit positions $t\in[\ell]$. For a hole address $a\in\{0,1\}^\ell$ put
--
--   $$
--   \delta_a(y_u)=\prod_{t=1}^{\ell}\bigl(a_ty_{u,t}+(1-a_t)(1-y_{u,t})\bigr),
--   $$
--
--   the indicator that pigeon $u$ is mapped to hole $a$. The polynomial encoding over $\mathbb F_2$ consists of the equations $\delta_a(y_u)\delta_a(y_{u'})=0$ for all $u\neq u'$ and all $a$, the encodings of the collision clauses $D_{u,u',a}$. No pigeon axioms are needed.
--
--   Theorems 3.2 and 3.7 are lower bounds for this system.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 3.1, p.20 (PDF p.22)

import Mathlib

namespace SemAC02.Supplement

open MvPolynomial

/-- `δ_a(y_u) = ∏_{t=1}^{ℓ} (a_t y_{u,t} + (1 − a_t)(1 − y_{u,t}))` (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), Definition 3.1, p.20): the indicator that pigeon `u` is mapped to the hole with
address `a ∈ {0,1}^ℓ`. The factor is `y_{u,t}` when `a_t = 1` and `1 − y_{u,t}` when `a_t = 0`. -/
noncomputable def deltaA {m ℓ : ℕ} (u : Fin m) (a : Fin ℓ → Bool) :
    MvPolynomial (Fin m × Fin ℓ) (ZMod 2) :=
  ∏ t : Fin ℓ, (if a t then X (u, t) else 1 - X (u, t))

/-- The **bit pigeonhole principle** `BPHP^m_n` over `𝔽₂`, `n = 2^ℓ` (Definition 3.1, p.20): the
variables `y_{u,t}` (`u ∈ [m]`, `t ∈ [ℓ]`) and the equations `δ_a(y_u) δ_a(y_{u'}) = 0` for all
pigeons `u ≠ u'` and hole addresses `a ∈ {0,1}^ℓ`, the polynomial encodings of the collision
clauses `D_{u,u',a}`. -/
noncomputable def bphp (m ℓ : ℕ) : Set (MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) :=
  {p | ∃ (u u' : Fin m) (a : Fin ℓ → Bool), u ≠ u' ∧ p = deltaA u a * deltaA u' a}

end SemAC02.Supplement


