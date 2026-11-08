-- Prove2me | Definitions.Def_CausalFailureRank_coefficient
-- name    : CausalFailureRank_coefficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:09.835952+00:00
-- url     : https://prove2.me/theorems/802c1b1f-0765-4a36-bfc1-96c5b2ea39b1
-- title:
--   Information weights $A_i$, coefficient $C(i,R)$ and iterated logarithms $\ell_j$
-- statement:
--   With natural logarithms, $D_{ix}=\mathrm{KL}(P_i^x\,\|\,P_i^{1-x})$, the **information weight** is
--   $$A_i=c_i\sum_{x=0}^{1}\frac{\pi_i(x)}{D_{ix}},$$
--   and $\ell_1(z)=\log z$, $\ell_{j+1}(z)=\log\ell_j(z)$. The **coefficient** is $C(i,R)=0$ at infinite-rank states, and at a finite-rank state $d=\rho(i,R)$, with $d_g=\rho(i+1,R)$,
--   $$C(i,R)=\mathbf 1\{d_g=d\}\,C(i+1,R)+\mathbf 1\{d_b+1=d\}\,A_i.$$
--   This is the leading constant of the price law.
--
--   **Formalization Note** Both indicators can fire, and then the terms add. The recursion is on the number of remaining stages, so it is well founded. $\ell_j$ is $\log$ iterated $j$ times, and is meaningful at large arguments only.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.5; §3.1, eq. (2), p.6

import Mathlib
import Definitions.Def_CausalFailureRank_Instance
import Definitions.Def_CausalFailureRank_rank

namespace CausalFailureRank

variable {N q : ℕ}

/-- The rank of an instance, `ρ(i, R)`: the game rank of its compatibility sets. -/
noncomputable def rank (I : Instance N q) (i : ℕ) (R : Finset (Fin q)) : ℕ∞ :=
  gameRank I.S i R

/-- `d_b(i, R)` of eq. (1), p.6, for an instance. -/
noncomputable def db (I : Instance N q) (i : Fin N) (R : Finset (Fin q)) : ℕ∞ :=
  gameBadRank I.S i R

/-- `D_ix = KL(P_i^x ‖ P_i^{1-x})`, natural logarithm. Zang, Li, Jin, Xu, *Causal Failure Rank
Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256
721c8b0d…), §2, p.5.

**Formalization Note.** The alphabet is finite and both laws have full support, so the sum and each
logarithm's argument are genuine. -/
noncomputable def D (I : Instance N q) (i : Fin N) (x : Bool) : ℝ :=
  ∑ y, (I.P i x y).toReal * Real.log ((I.P i x y).toReal / (I.P i (!x) y).toReal)

/-- The information weight `A_i = c_i Σ_x π_i(x) / D_ix`, §2, p.5. `π_i(x)` is paired with
`D_ix = KL(P_i^x ‖ P_i^{1-x})`. -/
noncomputable def A (I : Instance N q) (i : Fin N) : ℝ :=
  I.c i * (I.prior i / D I i true + (1 - I.prior i) / D I i false)

open scoped Classical in
/-- **The coefficient `C(i, R)` of eq. (2), p.6.** `0` at infinite-rank states, otherwise at
`d = ρ(i, R)`: `C(i, R) = 1{d_g = d} C(i+1, R) + 1{d_b + 1 = d} A_i`.

**Formalization Note.** Both indicators can fire, and then the terms add. `i ≥ N` has rank `⊤`, so
`C = 0` there; the recursion is on `N - i`. -/
noncomputable def C (I : Instance N q) (i : ℕ) (R : Finset (Fin q)) : ℝ :=
  if h : i < N then
    if rank I i R = ⊤ then 0
    else
      (if rank I (i + 1) R = rank I i R then C I (i + 1) R else 0) +
        (if db I ⟨i, h⟩ R + 1 = rank I i R then A I ⟨i, h⟩ else 0)
  else 0
termination_by N - i
decreasing_by omega

/-- The iterated natural logarithm: `iterLog 1 z = log z = ℓ₁(z)`, `iterLog (j + 1) z = ℓ_{j+1}(z)`,
§2, p.5.

**Formalization Note.** Used for `j ≥ 1`, at sufficiently large arguments only: `Real.log` is total,
so claims about it live under `∀ᶠ`. -/
noncomputable def iterLog (j : ℕ) (z : ℝ) : ℝ := Real.log^[j] z

end CausalFailureRank


