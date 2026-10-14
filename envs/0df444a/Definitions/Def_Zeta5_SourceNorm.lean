-- Prove2me | Definitions.Def_Zeta5_SourceNorm
-- name    : Zeta5_SourceNorm
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T14:19:23.956147+00:00
-- url     : https://prove2.me/theorems/cb2cc3c0-15fa-424f-aa7c-d6a4a2af64ec
-- title:
--   Zeta5: the normaliser $m_K$ (source `Apery/Norm.lean`)
-- statement:
--   The normaliser $m_K = \prod_{p \le 2h} p^{-L_p}$ of the source project `mo271/Zeta5`, module `Apery/Norm.lean`. For every prime $p \le 2h$ the local exponent $L_p$ is one of the proved lower bounds for $v_p^G(F_K)$:
--
--   * small primes $p\,M \le K$ (with $M = 400$): the bound (3.12), $L = -6h\,\lfloor\log_p(200n)\rfloor - h\,v_p(24)$;
--
--   * inner range $K < pM$, $3p \le K$ (when the side conditions `InnerOK` hold): $v_p(S_K) + \lfloor 2 \sum wcap\rfloor$ for the water-filling allocation;
--
--   * outer range $K < 3p \le 3h$ (when `OuterOK` holds): $v_p(S_K) + \lfloor \sum w_O - r\rfloor$;
--
--   falling back to (3.12) otherwise. Here $K = 40n$, $N = 3n$, $h = 37n$. The two main results about these objects — $m_K F_K \in \mathbb{Z}[X]$ for $n \ge 1$ and $\log m_K \le (A_{\mathrm{eff}}+\varepsilon)K^2$ eventually — are separate platform theorems. **Formalization Note** Nothing is proved in this module; the declarations are the definitions of the source, reproduced verbatim in the `Apery` namespace.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Norm.lean#L26-L93

import Mathlib
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceConstruction

/-!
# The normaliser `mN` (source `Apery/Norm.lean`)

The definitions of `Apery/Norm.lean` of the source project `mo271/Zeta5`
(commit `7fe736760f4b96bfdb4334b68e3b3124ecbe10b0`): the cutoff `Mcut`, the local exponent
`Lp` (small primes, water-filling inner allocation, outer allocation) and the normaliser

$$m_K = \prod_{p \le 2h} p^{-L_p}, \qquad K = 40n,\ h = 37n,$$

whose local exponents are one of the proved lower bounds for `v_p^G(F_K)`
(small primes `p M ≤ K`: the bound (3.12); inner range `K < pM`, `3p ≤ K`: the water-filling
allocation; outer range `K < 3p`: the outer allocation).

The main results about these objects (`integral_mN`, `growth_mN`) are stated as separate
platform theorems. Nothing is proved in this module; the definitions are reproduced verbatim
from the source.
-/

open Finset Polynomial

namespace Apery

/-- The cutoff `M` separating small primes from the inner range. -/
def Mcut : ℕ := 400

/-- `v_p(S_K)`. -/
noncomputable def vSK (n p : ℕ) : ℤ := padicValRat p (S n)

/-- The small-prime exponent (3.12). -/
noncomputable def Lsmall (n p : ℕ) : ℤ :=
  -(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℤ) + (37 * n : ℕ) * (padicValNat p 24 : ℤ))

/-- The class offsets `β_c = 6 ℓ_N(c) - ℓ_K(c) - 4`. -/
noncomputable def betaI (n p : ℕ) {m : ℕ} (c : Fin (m + 1)) : ℤ :=
  6 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) -
    (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - 4

/-- The water-filling parameters. -/
def kloI (n p : ℕ) : ℤ := -2 * ((40 * n / p : ℕ) : ℤ) - 6

def ktopI (n p : ℕ) : ℤ := 8 * ((40 * n / p : ℕ) : ℤ) + 20

def L0I (n p : ℕ) : ℕ := 3 * (40 * n / p) + 6

/-- The inner allocation. -/
noncomputable def allocI (n p m : ℕ) : Fin (m + 1) → ℕ :=
  allocK (betaI n p (m := m)) (37 * n)
    (kfSel (betaI n p (m := m)) (37 * n) (L0I n p) (kloI n p) (ktopI n p))

/-- The side conditions of the inner bound. -/
def InnerOK (n p : ℕ) : Prop :=
  ∃ _hm : 2 * (p / 2) + 1 = p, ∃ hm1 : 1 ≤ p / 2, 5 ≤ p ∧ Sep p (PlK (40 * n)) ∧ 40 * n < p ^ 2 ∧
    5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2 ∧
    ∑ c, allocI n p (p / 2) c = 37 * n ∧
    tmin hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) ≤
      2 * (allocI n p (p / 2) 0 : ℚ) + (Bse p (40 * n) (3 * n) 0 - 4) / 2

/-- The inner weight sum (for `m = p / 2`). -/
noncomputable def WI (n p : ℕ) : ℚ :=
  if hm1 : 1 ≤ p / 2 then
    ∑ s, wcap hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) s
  else 0

/-- The side conditions of the outer bound. -/
def OuterOK (n p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ 7 ≤ p ∧ 40 * n < 3 * p ∧ 2 * (40 * n) < p ^ 2 ∧ 3 * n < p

/-- The outer weight sum minus the rank loss (for `m = p / 2`). -/
noncomputable def WO (n p : ℕ) : ℚ :=
  if hpp : p.Prime then
    if hm : 2 * (p / 2) + 1 = p then
      haveI : Fact p.Prime := ⟨hpp⟩
      2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)
    else 0
  else 0

open Classical in
/-- **The local exponent.** -/
noncomputable def Lp (n p : ℕ) : ℤ :=
  if p * Mcut ≤ 40 * n then Lsmall n p
  else if 3 * p ≤ 40 * n then
    (if InnerOK n p then vSK n p + ⌊2 * WI n p⌋ else Lsmall n p)
  else (if OuterOK n p then vSK n p + ⌊WO n p⌋ else Lsmall n p)

open Classical in
/-- **The normaliser** `m_K = ∏_{p ≤ 2h} p^{-L_p}`. -/
noncomputable def mN (n : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime, (p : ℚ) ^ (-Lp n p)

end Apery


