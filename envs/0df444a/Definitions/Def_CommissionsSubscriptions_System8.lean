-- Prove2me | Definitions.Def_CommissionsSubscriptions_System8
-- name    : CommissionsSubscriptions_System8
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:10.930757+00:00
-- url     : https://prove2.me/theorems/a8ca6b62-3158-44b9-8cb8-35b996b09960
-- title:
--   System (8) for a price vector $p$
-- statement:
--   Given fees $(\gamma,\mu)$, a flow $\bar x$ and a supply-demand vector $(\bar q^s,\bar q^b)$, let
--   $\tilde\gamma^s_i=\frac1{1-\gamma^s_i}$, $\tilde\mu^s_i=\frac{\mu^s_i}{1-\gamma^s_i}$, $\tilde\gamma^b_j=\frac1{1+\gamma^b_j}$, $\tilde\mu^b_j=\frac{\mu^b_j}{1+\gamma^b_j}$.
--   A price vector $p$ satisfies **system (8)** if
--
--   1. (8a) $p_i-\tilde\mu^s_i-F^{-1}_{s_i}(\bar q^s_i/s_i)\,\tilde\gamma^s_i=0$ for all $i$ with $\bar q^s_i>0$;
--   2. (8b) $p_i-\tilde\mu^s_i\le0$ for all $i$ with $\bar q^s_i=0$;
--   3. (8c) $p_i+\tilde\mu^b_j+c_i\tilde\gamma^b_j-F^{-1}_{b_j}(1-\bar q^b_j/b_j)\,\tilde\gamma^b_j=0$ for all $(i,j)\in E$ with $\bar x_{ij}>0$;
--   4. (8d) the same expression is $\ge0$ for all $(i,j)\in E$ with $\bar x_{ij}=0$;
--   5. (8e) $\tilde\gamma^s_i\ge1$, $\tilde\mu^s_i\ge0$, $p_i\ge0$; (8f) $\tilde\gamma^b_j\ge0$, $\tilde\gamma^b_j\le1$, $\tilde\mu^b_j\ge0$.
--
--   Theorem 1(ii) characterizes the optimal fees by the solvability of this system, which is linear in $(p,\tilde\gamma,\tilde\mu)$.
--
--   **Formalization Note** The $F^{-1}$ terms are extended reals: (8a) and (8c) are written "expression $=F^{-1}\tilde\gamma$" and (8d) "$F^{-1}\tilde\gamma\le$ expression"; these agree with the printed form for finite values and are false, like the printed form, when the $F^{-1}$ term is $+\infty$. The theorems using the system assume $\gamma^s_i<1$ and $\gamma^b_j\ge0$, so the divisions are by nonzero numbers.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Theorem 1(ii), (8a)–(8f), p. 13

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Fees
import Definitions.Def_CommissionsSubscriptions_Finv

namespace CommissionsSubscriptions

/-- **The system (8) in the price vector `p`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Theorem 1(ii), (8a)–(8f), p. 13. With
`γ̃^s_i = 1/(1 − γ^s_i)`, `µ̃^s_i = µ^s_i/(1 − γ^s_i)`, `γ̃^b_j = 1/(1 + γ^b_j)`,
`µ̃^b_j = µ^b_j/(1 + γ^b_j)`, and a flow `x̄` and supply-demand vector `(q̄^s, q̄^b)`:
* (8a) `p_i − µ̃^s_i − F⁻¹_{s_i}(q̄^s_i/s_i) γ̃^s_i = 0` for all `i` with `q̄^s_i > 0`;
* (8b) `p_i − µ̃^s_i ≤ 0` for all `i` with `q̄^s_i = 0`;
* (8c) `p_i + µ̃^b_j + c_i γ̃^b_j − F⁻¹_{b_j}(1 − q̄^b_j/b_j) γ̃^b_j = 0` for all `(i,j)` with
  `x̄_{ij} > 0`;
* (8d) the same expression `≥ 0` for all `(i,j)` with `x̄_{ij} = 0`;
* (8e) `γ̃^s_i ≥ 1`, `µ̃^s_i ≥ 0`, `p_i ≥ 0`; (8f) `γ̃^b_j ≥ 0`, `γ̃^b_j ≤ 1`, `µ̃^b_j ≥ 0`.

**Formalization Note.** The `F⁻¹` terms are `EReal` (Reading 1), so "`a − F⁻¹·γ̃ = 0`" is
written `a = F⁻¹·γ̃` and "`a − F⁻¹·γ̃ ≥ 0`" as `F⁻¹·γ̃ ≤ a`; these agree with the printed form on
finite values, and when the `F⁻¹` term is `+∞` both the printed and the Lean form are false.
The pairs `(i,j)` in (8c)/(8d) range over `E`. The divisions are the paper's; the theorems using
`System8` assume `γ^s_i < 1` (as Theorem 1(ii) does) and `γ^b_j ≥ 0`, so no denominator is `0`. -/
noncomputable def System8 {S B : Type} (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ)
    (qb : B → ℝ) (f : Fees S B) (p : S → ℝ) : Prop :=
  let gts : S → ℝ := fun i => 1 / (1 - f.gs i)
  let mts : S → ℝ := fun i => f.ms i / (1 - f.gs i)
  let gtb : B → ℝ := fun j => 1 / (1 + f.gb j)
  let mtb : B → ℝ := fun j => f.mb j / (1 + f.gb j)
  (∀ i, 0 < qs i →
      ((p i - mts i : ℝ) : EReal) = Finv (M.Fs i) (qs i / M.s i) * ((gts i : ℝ) : EReal)) ∧
    (∀ i, qs i = 0 → p i - mts i ≤ 0) ∧
    (∀ e ∈ M.E, 0 < x e.1 e.2 →
      ((p e.1 + mtb e.2 + M.c e.1 * gtb e.2 : ℝ) : EReal) =
        Finv (M.Fb e.2) (1 - qb e.2 / M.b e.2) * ((gtb e.2 : ℝ) : EReal)) ∧
    (∀ e ∈ M.E, x e.1 e.2 = 0 →
      Finv (M.Fb e.2) (1 - qb e.2 / M.b e.2) * ((gtb e.2 : ℝ) : EReal) ≤
        ((p e.1 + mtb e.2 + M.c e.1 * gtb e.2 : ℝ) : EReal)) ∧
    (∀ i, 1 ≤ gts i ∧ 0 ≤ mts i ∧ 0 ≤ p i) ∧
    (∀ j, 0 ≤ gtb j ∧ gtb j ≤ 1 ∧ 0 ≤ mtb j)

end CommissionsSubscriptions


