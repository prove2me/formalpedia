-- Prove2me | Definitions.Def_DSICHardRev_GSDomain
-- name    : DSICHardRev_GSDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:24.891864+00:00
-- url     : https://prove2.me/theorems/29050103-fb10-408a-9f5e-3e28930b50b5
-- title:
--   The value range $R$ and the domain of monotone gross-substitutes valuations with values in $R$
-- statement:
--   Fix $m$ items $[m]$. The **value range** is
--   $$R=\{2^{s/2}\,t/m \;:\; s\in[-2^m,2^m]\cap\mathbb Z,\ t\in[0,m^5]\cap\mathbb Z\}.$$
--   A valuation $v:2^{[m]}\to\mathbb R$ is **gross substitutes** (GS) in the sense of Kelso and Crawford if, for all real price vectors $p\le p'$ and every bundle $C$ demanded at $p$ (maximizing $v(C)-\sum_{j\in C}p_j$), some bundle demanded at $p'$ contains every item of $C$ whose price did not change.
--
--   The domain $\mathcal D_{GS}(m)$ consists of the valuations $v$ on $[m]$ that are monotone non-decreasing, take every value $v(S)$ in $R$ (in particular $v\ge 0$), and are gross substitutes.
--
--   This is the valuation class over which Theorem 1.1 measures deterministic DSIC mechanisms.
--
--   **Formalization Note** The paper does not define GS; the published Kelso–Crawford definition `KelsoCrawford.OneSided.GrossSubstitutesOn v Set.univ` is used, with all real price vectors allowed. $v(\emptyset)=0$ is not required, as the paper does not require it.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.1, p.8 (the range R); §2.3, p.9 (valuations are monotone); §1.2, p.3 (GS valuations in Theorem 1.1)

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model

namespace DSICHardRev

/-!
# The value range `R` and the domain of the goal: monotone gross-substitutes valuations with values in `R`

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…): the range `R`, §2.1, p.8; valuations are monotone,
§2.3, p.9; gross substitutes (GS), used throughout and in Theorem 1.1, p.3.

**Formalization Note.**
* `Rset m = {2^{s/2} · t / m : s ∈ ℤ ∩ [−2^m, 2^m], t ∈ ℤ ∩ [0, m^5]}` exactly as printed on p.8;
  the exponent `s/2` is a real exponent (`Real.rpow`).
* Gross substitutes is not defined in the paper; the standard Kelso–Crawford definition is used,
  through the published `KelsoCrawford.OneSided.GrossSubstitutesOn v Set.univ`: for all real price
  vectors `p ≤ p'` and every bundle `C` demanded at `p`, some bundle demanded at `p'` contains the
  items of `C` whose price did not change. All real price vectors are allowed.
* `DGS m` is the domain of Theorem 1.1 on the item set `Fin m` (all `m` items): valuations that are
  monotone, take every value in `Rset m` (hence are non-negative) and are GS. `v ∅ = 0` is not
  required, as the paper does not require it.
-/

/-- The value range `R = {2^{s/2} t/m : s ∈ [−2^m, 2^m] ∩ ℤ, t ∈ [0, m^5] ∩ ℤ}` (p.8). -/
def Rset (m : ℕ) : Set ℝ :=
  {x | ∃ s t : ℤ, -(2 : ℤ) ^ m ≤ s ∧ s ≤ (2 : ℤ) ^ m ∧ 0 ≤ t ∧ t ≤ (m : ℤ) ^ 5 ∧
    x = (2 : ℝ) ^ ((s : ℝ) / 2) * (t : ℝ) / (m : ℝ)}

/-- The domain of Theorem 1.1: monotone gross-substitutes valuations on the items `Fin m` with every
value in `Rset m`. -/
def DGS (m : ℕ) : Set (Finset (Fin m) → ℝ) :=
  {v | Monotone v ∧ (∀ S, v S ∈ Rset m) ∧ KelsoCrawford.OneSided.GrossSubstitutesOn v Set.univ}

end DSICHardRev


