-- Prove2me | Definitions.Def_DynStrings_Supplement_CollParams
-- name    : DynStrings_Supplement_CollParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:50:17.887272+00:00
-- url     : https://prove2.me/theorems/ac40c9fb-9ab0-44e3-be40-d3b8716a35d2
-- title:
--   Collection space parameters $L_{\mathcal W},\delta(\mathcal W),\sigma_{\mathcal W},\Delta_{\mathcal W},D_{\mathcal W}$ (Definition 3.1) and the tail scale $\tau(m,\eta)$ (Eq. (3))
-- statement:
--   For a finite collection (multiset) $\mathcal W$ of non-empty strings (Definition 3.1):
--
--   1. $L_{\mathcal W}=\sum_{Z\in\mathcal W}(|Z|+1)$, the length of the collection written with a separator after each member;
--   2. $d_m(\mathcal W)$ is the number of distinct length-$m$ substrings of members of $\mathcal W$ (substrings never cross members), and $\delta(\mathcal W)=\max_{m\ge1}d_m(\mathcal W)/m$;
--   3. $\sigma_{\mathcal W}=d_1(\mathcal W)$ and $\Delta_{\mathcal W}=\max(|\mathcal W|,\delta(\mathcal W))$, where $|\mathcal W|$ counts members with multiplicity;
--   4. $D_{\mathcal W}=\Delta_{\mathcal W}\,\lg\Big(\dfrac{L_{\mathcal W}\log\sigma_{\mathcal W}}{\Delta_{\mathcal W}\log L_{\mathcal W}}\Big)$ if $\mathcal W\neq\emptyset$, and $D_\emptyset=0$.
--
--   For $m\ge0$ and $0<\eta<1$, the tail scale (Equation (3)) is
--
--   $$\tau(m,\eta)=\lg m+\frac{\log(1/\eta)}{\lg\big(\log(1/\eta)/\lg m\big)}.$$
--
--   Here $\log$ is base 2 and $\lg x=\log\max\{2,x\}$. These parameters state the space and time bounds of the dynamic data structure (Theorem 6.1).
--
--   **Formalization Note** Collections are `Multiset (List α)`; $\delta(\mathcal W)$ is the maximum over $1\le m\le\max(1,\text{longest member})$, beyond which $d_m(\mathcal W)=0$, and is $0$ for the empty collection. $\lg$ is the published base `lg`; since $\lg\ge1$, no denominator vanishes.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Definition 3.1, p.14 (PDF p.15); Equation (3), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_DynStrings_Strings

namespace DynStrings.Supplement

/-!
# Collection space parameters and the tail scale

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), Definition 3.1, p.14 (collection space parameters `L_W`, `δ(W)`, `σ_W`, `Δ_W`,
`D_W`) and Equation (3), p.20 (the tail scale `τ(m, η)`).

**Formalization Note.**
* A collection is a finite multiset `Multiset (List α)`; `|W|` is `Multiset.card W` (members
  counted with multiplicity). A substring of a collection is a substring of one of its members
  (`subsColl`, published base definition `DynStrings.Strings`), so substrings never cross members.
* `δ(W) = max_{m ≥ 1} d_m(W)/m` is computed as the maximum over `1 ≤ m ≤ max(1, longest member)`
  (`maxRatio`); `d_m(W) = 0` beyond the longest member, so this is the paper's maximum. It is `0`
  for `W = ∅`.
* `log` is `Real.logb 2` and `lg x = log max{2, x}` (base `lg`). For a collection of non-empty
  strings with `W ≠ ∅`, `L_W ≥ 2` and `Δ_W ≥ |W| ≥ 1`, so the quotient in `D_W` has no zero
  denominator; `σ_W = 1` gives `lg 0 = 1`, as the paper's truncated logarithm does.
* `τ(m, η) = lg m + log(1/η) / lg(log(1/η) / lg m)`; since `lg ≥ 1`, both denominators are
  positive.
-/

variable {α : Type} [DecidableEq α]

/-- `L_W = ∑_{Z ∈ W} (|Z| + 1)` (Definition 3.1): the length of the collection written with a
separator after each member. -/
def LColl (W : Multiset (List α)) : ℕ := (W.map fun Z => Z.length + 1).sum

/-- `d_m(W)`: the number of distinct length-`m` substrings of the members of `W`
(Definition 3.1). -/
def dColl (m : ℕ) (W : Multiset (List α)) : ℕ := (subsColl m W).card

/-- `δ(W) = max_{m ≥ 1} d_m(W)/m` (Definition 3.1), the substring complexity of a collection. -/
noncomputable def deltaColl (W : Multiset (List α)) : ℝ :=
  maxRatio (fun m => dColl m W) (W.map List.length).sup

/-- `σ_W = d_1(W)`, the number of distinct characters of `W` (Definition 3.1). -/
def sigmaColl (W : Multiset (List α)) : ℕ := dColl 1 W

/-- `Δ_W = max(|W|, δ(W))` (Definition 3.1). -/
noncomputable def DeltaColl (W : Multiset (List α)) : ℝ :=
  max (Multiset.card W : ℝ) (deltaColl W)

/-- `D_W = Δ_W lg(L_W log σ_W / (Δ_W log L_W))` for `W ≠ ∅`, and `D_∅ = 0` (Definition 3.1). -/
noncomputable def DColl (W : Multiset (List α)) : ℝ :=
  if W = 0 then 0
  else DeltaColl W * lg ((LColl W : ℝ) * Real.logb 2 (sigmaColl W) /
    (DeltaColl W * Real.logb 2 (LColl W)))

/-- The tail scale `τ(m, η) = lg m + log(1/η) / lg(log(1/η) / lg m)` (Equation (3), p.20), for
`m ≥ 0` and `0 < η < 1`. -/
noncomputable def tau (m η : ℝ) : ℝ :=
  lg m + Real.logb 2 (1 / η) / lg (Real.logb 2 (1 / η) / lg m)

end DynStrings.Supplement


