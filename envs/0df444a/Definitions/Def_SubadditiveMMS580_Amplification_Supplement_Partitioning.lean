-- Prove2me | Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
-- name    : SubadditiveMMS580_Amplification_Supplement_Partitioning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:04.504219+00:00
-- url     : https://prove2.me/theorems/35e306ba-1806-4fc5-bf43-0d0510875823
-- title:
--   q-partitioning valuations $\mathcal Q_q$, capped valuations $v^C$, the guarantee $\rho(c)$ and the grouping bound $F_d(x)$
-- statement:
--   Goods form a finite set $M=\{0,\dots,m-1\}$; a valuation is a set function $v:2^M\to\mathbb R$.
--
--   1. **$q$-partitioning valuations** (Definition 2.1). Let $q\ge2$ and $R\subseteq M$. A valuation $v$ satisfies the $\mathcal Q_q$ conditions on the ground set $R$ if $v(\emptyset)=0$, $v(S)\le v(T)$ whenever $S\subseteq T\subseteq R$, and for every $S\subseteq R$ and every ordered partition $(C_1,\dots,C_t)$ of $S$ into $1\le t\le q$ nonempty groups there are **supporting prices** $w_1,\dots,w_t\ge0$ with
--   $$\sum_{j=1}^t w_j=v(S),\qquad \sum_{j\in J}w_j\le v\Big(\bigcup_{j\in J}C_j\Big)\quad\text{for every }J\subseteq[t].$$
--   The prices may depend on $S$ and on the partition. The class $\mathcal Q_q$ consists of the valuations satisfying these conditions on $R=M$.
--   2. The **capped valuation** (§4.1): for $C\ge0$, $v^C(S)=\min\{v(S),C\}$.
--   3. The **guarantee function** of equation (1):
--   $$\rho(c)=\begin{cases}\dfrac{c}{11-5c},&0<c\le1,\\[4pt] \dfrac16,&1\le c\le\frac65,\\[4pt] \dfrac{2(c-1)}{7c-6},&\frac65\le c\le2,\\[4pt] \dfrac14,&c\ge2.\end{cases}$$
--   Adjacent branches agree at $c=1,\ 6/5,\ 2$.
--   4. The **grouping bound** of equation (8) and its crossing points (Lemma B.1): for $d>0$ and $x$ real,
--   $$F_d(x)=\frac{(1-x/d)^+}{2d-1},\qquad x_d=\frac{4d^2}{6d-1},$$
--   where $t^+=\max\{t,0\}$.
--
--   These objects state Theorem 1.2 and its supporting results in §4 and Appendix B: $\mathcal Q_q$ is the valuation class of the theorem, $\rho$ its guarantee, and $F_d$, $x_d$ the guarantee from $d$ groups of agents.
--
--   **Formalization Note** $\mathcal Q_q$ is defined through a ground-set-relative predicate so that restriction to a subset $R$ of goods (Lemma 4.1) is the same predicate with ground set $R$. Partitions are indexed by $\mathrm{Fin}\,t$. In the formula for $\rho$ the branches are taken on the half-open intervals $(-\infty,1]$, $(1,6/5]$, $(6/5,2]$, $(2,\infty)$; only arguments $c>0$ are ever used. Normalization and monotonicity on all of $M$ are the published predicates `MultiAllocToAlloc.Subadditive.IsNormalized` and `IsMonotone`.
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Definition 2.1 p. 9; eq. (1) p. 3; §4.1 p. 21 (capped valuation); eq. (8) p. 24 and Lemma B.1 p. 42 (F_d, x_d)

import Mathlib
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation

/-!
# q-partitioning valuations, capped valuations, the guarantee `ρ` and the grouping bound `F_d`

Bo Li, Ankang Sun, *Toward Constant-Factor Maximin Share Guarantees for Subadditive
Valuations*, STOC 2027 submission #580 (October 2026): Definition 2.1 p. 9 (the class `Q_q`),
eq. (1) p. 3 (`ρ`), §4.1 p. 21 (capped valuation `v^C`), eq. (8) p. 24 and Lemma B.1 p. 42
(`F_d(x)`, `x_d`).

Conventions. Goods are `Fin m`; a valuation is a real set function `Finset (Fin m) → ℝ`;
normalization and monotonicity are the published predicates
`MultiAllocToAlloc.Subadditive.IsNormalized` / `IsMonotone`.
-/

set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Supplement

open MultiAllocToAlloc.Subadditive

/-- Definition 2.1 (p. 9) relative to a ground set `R ⊆ M`: `v` is normalized, monotone on the
subsets of `R`, and for every `S ⊆ R` and every ordered partition `(C_1, …, C_t)` of `S` into
`1 ≤ t ≤ q` nonempty groups there are supporting prices `w_1, …, w_t ≥ 0` with
`∑_j w_j = v(S)` and `∑_{j ∈ J} w_j ≤ v(⋃_{j ∈ J} C_j)` for every `J ⊆ [t]`. -/
def IsQPartitioningOn {m : ℕ} (q : ℕ) (R : Finset (Fin m)) (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S T : Finset (Fin m), S ⊆ T → T ⊆ R → v S ≤ v T) ∧
  ∀ S : Finset (Fin m), S ⊆ R → ∀ t : ℕ, 1 ≤ t → t ≤ q → ∀ C : Fin t → Finset (Fin m),
    (∀ j, (C j).Nonempty) → (∀ j k, j ≠ k → Disjoint (C j) (C k)) →
    Finset.univ.biUnion C = S →
    ∃ w : Fin t → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = v S ∧
      ∀ J : Finset (Fin t), ∑ j ∈ J, w j ≤ v (J.biUnion C)

/-- Definition 2.1 (p. 9): the class `Q_q` of `q`-partitioning valuations on all goods `M`. -/
def IsQPartitioning {m : ℕ} (q : ℕ) (v : Finset (Fin m) → ℝ) : Prop :=
  IsQPartitioningOn q Finset.univ v

/-- §4.1 (p. 21): the capped valuation `v^C(S) = min {v(S), C}`. -/
noncomputable def capped {m : ℕ} (v : Finset (Fin m) → ℝ) (C : ℝ) : Finset (Fin m) → ℝ :=
  fun S => min (v S) C

/-- Eq. (1) (p. 3): `ρ(c) = c/(11 − 5c)` for `0 < c ≤ 1`, `1/6` for `1 ≤ c ≤ 6/5`,
`2(c − 1)/(7c − 6)` for `6/5 ≤ c ≤ 2`, and `1/4` for `c ≥ 2` (adjacent branches agree at
`1, 6/5, 2`). Only arguments `c > 0` are used. -/
noncomputable def rho (c : ℝ) : ℝ :=
  if c ≤ 1 then c / (11 - 5 * c)
  else if c ≤ 6 / 5 then 1 / 6
  else if c ≤ 2 then 2 * (c - 1) / (7 * c - 6)
  else 1 / 4

/-- Eq. (8) (p. 24) and Lemma B.1 (p. 42): `F_d(x) = (1 − x/d)^+ / (2d − 1)`. -/
noncomputable def Fd (d x : ℝ) : ℝ := max (1 - x / d) 0 / (2 * d - 1)

/-- Lemma B.1 (p. 42): the crossing point `x_d = 4d² / (6d − 1)`. -/
noncomputable def xd (d : ℝ) : ℝ := 4 * d ^ 2 / (6 * d - 1)

end SubadditiveMMS580.Amplification.Supplement


