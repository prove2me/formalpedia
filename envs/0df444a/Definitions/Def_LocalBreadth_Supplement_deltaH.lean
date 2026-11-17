-- Prove2me | Definitions.Def_LocalBreadth_Supplement_deltaH
-- name    : LocalBreadth_Supplement_deltaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:26.455339+00:00
-- url     : https://prove2.me/theorems/5c7217f6-eb30-4456-82a1-2df41483d208
-- title:
--   Filtered lower Banach density $\delta_h$ and threshold classes
-- statement:
--   Let $h:\mathbb N_{\ge1}\to(0,\infty)$ be nondecreasing. A **rectangle** is a nonempty finite axis-parallel lattice box $R$; write $V(R)=|R|$ and $m_B(R)=|B\cap R|$. For $A,B$ with $B$ infinite, the **$h$-filtered lower Banach density** of $A$ relative to $B$ is
--   $$\delta_h(A,B)=\lim_{s\to\infty}\ \inf_{R:\ m_B(R)\ge s\,h(V(R))}\frac{|A\cap B\cap R|}{m_B(R)},$$
--   where an empty infimum is interpreted as $1$. A target with $\sup_R m_B(R)/h(V(R))<\infty$ is called $h$-vacuous; for it $\delta_h(A,B)=1$ for every $A$. For $h\equiv1$ in dimension one this is ordinary lower Banach density.
--
--   The module also fixes the three threshold classes of the paper:
--   1. a **threshold**: $h$ positive and nondecreasing on $\mathbb N_{\ge1}$ (Definition 1.4, §9);
--   2. an **admissible** threshold (§6): a threshold with $\sup_{N\ge1}N/h(N)=\infty$;
--   3. the class of §7: $h(V)=u(V)\log(2+V)$ with $u:[1,\infty)\to(0,\infty)$ nondecreasing.
--
--   **Formalization Note** Rectangles are pairs $(a,b)$ with $a\le b$ in the product order, standing for $[a,b]$; $h$ is a function `ℕ → ℝ` evaluated only at volumes $\ge1$. The empty infimum is set to $1$ explicitly, and since the infimum is nondecreasing in $s$ the limit is written as the supremum over natural $s$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), Definition 1.4, p.4; §6, p.42; §7, p.51; §9, p.71

import Mathlib

namespace LocalBreadth.Supplement

variable {P : Type} [Preorder P]

/-- The rectangle `[R.1, R.2]`: for `P = Fin d → ℤ` with the product order this is
the finite axis-parallel lattice box `∏ i, [R.1 i, R.2 i]`; it is nonempty exactly when `R.1 ≤ R.2`. -/
def rect (R : P × P) : Set P := Set.Icc R.1 R.2

/-- The volume `V(R) = |R|`. -/
noncomputable def vol (R : P × P) : ℕ := (rect R).ncard

/-- The target count `m_B(R) = |B ∩ R|`. -/
noncomputable def mass (B : Set P) (R : P × P) : ℕ := (B ∩ rect R).ncard

open Classical in
/-- The infimum in Definition 1.4 at level `s`: over nonempty rectangles `R` with
`m_B(R) ≥ s·h(V(R))`, of `|A ∩ B ∩ R| / m_B(R)`; an empty infimum is `1`. -/
noncomputable def filteredInf (h : ℕ → ℝ) (A B : Set P) (s : ℝ) : ℝ :=
  if {R : P × P | R.1 ≤ R.2 ∧ s * h (vol R) ≤ (mass B R : ℝ)}.Nonempty then
    ⨅ R : {R : P × P // R.1 ≤ R.2 ∧ s * h (vol R) ≤ (mass B R : ℝ)},
      ((A ∩ B ∩ rect R.1).ncard : ℝ) / (mass B R.1 : ℝ)
  else 1

/-- **Filtered lower Banach density** `δ_h(A, B)`. Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), Definition 1.4, p.4:
`δ_h(A, B) = lim_{s→∞} inf_{R a finite axis-parallel rectangle, m_B(R) ≥ s h(V(R))} |A ∩ B ∩ R| / m_B(R)`,
an empty infimum being `1`.

**Formalization Note.** The threshold is a function `h : ℕ → ℝ`, only ever evaluated at volumes
`V(R) ≥ 1`; its positivity and monotonicity on `ℕ_{≥1}` are hypotheses of the theorems that use it.
Rectangles are pairs `(a, b)` with `a ≤ b`. The empty infimum is `1` explicitly (Lean's real `⨅` over
an empty type is `0`). Every ratio lies in `[0, 1]` (at `s = 0` a rectangle with `m_B(R) = 0` gives
`0 / 0 = 0`), so each infimum is a genuine one and lies in `[0, 1]`; it is nondecreasing in `s`, so
the limit `s → ∞` (over real `s`) is the supremum over natural `s`, which is what is written. -/
noncomputable def deltaH (h : ℕ → ℝ) (A B : Set P) : ℝ := ⨆ s : ℕ, filteredInf h A B s

/-- `h : ℕ_{≥1} → (0, ∞)` nondecreasing (Definition 1.4, p.4; §9, p.71). -/
def IsThreshold (h : ℕ → ℝ) : Prop := (∀ n, 1 ≤ n → 0 < h n) ∧ MonotoneOn h (Set.Ici 1)

/-- An **admissible** threshold (§6, p.42): finite-valued, nondecreasing, positive on `ℕ_{≥1}`, and
`sup_{N ≥ 1} N / h(N) = ∞`. -/
def IsAdmissible (h : ℕ → ℝ) : Prop :=
  IsThreshold h ∧ ¬ BddAbove ((fun N : ℕ => (N : ℝ) / h N) '' Set.Ici 1)

/-- The threshold class of §7 (p.51): `h(V) = u(V) log(2 + V)` with `u : [1, ∞) → (0, ∞)`
nondecreasing. -/
def IsLogThreshold (h : ℕ → ℝ) : Prop :=
  ∃ u : ℝ → ℝ, (∀ v, 1 ≤ v → 0 < u v) ∧ MonotoneOn u (Set.Ici 1) ∧
    ∀ V : ℕ, 1 ≤ V → h V = u V * Real.log (2 + V)

end LocalBreadth.Supplement


