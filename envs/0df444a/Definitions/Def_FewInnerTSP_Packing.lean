-- Prove2me | Definitions.Def_FewInnerTSP_Packing
-- name    : FewInnerTSP_Packing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:14.212687+00:00
-- url     : https://prove2.me/theorems/69c26814-3131-49fe-a461-698a68d3cdc0
-- title:
--   Closed axis-aligned squares and packing-compliant free edges, $p_0=32768$
-- statement:
--   For a center $c\in\mathbb R^2$ and side $s$, the **closed axis-aligned square** is $\{x : |x_1-c_1|\le s/2,\ |x_2-c_2|\le s/2\}$, and its boundary is where $\max\{|x_1-c_1|,|x_2-c_2|\}=s/2$.
--
--   Let $p_0=32768=2\cdot16^2\cdot64$ (Lemma F.1) and $\lambda=400p_0=13\,107\,200$ (App. F). A set $F$ of free edges (unordered index pairs) is **packing-compliant** if for every closed axis-aligned square $D$ of side $s>0$, at most $p_0$ edges of $F$ have length at least $s$ and exactly one endpoint in $D$:
--   $$\#\{e=\{a,b\}\in F : |P_aP_b|\ge s,\ P_a\in D,\ P_b\notin D\}\le p_0 .$$
--   The property is hereditary: every subset of a compliant set is compliant.
--
--   This is the property the separator uses to cap crossing edges (Theorem 4.1) and that the recursion preserves for witnesses (Definition 5.1).
--
--   **Formalization Note** Definition 3.4 refers to "the preceding square packing bounds with the fixed universal constants". Appendices B.4 and F derive every cap used from the single form of Lemma F.1 through constant covers, so compliance here is that one clause with $p_0=32768$. Compliance constrains free edges only.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §3.1 and Definition 3.4, p.5 (PDF p.7); Lemma F.1 and App. F, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_FewInnerTSP_MixedInstance

namespace FewInnerTSP

/-- The closed axis-aligned square with center `c` and side `s`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), §3.1, p.5 (PDF p.7). -/
def closedSquare (c : Pt) (s : ℝ) : Set Pt :=
  {x | |x 0 - c 0| ≤ s / 2 ∧ |x 1 - c 1| ≤ s / 2}

/-- The boundary of the closed axis-aligned square with center `c` and side `s`. -/
def squareBoundary (c : Pt) (s : ℝ) : Set Pt :=
  {x | max |x 0 - c 0| |x 1 - c 1| = s / 2}

/-- The universal packing constant `p₀ = 32768 = 2 · 16² · 64`.
Source: Li, Ma, Gong, Lemma F.1, p.22 (PDF p.24). -/
def p0 : ℕ := 32768

/-- The frame cap `λ = 400 p₀ = 13 107 200`, also the cap on long straddling edges.
Source: Li, Ma, Gong, App. F, p.22 (PDF p.24). -/
def lam : ℕ := 400 * p0

open Classical in
/-- **Packing-compliant free edges.** For every closed axis-aligned square `D` of side `s > 0`, at most
`p₀` edges of `F` have length at least `s` and exactly one endpoint in `D`.
Source: Li, Ma, Gong, Definition 3.4, p.5 (PDF p.7) and Lemma F.1, p.22 (PDF p.24).

**Formalization Note** Definition 3.4 refers to "the preceding square packing bounds with the fixed
universal constants". Appendices B.4 and F derive every cap from the single form of Lemma F.1 through
constant covers, with `λ = 400 p₀`, so compliance here is that one clause. The second clause of §3.1
is a consequence with another constant. Compliance constrains free edges only, never skeleton
edges. -/
def IsPackingCompliant {n : ℕ} (P : Fin n → Pt) (F : Finset (Sym2 (Fin n))) : Prop :=
  ∀ (c : Pt) (s : ℝ), 0 < s →
    (F.filter fun e => s ≤ edgeLen P e ∧
      ∃ a b, e = s(a, b) ∧ P a ∈ closedSquare c s ∧ P b ∉ closedSquare c s).card ≤ p0

end FewInnerTSP


