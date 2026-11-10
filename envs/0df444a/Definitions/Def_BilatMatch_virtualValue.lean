-- Prove2me | Definitions.Def_BilatMatch_virtualValue
-- name    : BilatMatch_virtualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:01.098262+00:00
-- url     : https://prove2.me/theorems/d06cc0f4-4511-4b2a-89c6-5b9de36d4761
-- title:
--   Virtual values and costs (2) and $\alpha$-virtual scores
-- statement:
--   Let a finitely supported prior have support $v^1<\dots<v^n$ with point masses $f(v^\ell)>0$. The buyer **virtual value** and seller **virtual cost** are
--   $$\phi(v^\ell)=v^\ell-(v^{\ell+1}-v^\ell)\frac{\Pr(v>v^\ell)}{f(v^\ell)}\ (\ell<n),\qquad \tau(c^k)=c^k+(c^k-c^{k-1})\frac{\Pr(c<c^k)}{f(c^k)}\ (k>1),$$
--   with $\phi(v^n)=v^n$ and $\tau(c^1)=c^1$ at the endpoints. For $\alpha\ge0$ the $\alpha$-virtual value and cost are $\phi^\alpha(v)=v+\alpha\phi(v)$ and $\tau^\alpha(c)=c+\alpha\tau(c)$.
--
--   **Formalization Note** The functions are total on $\mathbb R$ but used only at atoms of a finitely supported prior, where the next and previous atoms exist.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), eq. (2), p.7 (pdf p.9)

import Mathlib
import Definitions.Def_BilatMatch_bilateral

open MeasureTheory

namespace BilatMatch

/-!
Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), eq. (2), p.7 (pdf p.9).

**Formalization Note** The functions are total on `ℝ` but meaningful at the atoms of a finitely
supported prior `μ`, where the next atom above `v` (`sInf` of a nonempty finite set) and the
previous atom below `c` exist. The endpoint conventions of p.7 are the `else` branches:
`ϕ(v^{n}) = v^{n}` at the largest atom and `τ(c^1) = c^1` at the smallest atom.
-/

open Classical in
/-- Buyer virtual value, eq. (2) (p.7): at an atom `v` of `μ` that is not the largest,
`ϕ(v) = v − (v⁺ − v) · Pr(X > v) / Pr(X = v)` with `v⁺` the next atom; at the largest atom
`ϕ(v) = v`. -/
noncomputable def virtualValue (μ : Measure ℝ) (v : ℝ) : ℝ :=
  if ∃ y ∈ atoms μ, v < y then
    v - (sInf {y | y ∈ atoms μ ∧ v < y} - v) * (μ (Set.Ioi v)).toReal / (μ {v}).toReal
  else v

open Classical in
/-- Seller virtual cost, eq. (2) (p.7): at an atom `c` of `μ` that is not the smallest,
`τ(c) = c + (c − c⁻) · Pr(X < c) / Pr(X = c)` with `c⁻` the previous atom; at the smallest atom
`τ(c) = c`. -/
noncomputable def virtualCost (μ : Measure ℝ) (c : ℝ) : ℝ :=
  if ∃ y ∈ atoms μ, y < c then
    c + (c - sSup {y | y ∈ atoms μ ∧ y < c}) * (μ (Set.Iio c)).toReal / (μ {c}).toReal
  else c

/-- The buyer's `α`-virtual value `ϕ^α(v) = v + α ϕ(v)` (p.7). -/
noncomputable def alphaVirtualValue (α : ℝ) (μ : Measure ℝ) (v : ℝ) : ℝ :=
  v + α * virtualValue μ v

/-- The seller's `α`-virtual cost `τ^α(c) = c + α τ(c)` (p.7). -/
noncomputable def alphaVirtualCost (α : ℝ) (μ : Measure ℝ) (c : ℝ) : ℝ :=
  c + α * virtualCost μ c

end BilatMatch


