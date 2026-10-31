-- Prove2me | Definitions.Def_PandoraComb_Bernoullify
-- name    : PandoraComb_Bernoullify
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:50.047273+00:00
-- url     : https://prove2.me/theorems/ce1d7b2e-bc52-49c6-8669-fae813fd0ddc
-- title:
--   Transformation $T$: Bernoulli copies $D_{i,j}$ and the lifted cost $c'$
-- statement:
--   Let every $D_i$ be supported in a grid $0=v_0<v_1<\dots<v_m$.
--
--   1. Box $i$ is replaced by boxes $(i,j)$, $j=0,\dots,m$. Box $(i,j)$ has the weighted Bernoulli law with value $v_j$ and probability
--   $$\frac{\mathbb P(V_i=v_j)}{\mathbb P(V_i\le v_j)},$$
--   where $0/0$ is read as $0$.
--   2. The **lifted cost** is $c'(S)=c\big(\{i\mid\exists j:\ (i,j)\in S\}\big)$ for $S\subseteq\iota\times\{0,\dots,m\}$.
--
--   $T(\mathcal I)=(D_{i,j},c')$ is a Bernoulli instance equivalent to $\mathcal I$ (Proposition 4.3), and $c'$ is submodular when $c$ is (Proposition 4.2).
--
--   **Formalization Note** The grid is `v : Fin (m + 1) → ℝ` (the paper's $v_1<\dots<v_m$ indexed from $0$); Lean's real division gives $0/0=0$, the paper's convention. The copy index of `liftCost` may be any type.
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §4, p.19, Transformation 2

import Definitions.Def_PandoraComb_Bernoulli

open MeasureTheory

noncomputable section

namespace PandoraComb

/-- **Transformation `T`, the laws** (arXiv:2303.01078v1, §4, p.19): for a grid
`0 = v_0 < v_1 < ⋯ < v_m` containing the supports, box `(i, j)` of the new instance has the
weighted Bernoulli distribution with value `v_j` and probability `P(V_i = v_j) / P(V_i ≤ v_j)`
("where 0/0 is interpreted as 0").

**Formalization Note.** The grid is `v : Fin (m + 1) → ℝ` (the paper's `v_1 < ⋯ < v_m`, indexed
from `0`); Lean's real division gives `0 / 0 = 0`. -/
def bernoullify {ι : Type*} (D : ι → Measure ℝ) {m : ℕ} (v : Fin (m + 1) → ℝ) :
    ι × Fin (m + 1) → Measure ℝ :=
  fun ij => bernoulliLaw (v ij.2) ((D ij.1 {v ij.2}).toReal / (D ij.1 (Set.Iic (v ij.2))).toReal)

/-- **Transformation `T`, the cost** (§4, p.19): `c′(S) := c({i | ∃ j such that (i, j) ∈ S})`
for `S ⊆ [n] × [m]`. -/
def liftCost {ι κ : Type*} [DecidableEq ι] (c : Finset ι → ℝ) : Finset (ι × κ) → ℝ :=
  fun S => c (S.image Prod.fst)

end PandoraComb


