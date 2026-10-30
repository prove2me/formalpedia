-- Prove2me | Definitions.Def_NestedLogitNBR_Feasible7
-- name    : NestedLogitNBR_Feasible7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:40:50.767064+00:00
-- url     : https://prove2.me/theorems/0a525ad0-0eb2-4297-8ae3-37366f4e3ff4
-- title:
--   Feasibility for the fractional program (7)
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Problem (7) (p. 20) is
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge\max_{z_i\in[0,1]^n}\Big(\sum_{j\in N}v_{ij}z_{ij}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_{ij}}{\sum_{j\in N}v_{ij}z_{ij}}-x\right]\ \ \forall i\in M.
--   $$
--
--   This predicate says that $(x,y)$ satisfies these constraints. The proof of Theorem 7 shows that $(\alpha\hat x,\alpha\hat y)$ is feasible for (7), and (7) is tighter than (3).
--
--   **Formalization Note** "$y_i\ge\max_z$" is written as "$y_i\ge$ the objective at every $z\in[0,1]^n$", with the objective's convention at total weight $0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), problem (7), p. 20

import Mathlib
import Definitions.Def_NestedLogitNBR_fracObj

namespace NestedLogitNBR

/-- **Feasibility for the fractional program (7).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), problem (7), p. 20: `min x` s.t. `v_0 x ≥ Σ_{i∈M} y_i`,
`y_i ≥ max_{z_i∈[0,1]^n} { (Σ_{j∈N} v_ij z_ij)^{γ_i} [ Σ_{j∈N} r_ij v_ij z_ij / Σ_{j∈N} v_ij z_ij − x ] }`
for all `i ∈ M`.

`Feasible7 v0 r v γ x y` says that `(x, y)` satisfies the first constraint and, for every nest
`i` and every `z ∈ [0,1]^n`, `fracObj r v γ i z x ≤ y i`.

**Formalization Note.** "`y_i ≥ max_z …`" is written as "`y_i ≥` the objective at every
`z ∈ [0,1]^n`", which is equivalent whenever the maximum exists (Lemma 6, p. 21) and needs no
`sSup`. -/
def Feasible7 {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (x : ℝ)
    (y : Fin m → ℝ) : Prop :=
  ∑ i, y i ≤ v0 * x ∧
    ∀ (i : Fin m) (z : Fin n → ℝ), (∀ j, z j ∈ Set.Icc (0 : ℝ) 1) → fracObj r v γ i z x ≤ y i

end NestedLogitNBR


