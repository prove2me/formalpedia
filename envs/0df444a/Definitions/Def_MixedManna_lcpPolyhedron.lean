-- Prove2me | Definitions.Def_MixedManna_lcpPolyhedron
-- name    : MixedManna_lcpPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:21.475146+00:00
-- url     : https://prove2.me/theorems/fa5995b6-d93d-4764-93da-c3b20aae3bba
-- title:
--   The polyhedron $\mathcal P$ of the augmented LCP (14)
-- statement:
--   Fix $P>0$, $R$, coefficients $\delta_j$ for the goods and the last-segment length $1+\varepsilon$. The polyhedron $\mathcal P$ consists of the points with all of $p,f,r,s,z\ge 0$ and
--
--   $$
--   \begin{aligned}
--   &\forall i\in N: && \textstyle\sum_{j\in M^+}W_{ij}p_j-\sum_{j\in M^-}W_{ij}p_j+\sum_{k,j\in M^+}f_{ijk}-\sum_{k,j\in M^-}f_{ijk}-z\le P\big(\sum_{j\in M^+}W_{ij}-\sum_{j\in M^-}W_{ij}\big) &(14a)\\
--   &\forall j\in M^-: && \textstyle\sum_{i,k}f_{ijk}+p_j\le P &(14b)\\
--   &\forall j\in M^+: && \textstyle-\sum_{i,k}f_{ijk}-p_j-\delta_jz\le -P &(14c)\\
--   &\forall j\in M^-,\forall i,k: && D_{ijk}r_i-p_j-s_{ijk}\le D_{ijk}R-P &(14d)\\
--   &\forall j\in M^+,\forall i,k: && -U_{ijk}r_i+p_j-s_{ijk}-z\le P-U_{ijk}R &(14e)\\
--   &\forall (i,j,k): && f_{ijk}+L_{ijk}p_j\le L_{ijk}P &(14f)
--   \end{aligned}
--   $$
--
--   where $D_{ijk}=|U_{ijk}|$ and the final segment has length $L_{ijk}=1+\varepsilon$ in (14f). The relative prices are $P-p_j$ for goods and $-(P-p_j)$ for bads, and $1/(R-r_i)$ is agent $i$'s bang per buck.
--
--   **Formalization Note** Each constraint is stored through its slack (right side minus left side); $(i,j,k)$ ranges over the segments carrying variables. The conditions on $P,R,\delta,\varepsilon$ are hypotheses of the theorems.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.2, (14a)–(14f), p.21 ("Let 𝒫 be the polyhedron corresponding to LCP (14)"); last segment length p.14 and p.23

import Mathlib
import Definitions.Def_MixedManna_LCPVar

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

open Classical

/-- The segment length used in LCP (14): `L_ijk` for a finite segment and `1 + ε` for the final
one (p.14: "the length of the last segment is 1 plus some small constant"; Claim 1's proof, p.23:
"we set `L_ijk = 1 + ϵ`, for some small `ϵ > 0`"). -/
noncomputable def lcpLength (I : Instance N M) (ε : ℝ) (σ : Seg I) : ℝ :=
  if IsLastSeg σ then 1 + ε else I.L (segAgent σ) (segItem σ) (segIdx σ)

/-- Slack of `(14a)` for agent `i`:
`P(Σ_{M⁺} W_ij − Σ_{M⁻} W_ij) − (Σ_{M⁺} W_ij p_j − Σ_{M⁻} W_ij p_j + Σ_{k,j∈M⁺} f_ijk
− Σ_{k,j∈M⁻} f_ijk − z)`. -/
noncomputable def agentSlack (I : Instance N M) (P : ℝ) (x : LCPVar I) (i : N) : ℝ :=
  P * ∑ j, itemSign I j * I.W i j -
    (∑ j, itemSign I j * I.W i j * pv x j +
      ∑ σ : Seg I, (if segAgent σ = i then itemSign I (segItem σ) * fv x σ else 0) - zv x)

/-- Slack of the price constraint of item `j`: `(14b)` `P − Σ_{i,k} f_ijk − p_j` on a bad, and
`(14c)` `−P − (−Σ_{i,k} f_ijk − p_j − δ_j z)` on a good. -/
noncomputable def priceSlack (I : Instance N M) (P : ℝ) (δ : M → ℝ) (x : LCPVar I) (j : M) : ℝ :=
  if IsGood I j then
    -P - (-(∑ σ : Seg I, if segItem σ = j then fv x σ else 0) - pv x j - δ j * zv x)
  else P - ((∑ σ : Seg I, if segItem σ = j then fv x σ else 0) + pv x j)

/-- Slack of the spending constraint of segment `(i, j, k)`: `(14d)`
`D_ijk R − P − (D_ijk r_i − p_j − s_ijk)` on a bad (`D_ijk = −U_ijk`), and `(14e)`
`P − U_ijk R − (−U_ijk r_i + p_j − s_ijk − z)` on a good. -/
noncomputable def spendSlack (I : Instance N M) (P R : ℝ) (x : LCPVar I) (σ : Seg I) : ℝ :=
  if IsGood I (segItem σ) then
    P - segSlope σ * R - (-segSlope σ * rv x (segAgent σ) + pv x (segItem σ) - sv x σ - zv x)
  else
    (-segSlope σ) * R - P - ((-segSlope σ) * rv x (segAgent σ) - pv x (segItem σ) - sv x σ)

/-- Slack of `(14f)` for segment `(i, j, k)`: `L_ijk P − (f_ijk + L_ijk p_j)`, with the LCP
length `lcpLength`. -/
noncomputable def segSlack (I : Instance N M) (P ε : ℝ) (x : LCPVar I) (σ : Seg I) : ℝ :=
  lcpLength I ε σ * P - (fv x σ + lcpLength I ε σ * pv x (segItem σ))

/-- **The polyhedron `𝒫` of LCP (14)** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive
Allocation of a Mixed Manna*, arXiv:2008.02753v1, (14a)–(14f), p.21: "Let `𝒫` be the polyhedron
corresponding to LCP (14)"): the points `(p, f, r, s, z)` with every variable `≥ 0` (`z`
included) and

* `(14a)` `∀ i ∈ N`: `Σ_{M⁺} W_ij p_j − Σ_{M⁻} W_ij p_j + Σ_{k,j∈M⁺} f_ijk − Σ_{k,j∈M⁻} f_ijk − z
  ≤ P(Σ_{M⁺} W_ij − Σ_{M⁻} W_ij)`;
* `(14b)` `∀ j ∈ M⁻`: `Σ_{i,k} f_ijk + p_j ≤ P`;
* `(14c)` `∀ j ∈ M⁺`: `−Σ_{i,k} f_ijk − p_j − δ_j z ≤ −P`;
* `(14d)` `∀ j ∈ M⁻, ∀ i, k`: `D_ijk r_i − p_j − s_ijk ≤ D_ijk R − P`;
* `(14e)` `∀ j ∈ M⁺, ∀ i, k`: `−U_ijk r_i + p_j − s_ijk − z ≤ P − U_ijk R`;
* `(14f)` `∀ (i, j, k)`: `f_ijk + L_ijk p_j ≤ L_ijk P`.

**Formalization Note** `i, k` and `(i, j, k)` range over `Seg I` (segments of goods with
`U_ij1 ≤ 0` carry no variable, p.17). The final segment has length `1 + ε` in `(14f)`
(`lcpLength`). `P`, `R`, `δ`, `ε` are parameters; the constraints on them are hypotheses of the
theorems. -/
def lcpPolyhedron (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) : Set (LCPVar I) :=
  {x | (∀ j, 0 ≤ pv x j) ∧ (∀ σ, 0 ≤ fv x σ) ∧ (∀ i, 0 ≤ rv x i) ∧ (∀ σ, 0 ≤ sv x σ) ∧
    0 ≤ zv x ∧ (∀ i, 0 ≤ agentSlack I P x i) ∧ (∀ j, 0 ≤ priceSlack I P δ x j) ∧
    (∀ σ, 0 ≤ spendSlack I P R x σ) ∧ (∀ σ, 0 ≤ segSlack I P ε x σ)}

end MixedManna


