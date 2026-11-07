-- Prove2me | Definitions.Def_VertexSampleCSP_Instance_Gamma
-- name    : VertexSampleCSP_Instance_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:34.836547+00:00
-- url     : https://prove2.me/theorems/f56e6857-b272-47b0-9c41-77ad5b556981
-- title:
--   The norm $\|f_e\|^2$, the variable scale $\gamma_i(\mathcal I)$ and the scale $\Gamma(\mathcal I)$
-- statement:
--   For an instance $\mathcal I$ on $V$, put $\|f_e\|^2=\sum_{a\in[q]^e}f_e(a)^2$ and
--
--   $$\gamma_i(\mathcal I)=\Big(\sum_{e\ni i}\|f_e\|^2\Big)^{1/2},\qquad \Gamma(\mathcal I)=\sum_{i\in V}\gamma_i(\mathcal I),$$
--
--   where $e$ ranges over the $r$-subsets containing $i$. A variable $i$ is **relevant** if $\gamma_i(\mathcal I)>0$.
--
--   $\Gamma$ is the scale in which every variable enters through its own payoffs; for Max-Cut of a graph $\gamma_v=\sqrt{2d_v}$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Instances", p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

/-- **`‖f_e‖²`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*, STOC 2027
submission (manuscript sha256 1e0edd23…), Appendix A, "Instances", p.13 (PDF p.15):
`‖f_e‖² = Σ_{a ∈ [q]^e} f_e(a)²`. -/
noncomputable def Instance.normSq {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (e : Finset V) : ℝ :=
  ∑ a : (e → Fin q), I.f e a ^ 2

/-- **`γ_i(I)`.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A,
"Instances", p.13 (PDF p.15): `γ_i(I) = (Σ_{e ∋ i} ‖f_e‖²)^{1/2}`, the sum over the `r`-subsets `e`
containing the variable `i`. A variable `i` is *relevant* if `γ_i(I) > 0`. -/
noncomputable def Instance.gamma {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (i : V) : ℝ :=
  Real.sqrt (∑ e ∈ (Finset.powersetCard r Finset.univ).filter (fun e => i ∈ e), I.normSq e)

/-- **The scale `Γ(I)`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Instances", p.13 (PDF p.15):
`Γ(I) = Σ_{i ∈ V} γ_i(I)`. For Max-Cut of a graph, `γ_v = √(2 d_v)`. -/
noncomputable def Instance.Gamma {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) : ℝ :=
  ∑ i, I.gamma i

end VertexSampleCSP


