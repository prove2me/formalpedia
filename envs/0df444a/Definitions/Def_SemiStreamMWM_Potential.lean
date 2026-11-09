-- Prove2me | Definitions.Def_SemiStreamMWM_Potential
-- name    : SemiStreamMWM_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:18:59.041435+00:00
-- url     : https://prove2.me/theorems/028fdf4a-caa3-4f7f-b64f-4c2c62e1d5e2
-- title:
--   §2, §2.1 — the potential $F_t$, its gradient, $F_t^*$, $\delta$ and $\eta$
-- statement:
--   Fix integer edge weights $w$ and the weight bound $W$. For $t>0$ the paper regularizes the vertex duals and minimizes
--
--   $$F_t(x)=-w^\top x+t(\log e)\sum_v y_{t,v}(x),\qquad y_{t,v}(x)=W^4\,2^{-(1-x_v)/t},$$
--
--   over the matching polytope; $F_t^*=\min_{x\in\mathcal P_G}F_t(x)$. Its gradient is $\nabla F_t(x)=-w+A^\top y_t(x)$, i.e. $\nabla F_t(x)_e=-w_e+y_{t,u}(x)+y_{t,v}(x)$ for $e=uv$. Within a phase the degree slack is $\delta=t\log W$ and the step size $\eta$ is the largest power of two not exceeding $t\delta/128$. Here $\log$ is the base-2 logarithm.
--
--   These quantities drive Algorithms 2.1 and 2.2 and every lemma of §2.
--
--   **Formalization Note** The closed form $-w^\top x+t(\log e)\sum_v y_{t,v}(x)$, the second line of the display on p.9, is the definition. $F_t^*$ is the infimum of $F_t$ over $\mathcal P_G$, a nonempty compact set on which $F_t$ is continuous, so it is the attained minimum. $\eta=2^{\lfloor\log_2(t\delta/128)\rfloor}$ with an integer exponent.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §2 p.9 (display and footnote 4); §2.1 p.10

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph

open Classical

namespace SemiStreamMWM

/-! # The entropy-regularized potential `F_t` and the phase parameters

J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §2 p.9 and §2.1 p.10:
`F_t(x) = −w^⊤x + max_{y≥0} Σ_v [(x_v − 1)y_v − t y_v (log(y_v/W^4) − log e)]
        = −w^⊤x + t(log e) Σ_v y_{t,v}(x)`, with `y_{t,v}(x) = W^4 2^{−(1−x_v)/t}`;
`F_t^∗ = min_{x∈P_G} F_t(x)`; `∇F_t(x) = −w + A^⊤y_t(x)` (p.10); within a phase `δ = t log W` and `η`
is the largest power of two not exceeding `tδ/128` (p.10).

**Formalization Note.** `log` is base 2 (footnote 4, p.9): `Real.logb 2`. The closed form (the
second line of the display on p.9) is the definition; that it equals the maximum over `y ≥ 0` is
a fact, not an assumption. `2^{−(1−x_v)/t}` is a real power (`Real.rpow`). `F_t^∗` is an infimum
over `P_G`, which is nonempty (it contains `0`) and compact, and `F_t` is continuous, so the
infimum is the attained minimum of p.9. `η = 2^{⌊log₂(tδ/128)⌋}` with an integer exponent, which
is the largest power of two `≤ tδ/128` whenever `tδ > 0`. -/

variable {V : Type*} [Fintype V]

/-- `log W`, base 2. -/
noncomputable def logW (W : ℕ) : ℝ := Real.logb 2 W

/-- `log e`, base 2. -/
noncomputable def loge : ℝ := Real.logb 2 (Real.exp 1)

/-- The maximizing vertex duals `y_{t,v}(x) = W^4 2^{−(1−x_v)/t}` (p.9). -/
noncomputable def dual (G : SimpleGraph V) (W : ℕ) (t : ℝ) (x : G.edgeSet → ℝ) (v : V) : ℝ :=
  (W : ℝ) ^ 4 * (2 : ℝ) ^ (-(1 - deg G x v) / t)

/-- The potential `F_t(x) = −w^⊤x + t(log e) Σ_v y_{t,v}(x)` (p.9). -/
noncomputable def F (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ) (x : G.edgeSet → ℝ) : ℝ :=
  -wdot G (weightVec G w) x + t * loge * ∑ v, dual G W t x v

/-- `F_t^∗ = min_{x∈P_G} F_t(x)` (p.9). -/
noncomputable def Fstar (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ) : ℝ :=
  sInf (F G w W t '' matchingPolytope G)

/-- The gradient `∇F_t(x) = −w + A^⊤y_t(x)` (p.10): at the edge `e = uv` it is
`−w_e + y_{t,u}(x) + y_{t,v}(x)`. -/
noncomputable def gradF (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (t : ℝ) (x : G.edgeSet → ℝ) :
    G.edgeSet → ℝ :=
  fun e => -(w e.1 : ℝ) + ∑ v, if v ∈ (e : Sym2 V) then dual G W t x v else 0

/-- The degree slack `δ = t log W` (p.10). -/
noncomputable def delta (W : ℕ) (t : ℝ) : ℝ := t * logW W

/-- The step size `η`: the largest power of two not exceeding `tδ/128` (p.10). -/
noncomputable def eta (W : ℕ) (t : ℝ) : ℝ :=
  (2 : ℝ) ^ (⌊Real.logb 2 (t * delta W t / 128)⌋)

end SemiStreamMWM


