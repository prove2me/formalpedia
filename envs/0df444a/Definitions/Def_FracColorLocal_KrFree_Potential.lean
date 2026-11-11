-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Potential
-- name    : FracColorLocal_KrFree_Potential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:30.189478+00:00
-- url     : https://prove2.me/theorems/5324c7bc-f50f-4779-82ba-b3470ebaa1e6
-- title:
--   Weighted degrees, Φ_{G,u}, the scalar potential U_a, d∗, ξ_a, the potential U_{G,u}, gains g_x, ζ_v, S and J_p
-- statement:
--   Let $G$ be a finite graph on $V$, $N(v)$ the open neighbourhood of $v$, $N[v]=N(v)\cup\{v\}$, and for a vertex weight $a$ and $A\subseteq V$ write $a(A)=\sum_{v\in A}a(v)$.
--
--   - **Weighted degree**: for a positive weight $s$, $d_{G,s}(v)=s(N(v))/s(v)$; and $\Phi_{G,u}(s)=\sum_v u(v)\,f(d_{G,s}(v))$ with $f$ Shearer's function.
--   - **Scalar potential**: for $a>0$, $U_a(x)=\inf_{t>0}\{a f(t)+t x^2\}$ for $x>0$, and $U_a(0)=0$. $d_*(a,x)$ denotes the minimizer of $t\mapsto af(t)+tx^2$ over $t>0$, and $\xi_a(x)=U_a(x)-xU_a'(x)$.
--   - **Potential**: with $\Lambda_v=w(N(v))$ and $M_G(w)=\sum_{xy\in E(G)}w(x)w(y)$ (each edge once), for a nonnegative weight $w$
--     $$U_{G,u}(w)=\sum_v U_{u(v)}(w(v))-2M_G(w).$$
--     For an induced subgraph $G[A]$ the weights are restricted to $A$: $U_{G[A],u}(w)=\sum_{v\in A}U_{u(v)}(w(v))-2M_{G[A]}(w)$.
--   - **Gain** of selecting $x$, for $0<c\le 1$: $g_x=u(x)+c\,U_{G_x,u}(w)-c\,U_{G,u}(w)$, where $G_x=G-N[x]$.
--   - $\xi_v=\xi_{u(v)}(w(v))$, $\zeta_v=U'_{u(v)}(w(v))-2\Lambda_v$, $S=\sum_v u(v)w(v)$, and for integers $r\ge 4$, $p\ge 1$: $J_p(w)=(1+2^{(12r-14)p})\,w(V)$.
--
--   **Formalization Note** $U_a$ (`scalarU`) is `0` at `x = 0` and otherwise the real infimum `⨅` over the subtype of positive reals; for $a>0$ the expression is bounded below by $0$, so this is the true infimum. $U_a'$ is the ordinary derivative `deriv (scalarU a)`, used at $x>0$. `dStar a x` is a chosen positive minimizer when one exists (value `0` otherwise; (4.1) asserts existence and uniqueness for $a,x>0$). $M_{G[A]}(w)$ is half the ordered-pair sum `crossMass G w A A` of the referenced weighted-graph definitions, and $\Lambda_v$ is `neighborMass G w v`. $G_x$ is represented as the vertex set $V\setminus N[x]$ of the induced subgraph (`potentialOn`).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 4 (PDF 5), §1.2; pp. 17–18 (PDF 18–19), §4.1–§4.2; p. 21 (PDF 22), (5.4)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Shearer

namespace FracColorLocal.KrFree

open OAI.CliqueFreeIndependence.WeightedGraph

variable {V : Type*} [Fintype V]

/-- The weighted degree `d_{G,s}(v) := s(N_G(v)) / s(v)` (§1.2), for a positive vertex weight `s`. -/
noncomputable def weightedDegree (G : SimpleGraph V) (s : V → ℝ) (v : V) : ℝ :=
  neighborMass G s v / s v

/-- `Φ_{G,u}(s) := ∑_v u(v) f(d_{G,s}(v))` (§1.2). -/
noncomputable def phiPot (G : SimpleGraph V) (u s : V → ℝ) : ℝ :=
  ∑ v, u v * shearerF (weightedDegree G s v)

/-- The scalar potential `U_a(x) := inf_{t > 0} (a f(t) + t x²)` for `x ≠ 0`, and `U_a(0) := 0`
(§4.1). Used for `a > 0`, `x ≥ 0`; the infimum is over the positive reals. -/
noncomputable def scalarU (a x : ℝ) : ℝ :=
  if x = 0 then 0 else ⨅ t : {t : ℝ // 0 < t}, (a * shearerF t + t * x ^ 2)

/-- `d∗(a, x)`: a positive minimizer of `t ↦ a f(t) + t x²` over `t > 0`, when one exists
(junk value `0` otherwise). (4.1) asserts that for `a, x > 0` it exists and is unique. -/
noncomputable def dStar (a x : ℝ) : ℝ := by
  classical
  exact if h : ∃ d : ℝ, 0 < d ∧ a * shearerF d + d * x ^ 2 = scalarU a x then h.choose else 0

/-- The tangent loss `ξ_a(x) := U_a(x) - x U'_a(x)` (§4.2), `U'_a` the ordinary derivative. -/
noncomputable def xiScalar (a x : ℝ) : ℝ :=
  scalarU a x - x * deriv (scalarU a) x

/-- The potential of the induced subgraph `G[A]` at the weights `w` restricted to `A`:
`U_{G[A],u}(w) = ∑_{v ∈ A} U_{u(v)}(w(v)) - 2 M_{G[A]}(w)`, where
`M_{G[A]}(w) = ∑_{xy ∈ E(G[A])} w(x) w(y)` is half the ordered-pair sum `crossMass G w A A`. -/
noncomputable def potentialOn (G : SimpleGraph V) (u w : V → ℝ) (A : Finset V) : ℝ :=
  ∑ v ∈ A, scalarU (u v) (w v) - 2 * (crossMass G w A A / 2)

/-- The potential `U_{G,u}(w) := ∑_v U_{u(v)}(w(v)) - 2 M_G(w)` (§4.1), for nonnegative `w`. -/
noncomputable def potential (G : SimpleGraph V) (u w : V → ℝ) : ℝ :=
  potentialOn G u w Finset.univ

/-- The closed neighbourhood `N_G[x] = N_G(x) ∪ {x}`. -/
noncomputable def closedNbhd (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact insert x (neighbors G x)

/-- The gain `g_x := u(x) + c U_{G_x,u}(w) - c U_{G,u}(w)` from selecting `x` (§4.2), where
`G_x := G - N_G[x]` is the subgraph induced by `V \ N_G[x]`. -/
noncomputable def gain (G : SimpleGraph V) (u w : V → ℝ) (c : ℝ) (x : V) : ℝ := by
  classical
  exact u x + c * potentialOn G u w (Finset.univ \ closedNbhd G x) - c * potential G u w

/-- `ξ_v := ξ_{u(v)}(w(v))` (§4.2). -/
noncomputable def xiV (u w : V → ℝ) (v : V) : ℝ := xiScalar (u v) (w v)

/-- `ζ_v := U'_{u(v)}(w(v)) - 2 Λ_v`, with `Λ_v := w(N(v))` (§4.2). -/
noncomputable def zetaV (G : SimpleGraph V) (u w : V → ℝ) (v : V) : ℝ :=
  deriv (scalarU (u v)) (w v) - 2 * neighborMass G w v

/-- `S := ∑_v u(v) w(v)` (§4.2). -/
noncomputable def sObj (u w : V → ℝ) : ℝ := ∑ v, u v * w v

/-- `J_p(w) := (1 + 2^{(12r - 14)p}) w(V(G))` (5.4), for an integer `r ≥ 4`. -/
noncomputable def Jp (r p : ℕ) (w : V → ℝ) : ℝ :=
  (1 + (2 : ℝ) ^ ((12 * r - 14) * p)) * ∑ v, w v

end FracColorLocal.KrFree


