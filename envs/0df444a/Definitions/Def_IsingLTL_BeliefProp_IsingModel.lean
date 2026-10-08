-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_IsingModel
-- name    : IsingLTL_BeliefProp_IsingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:34.509043+00:00
-- url     : https://prove2.me/theorems/16867d9d-605b-4947-9c7d-26931c1c591f
-- title:
--   The ferromagnetic Ising measure with vertex fields and plus-pinned vertices, magnetizations, correlations, marginals
-- statement:
--   Let $G$ be a graph on a vertex set $V$ and $A\subseteq V$ a finite set of vertices. A **configuration** on $A$ is $\underline x=\{x_i: i\in A\}$ with $x_i\in\{+1,-1\}$. For an inverse temperature $\beta\in\mathbb R$, vertex fields $\underline B=\{B_i\}$ and a set $S$ of **pinned** vertices, the **Ising measure** on the subgraph of $G$ induced by $A$ is
--   $$\mu(\underline x)=\frac1Z\,\mathbb 1\{x_i=+1\ \forall i\in S\cap A\}\,\exp\Big\{\beta\sum_{(i,j)\in E(A)}x_ix_j+\sum_{i\in A}B_ix_i\Big\},$$
--   where $E(A)$ is the set of edges of $G$ with both endpoints in $A$, each counted once, and $Z>0$ is the normalizing constant. This is the model (1.1) when $A=V$ is finite, $B_i\equiv B$ and $S=\emptyset$, and the model (3.1) with vertex-dependent fields. A pinned vertex corresponds to the field $B_i=+\infty$ (the convention of p. 10, used for plus boundary conditions).
--
--   Associated quantities, for a distribution $\mu$ of configurations on $A$:
--
--   1. the **magnetization** $\langle x_v\rangle=\mu(x_v=+1)-\mu(x_v=-1)$;
--   2. the **centered two-point correlation** $\langle x_u;x_v\rangle=\langle x_ux_v\rangle-\langle x_u\rangle\langle x_v\rangle$;
--   3. the **marginal** $\mu_U(\underline y)=\sum_{\underline x:\,\underline x_U=\underline y}\mu(\underline x)$ on $U\subseteq A$;
--   4. the **local magnetization** $m_j(\underline B)$ at $j$ of the model (3.1) on a finite graph, as a function of the field vector $\underline B$, and the partial derivative $\partial F/\partial B_k=\frac{d}{dt}F(\underline B+t e_k)\big|_{t=0}$.
--
--   **Formalization Note** Spins are Booleans (`true` $=+1$). The edge sum is half of the sum over ordered adjacent pairs. Fields equal to $+\infty$ are never encoded by large real numbers: they are pins. The all-plus configuration has positive weight, so $Z>0$ and there is no division by zero. The marginal is meant for $U\subseteq A$ (it is $0$ otherwise).
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 1, eq. (1.1); p. 8, eq. (3.1); p. 9 (Theorem 3.2, magnetization); p. 10 (B_i = +∞ convention); p. 14 (centered correlation, Lemma 4.4)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace IsingLTL.BeliefProp

/-- The spin value `x ∈ {+1, −1}` encoded by a Boolean: `true ↦ +1`, `false ↦ −1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The spin `x_v ∈ {+1, −1}` of vertex `v` in a configuration `x` on a finite vertex set `A`;
`0` if `v ∉ A` (that value is never used on vertices of `A`). -/
def spinOf {V : Type*} [DecidableEq V] (A : Finset V) (x : {v // v ∈ A} → Bool) (v : V) : ℝ :=
  if h : v ∈ A then spin (x ⟨v, h⟩) else 0

/-- Unnormalized Boltzmann weight of the ferromagnetic Ising model on the subgraph of `G`
induced by the finite vertex set `A`, at inverse temperature `β`, with vertex fields `B`, and
with the vertices of `S` pinned to `+1` (field `B_i = +∞`):
`1{x_i = +1 ∀ i ∈ S ∩ A} · exp(β ∑_{(i,j) ∈ E(A)} x_i x_j + ∑_{i ∈ A} B_i x_i)`.
The edge sum counts every (unordered) edge once: it is half of the sum over ordered pairs. -/
noncomputable def isingWeight {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (B : V → ℝ) (S A : Finset V) (x : {v // v ∈ A} → Bool) : ℝ :=
  if ∀ v : {v // v ∈ A}, v.1 ∈ S → x v = true then
    Real.exp (β * ((∑ u : {v // v ∈ A}, ∑ w : {v // v ∈ A},
        if G.Adj u.1 w.1 then spin (x u) * spin (x w) else 0) / 2)
      + ∑ u : {v // v ∈ A}, B u.1 * spin (x u))
  else 0

/-- The **Ising measure** (Dembo–Montanari, arXiv:0804.4726v3, (1.1) p. 1 and (3.1) p. 8) on the
subgraph of `G` induced by the finite vertex set `A`:
`μ(x) = (1/Z) exp{β ∑_{(i,j)∈E} x_i x_j + ∑_{i} B_i x_i}`, `x ∈ {+1,−1}^A`, with the vertices of
`S` pinned to `+1`.

Formalization Note: configurations are `{v // v ∈ A} → Bool` (`true` = `+1`). A field
`B_i = +∞` (the plus boundary condition of (4.2), p. 10) is encoded by putting `i` in `S`,
never by a large real field. `Z > 0` always (the all-plus configuration has positive weight), so
the division is never by zero. The model of (1.1) on a finite graph `G` with constant field `B`
is `isingOn G β (fun _ => B) ∅ Finset.univ`. -/
noncomputable def isingOn {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (B : V → ℝ) (S A : Finset V) (x : {v // v ∈ A} → Bool) : ℝ :=
  isingWeight G β B S A x / ∑ y, isingWeight G β B S A y

/-- The magnetization `⟨x_v⟩ = μ(x_v = +1) − μ(x_v = −1)` of vertex `v` under a distribution
`μ` of configurations on `A` (arXiv:0804.4726v3, Theorem 3.2, p. 9). -/
noncomputable def magOn {V : Type*} [DecidableEq V] (A : Finset V)
    (μ : ({v // v ∈ A} → Bool) → ℝ) (v : V) : ℝ :=
  IsingLTL.FreeEntropy.pairing μ (fun x => spinOf A x v)

/-- The centered two-point correlation `⟨x_u; x_v⟩ = ⟨x_u x_v⟩ − ⟨x_u⟩⟨x_v⟩` under `μ`
(arXiv:0804.4726v3, Lemma 4.4, p. 14). -/
noncomputable def corrOn {V : Type*} [DecidableEq V] (A : Finset V)
    (μ : ({v // v ∈ A} → Bool) → ℝ) (u v : V) : ℝ :=
  IsingLTL.FreeEntropy.pairing μ (fun x => spinOf A x u * spinOf A x v) - magOn A μ u * magOn A μ v

/-- The marginal `μ_U` on `U` of a distribution `μ` of configurations on `A`:
`μ_U(y) = ∑_{x : x_U = y} μ(x)`. Meaningful for `U ⊆ A` (otherwise it is `0`). -/
noncomputable def marginalOn {V : Type*} [DecidableEq V] (A U : Finset V)
    (μ : ({v // v ∈ A} → Bool) → ℝ) (y : {v // v ∈ U} → Bool) : ℝ := by
  classical
  exact ∑ x, if (∀ u : {v // v ∈ U}, spinOf A x u.1 = spin (y u)) then μ x else 0

/-- The local magnetization `m_j(B)` at vertex `j` of the Ising model (3.1) on the finite graph
`G` with vertex fields `B` (arXiv:0804.4726v3, Theorem 3.2, p. 9), as a function of `B`. -/
noncomputable def localMag {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (j : V) (B : V → ℝ) : ℝ :=
  magOn Finset.univ (isingOn G β B ∅ Finset.univ) j

/-- The partial derivative `∂F/∂B_k` at `B` of a function `F` of the field vector:
`d/dt F(B + t e_k)` at `t = 0`. -/
noncomputable def partialDeriv {V : Type*} [DecidableEq V] (k : V) (F : (V → ℝ) → ℝ)
    (B : V → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (B + t • Pi.single k (1 : ℝ))) 0

end IsingLTL.BeliefProp


