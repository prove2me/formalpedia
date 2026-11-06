-- Prove2me | Definitions.Def_SpinGirth5_heatBath
-- name    : SpinGirth5_heatBath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:41.726763+00:00
-- url     : https://prove2.me/theorems/9fdee32c-ef96-4ce5-b039-90a8ed7b28a1
-- title:
--   Heat-bath operators $P_v$, Laplacians $L_v$, $L_B$, pinnings, Poincaré inequality and conditional independence
-- statement:
--   Let $\mu$ be a probability mass function on configurations $\sigma\in[q]^V$ of a finite vertex set $V$. This module fixes the analytic vocabulary of the paper.
--
--   1. **Conditional expectation.** For $S\subseteq V$, $\mathbb E_\mu[f(X)\mid X_S=x_S]$ is the $\mu$-weighted average of $f$ over the configurations that agree with $x$ on $S$.
--   2. **Heat-bath operator** (Eq. (7)): $(P_vf)(x):=\mathbb E_\mu[f(X)\mid X_{V\setminus\{v\}}=x_{V\setminus\{v\}}]$, i.e. resample the colour of $v$ from its conditional law.
--   3. **Laplacians** (Eqs. (8)–(10)): $L_v:=\mathrm{Id}-P_v$, $L_B:=\sum_{v\in B}L_v$, and $L:=L_V$, the Laplacian of the continuous-time Glauber dynamics.
--   4. **Pinning.** For $\Lambda\subseteq V$ and a configuration $x$, the conditioned law $\mu(\cdot\mid X_\Lambda=x_\Lambda)$; the pinning $\tau=x_\Lambda$ is feasible when $\mu(x)>0$ for some such $x$.
--   5. **Centering and the Poincaré inequality.** $f\perp\mathbf 1$ means $\langle f,\mathbf 1\rangle_\mu=\mathbb E_\mu f=0$, where $\langle f,g\rangle_\mu=\sum_x\mu(x)f(x)g(x)$. A Laplacian $\mathcal L$ has spectral gap at least $\gamma$ when
--   $$\gamma\,\langle f,f\rangle_\mu\le\langle f,\mathcal Lf\rangle_\mu\qquad\text{for all } f\perp\mathbf 1 .$$
--   6. **Irreducibility.** The Glauber dynamics of $\mu$ is irreducible when the heat-bath Glauber chain restricted to $\operatorname{supp}\mu$ is irreducible.
--   7. **Conditional independence** (Definition 19): $X_u\perp\!\!\!\perp X_w\mid X_{V\setminus\{u,w\}}$ whenever $\operatorname{dist}_G(u,w)\ge 2$.
--   8. The closed neighbourhood $N[v]=N(v)\cup\{v\}$.
--
--   **Formalization Note** $L^2(\mu)$ is realized as all real functions on $[q]^V$ with the $\mu$-weighted form `MarkovMixing.innerPi`; values outside $\operatorname{supp}\mu$ never enter. Pinned laws are kept on the full configuration space, supported on the configurations that extend the pinning. Conditional independence of $X_u,X_w$ given the rest is written as the vanishing of all $2\times 2$ minors of $(a,b)\mapsto\mu(a,b,\text{rest})$, which for a nonnegative $\mu$ is the same thing. The irreducibility predicate uses the published `MarkovMixing.glauber` and `MarkovMixing.subChain`.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §2.1, pp.9–10; §2.4, p.12; §2.5, Eqs. (7)–(10), pp.13–14; Definition 19, p.14

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_mm_mcmc

namespace SpinGirth5

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The conditional expectation `E_μ[f(X) | X_S = x_S]` of `f` under a (nonnegative, normalized)
mass function `μ` on configurations `V → [q]`, given the coordinates in `S`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §2.1, pp.9–10 (conditioning on a pinning) and §2.5, Eq. (7), p.13.

**Formalization Note** The value is meaningful at `x ∈ supp μ`, where the denominator is
positive; elsewhere it is Lean's junk value `·/0 = 0`. Every statement of the mission uses it only
through `μ`-weighted sums, which ignore configurations outside `supp μ`. -/
noncomputable def condExp (μ : (V → Fin q) → ℝ) (S : Finset V) (f : (V → Fin q) → ℝ)
    (x : V → Fin q) : ℝ :=
  (∑ y ∈ univ.filter (fun y : V → Fin q => ∀ w ∈ S, y w = x w), μ y * f y) /
    ∑ y ∈ univ.filter (fun y : V → Fin q => ∀ w ∈ S, y w = x w), μ y

/-- The **single-site heat-bath operator** `(P_v f)(x) := E_μ[f(X) | X_{V∖{v}} = x_{V∖{v}}]`
(Chen, Liu, arXiv:2608.25491, Eq. (7), p.13). It is the same conditional average that
`MarkovMixing.glauber μ` performs at site `v`. -/
noncomputable def heatBath (μ : (V → Fin q) → ℝ) (v : V) (f : (V → Fin q) → ℝ) :
    (V → Fin q) → ℝ :=
  condExp μ (univ.erase v) f

/-- The **single-site Laplacian** `L_v := Id − P_v` (Chen, Liu, arXiv:2608.25491, Eq. (8),
p.13). -/
noncomputable def singleLap (μ : (V → Fin q) → ℝ) (v : V) (f : (V → Fin q) → ℝ) :
    (V → Fin q) → ℝ :=
  fun x => f x - heatBath μ v f x

/-- `L_B := ∑_{v ∈ B} L_v` for a set of sites `B` (Chen, Liu, arXiv:2608.25491, Eq. (9),
p.13). With `B = V` it is the Laplacian `L` of the continuous-time Glauber dynamics, Eq. (10),
p.13. -/
noncomputable def lapSum (μ : (V → Fin q) → ℝ) (B : Finset V) (f : (V → Fin q) → ℝ) :
    (V → Fin q) → ℝ :=
  fun x => ∑ u ∈ B, singleLap μ u f x

/-- The law `μ(· | X_Λ = x_Λ)` of a configuration conditioned on the **pinning** `τ = x_Λ` on the
set `Λ` (Chen, Liu, arXiv:2608.25491, §2.1, pp.9–10).

**Formalization Note** The conditioned law is kept on the full configuration space `V → [q]`,
where it is supported on the configurations that agree with `x` on `Λ`; its restriction to the
free coordinates `V ∖ Λ` is the paper's `μ^τ_{V∖Λ}`. The pinning is feasible
(`μ_Λ(τ) > 0`) exactly when some `x` with `μ x > 0` induces it. -/
noncomputable def pin (μ : (V → Fin q) → ℝ) (Λ : Finset V) (x : V → Fin q) :
    (V → Fin q) → ℝ :=
  fun y => if ∀ w ∈ Λ, y w = x w then
    μ y / ∑ z ∈ univ.filter (fun z : V → Fin q => ∀ w ∈ Λ, z w = x w), μ z
  else 0

/-- `f ⊥ 1` in `L²(μ)`, i.e. `E_μ[f] = ⟨f, 1⟩_μ = 0` (Chen, Liu, arXiv:2608.25491, §2.1,
p.10). -/
def IsCentered (μ : (V → Fin q) → ℝ) (f : (V → Fin q) → ℝ) : Prop :=
  MarkovMixing.innerPi μ f (fun _ => 1) = 0

/-- The **Poincaré inequality** with constant `γ` for a Laplacian `𝓛` in `L²(μ)`:
`γ ⟨f, f⟩_μ ≤ ⟨f, 𝓛 f⟩_μ` for every `f ⊥ 1`. "Spectral gap at least `γ`" means exactly this
(Chen, Liu, arXiv:2608.25491, §2.4, p.12: "1 − λ2(P) is the largest constant γ for which the
Poincaré inequality γ⟨f, f⟩µ ≤ ⟨f, Lf⟩µ, f ⊥ 1, holds").

**Formalization Note** `L²(μ)` is realized as all functions on `V → [q]` with the `μ`-weighted
form `MarkovMixing.innerPi μ`; values off `supp μ` do not enter any term. -/
def PoincareIneq (μ : (V → Fin q) → ℝ)
    (𝓛 : ((V → Fin q) → ℝ) → ((V → Fin q) → ℝ)) (γ : ℝ) : Prop :=
  ∀ f : (V → Fin q) → ℝ, IsCentered μ f →
    γ * MarkovMixing.innerPi μ f f ≤ MarkovMixing.innerPi μ f (𝓛 f)

/-- The heat-bath **Glauber dynamics of `μ` is irreducible**: the chain
`MarkovMixing.glauber μ`, restricted to the support `{x | 0 < μ x}`, is irreducible
(Chen, Liu, arXiv:2608.25491, Theorem 5, p.5, and Theorem 20, p.14). -/
def GlauberIrreducible (μ : (V → Fin q) → ℝ) : Prop :=
  MarkovMixing.Irreducible
    (MarkovMixing.subChain (MarkovMixing.glauber μ) (fun x : V → Fin q => 0 < μ x))

/-- **Conditional independence** (Definition 19): `X_u ⊥⊥ X_w | X_{V∖{u,w}}` whenever
`dist_G(u, w) ≥ 2`, i.e. `u ≠ w` and `u ≁ w`.

Chen, Liu, arXiv:2608.25491, Definition 19, p.14: "A Gibbs distribution µ on G is conditionally
independent if Xu ⊥⊥ Xv | X_{V∖{u,v}} whenever distG(u, v) ≥ 2".

**Formalization Note** For a nonnegative `μ`, independence of `X_u` and `X_w` given the rest
`X_{V∖{u,w}} = r` is the vanishing of every `2 × 2` minor of the matrix `(a, b) ↦ μ(a, b, r)`,
which is the identity required here (with `x` supplying `r`). Pairs in different components have
infinite distance and are included. -/
def CondIndep (G : SimpleGraph V) (μ : (V → Fin q) → ℝ) : Prop :=
  ∀ u w : V, u ≠ w → ¬ G.Adj u w → ∀ (x : V → Fin q) (a a' b b' : Fin q),
    μ (Function.update (Function.update x u a) w b) *
        μ (Function.update (Function.update x u a') w b') =
      μ (Function.update (Function.update x u a) w b') *
        μ (Function.update (Function.update x u a') w b)

/-- The closed neighbourhood `N[v] := N(v) ∪ {v}` (Chen, Liu, arXiv:2608.25491, §2.1, p.9). -/
def closedNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (G.neighborFinset v)

end SpinGirth5


