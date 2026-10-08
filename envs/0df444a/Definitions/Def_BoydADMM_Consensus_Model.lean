-- Prove2me | Definitions.Def_BoydADMM_Consensus_Model
-- name    : BoydADMM_Consensus_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:11.177893+00:00
-- url     : https://prove2.me/theorems/5bf72b26-afcf-489e-a753-c1539ae66c17
-- title:
--   Consensus, general form consensus and sharing ADMM (§7.1–§7.3): averages, soft thresholding, $k_g$ and the three run predicates
-- statement:
--   Throughout, vectors live in $\mathbb R^n$ with the Euclidean inner product and norm, and there are $N$ agents $i=1,\dots,N$.
--
--   1. **Average.** For vectors $v_1,\dots,v_N\in\mathbb R^n$, the overline denotes their average, $\bar v = \frac1N\sum_{i=1}^N v_i$ (§7.1, p. 50).
--   2. **Soft thresholding** (§4.4.3, p. 32). For $\kappa\in\mathbb R$ and $a\in\mathbb R$,
--   $$S_\kappa(a)=\begin{cases}a-\kappa & a>\kappa,\\ 0 & |a|\le\kappa,\\ a+\kappa & a<-\kappa.\end{cases}$$
--   3. **Global variable consensus ADMM** (§7.1, p. 49), for the problem of minimizing $\sum_i f_i(x_i)$ subject to $x_i - z = 0$. Given $\rho$, sequences $x_i^k$, $z^k$, $y_i^k$ form a run if for every $k\ge0$ and every $i$:
--   $$x_i^{k+1}\in\operatorname*{argmin}_{x_i}\big(f_i(x_i)+y_i^{kT}(x_i-z^k)+(\rho/2)\|x_i-z^k\|_2^2\big),$$
--   $$z^{k+1}=\frac1N\sum_{i=1}^N\big(x_i^{k+1}+(1/\rho)y_i^k\big),\qquad y_i^{k+1}=y_i^k+\rho(x_i^{k+1}-z^{k+1}).$$
--   4. **General form consensus** (§7.2, pp. 53–55). Local variable $i$ has dimension $n_i$ and its entry $j$ corresponds to the global entry $z_{\mathcal G(i,j)}$ of $z\in\mathbb R^n$; $\tilde z_i\in\mathbb R^{n_i}$ is given by $(\tilde z_i)_j = z_{\mathcal G(i,j)}$, and $k_g = \#\{(i,j) : \mathcal G(i,j)=g\}$. Sequences $x_i^k\in\mathbb R^{n_i}$, $z^k\in\mathbb R^n$, $y_i^k\in\mathbb R^{n_i}$ form a run if for every $k\ge 0$ and every $i$:
--   $$x_i^{k+1}\in\operatorname*{argmin}_{x_i}\big(f_i(x_i)+y_i^{kT}x_i+(\rho/2)\|x_i-\tilde z_i^k\|_2^2\big),\qquad z^{k+1}\in\operatorname*{argmin}_z\sum_{i=1}^N\big(-y_i^{kT}\tilde z_i+(\rho/2)\|x_i^{k+1}-\tilde z_i\|_2^2\big),$$
--   $$y_i^{k+1}=y_i^k+\rho(x_i^{k+1}-\tilde z_i^{k+1}).$$
--   5. **Sharing ADMM** (§7.3, p. 56), scaled form, for problem (7.12): minimize $\sum_i f_i(x_i)+g(\sum_i z_i)$ subject to $x_i-z_i=0$. The $z$-update objective is $g(\sum_i z_i)+(\rho/2)\sum_i\|z_i-a_i\|_2^2$. Sequences $x_i^k, z_i^k, u_i^k\in\mathbb R^n$ form a run if for every $k\ge0$ and every $i$:
--   $$x_i^{k+1}\in\operatorname*{argmin}_{x_i}\big(f_i(x_i)+(\rho/2)\|x_i-z_i^k+u_i^k\|_2^2\big),\qquad z^{k+1}\in\operatorname*{argmin}_{z}\Big(g\big(\textstyle\sum_{i} z_i\big)+(\rho/2)\sum_{i=1}^N\|z_i-u_i^k-x_i^{k+1}\|_2^2\Big),$$
--   $$u_i^{k+1}=u_i^k+x_i^{k+1}-z_i^{k+1}.$$
--
--   These are the objects every statement of the mission is written with.
--
--   **Formalization Note** Each extended-real-valued function $\varphi:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ of the book is encoded by its effective domain $\operatorname{dom}\varphi$ (a set) and its finite values on it (a real function); a minimization of a sum containing $\varphi$ is a minimization over $\operatorname{dom}\varphi$. The iterates are given sequences satisfying the update rules; they are never constructed, because the book's subproblems need not have minimizers (see p. 16). The starting state is $(z^0, y^0)$ (resp. $(z^0,u^0)$); $x^0$ is not used. Agents are indexed by `Fin N`, so the book's $i=1,\dots,N$ is Lean's $i-1$; likewise for the components $j$ and $g$. The book's p. 55 $x$-update writes $y_i^{kT}x_i$ (not $y_i^{kT}(x_i-\tilde z_i^k)$); the two differ by a constant in $x_i$, and the page's form is used. No convexity is assumed in the definitions; the statements of this mission do not need it.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 48–56, §7.1 (p. 49 algorithm, p. 50 overline), §7.2 (pp. 53–55, (7.9), 𝒢, k_g), §7.3 (p. 56, (7.12) and scaled ADMM); soft thresholding §4.4.3, p. 32

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

namespace BoydADMM.Consensus

open scoped BigOperators InnerProductSpace

/-- The overline average `v̄ = (1/N) ∑_{i=1}^N v_i` of `N` vectors (§7.1, p. 50). The `N`
agents are indexed by `Fin N`, so the book's `i = 1, …, N` is Lean's `i = 0, …, N - 1`. -/
noncomputable def avg {n N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (1 / (N : ℝ)) • ∑ i, v i

/-- Global variable consensus ADMM (§7.1, p. 49), unscaled form. Each `f_i` is given by its
effective domain `Cf i` and its finite values `f i` on it. `x k i`, `z k`, `y k i` are
`x_i^k`, `z^k`, `y_i^k`; `z 0` and `y 0` are the starting state and `x 0` is never used.
The `x`-update is an argmin over `dom f_i`; the `z`-update is the averaging step of the
printed algorithm; the `y`-update is the dual step. -/
structure IsConsensusADMMRun {n N : ℕ} (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ)
    (x : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) : Prop where
  x_mem : ∀ k i, x (k + 1) i ∈ Cf i
  x_min : ∀ k i, ∀ x' ∈ Cf i,
    f i (x (k + 1) i) + ⟪y k i, x (k + 1) i - z k⟫_ℝ + (ρ / 2) * ‖x (k + 1) i - z k‖ ^ 2 ≤
      f i x' + ⟪y k i, x' - z k⟫_ℝ + (ρ / 2) * ‖x' - z k‖ ^ 2
  z_succ : ∀ k, z (k + 1) = (1 / (N : ℝ)) • ∑ i, (x (k + 1) i + (1 / ρ) • y k i)
  y_succ : ∀ k i, y (k + 1) i = y k i + ρ • (x (k + 1) i - z (k + 1))

/-- General form consensus (§7.2, pp. 53–54): local variable `i` has dimension `nl i`, and
its component `j` copies the global component `G i j` of `z ∈ ℝⁿ`. The vector
`z̃_i ∈ ℝ^{n_i}` is `(z̃_i)_j = z_{G(i,j)}`. -/
noncomputable def ztil {n N : ℕ} {nl : Fin N → ℕ} (G : (i : Fin N) → Fin (nl i) → Fin n)
    (z : EuclideanSpace ℝ (Fin n)) (i : Fin N) : EuclideanSpace ℝ (Fin (nl i)) :=
  (EuclideanSpace.equiv (Fin (nl i)) ℝ).symm (fun j => z (G i j))

/-- The set of local entries `(i, j)` with `G(i, j) = g`. -/
def entriesOf {n N : ℕ} {nl : Fin N → ℕ} (G : (i : Fin N) → Fin (nl i) → Fin n) (g : Fin n) :
    Finset (Σ i : Fin N, Fin (nl i)) :=
  Finset.univ.filter (fun p => G p.1 p.2 = g)

/-- `k_g`, the number of local variable entries that correspond to the global entry `z_g`
(§7.2, p. 55). -/
def kg {n N : ℕ} {nl : Fin N → ℕ} (G : (i : Fin N) → Fin (nl i) → Fin n) (g : Fin n) : ℕ :=
  (entriesOf G g).card

/-- General form consensus ADMM (§7.2, p. 55), unscaled form, as printed: the `x_i`-update
minimizes `f_i(x_i) + y_i^{kT} x_i + (ρ/2)‖x_i − z̃_i^k‖²` over `dom f_i`, the `z`-update
minimizes `∑_i (−y_i^{kT} z̃_i + (ρ/2)‖x_i^{k+1} − z̃_i‖²)` over `z ∈ ℝⁿ`, and
`y_i^{k+1} = y_i^k + ρ(x_i^{k+1} − z̃_i^{k+1})`. -/
structure IsGeneralConsensusADMMRun {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n)
    (Cf : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (nl i))))
    (f : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)) → ℝ) (ρ : ℝ)
    (x : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) : Prop where
  x_mem : ∀ k i, x (k + 1) i ∈ Cf i
  x_min : ∀ k i, ∀ x' ∈ Cf i,
    f i (x (k + 1) i) + ⟪y k i, x (k + 1) i⟫_ℝ + (ρ / 2) * ‖x (k + 1) i - ztil G (z k) i‖ ^ 2 ≤
      f i x' + ⟪y k i, x'⟫_ℝ + (ρ / 2) * ‖x' - ztil G (z k) i‖ ^ 2
  z_min : ∀ k, ∀ z' : EuclideanSpace ℝ (Fin n),
    ∑ i, (-⟪y k i, ztil G (z (k + 1)) i⟫_ℝ + (ρ / 2) * ‖x (k + 1) i - ztil G (z (k + 1)) i‖ ^ 2) ≤
      ∑ i, (-⟪y k i, ztil G z' i⟫_ℝ + (ρ / 2) * ‖x (k + 1) i - ztil G z' i‖ ^ 2)
  y_succ : ∀ k i, y (k + 1) i = y k i + ρ • (x (k + 1) i - ztil G (z (k + 1)) i)

/-- The objective of the sharing `z`-update (§7.3, p. 56):
`g(∑_i z_i) + (ρ/2) ∑_i ‖z_i − a_i‖²`, where `g` is given by its finite values (its domain is
handled by the caller). -/
noncomputable def sharingZObj {n N : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) : ℝ :=
  g (∑ i, z i) + (ρ / 2) * ∑ i, ‖z i - a i‖ ^ 2

/-- Sharing ADMM (§7.3, p. 56), scaled form, for problem (7.12): `f_i` and `g` are given by
their effective domains `Cf i`, `Cg` and finite values `f i`, `g`. `x k i`, `z k i`, `u k i`
are `x_i^k`, `z_i^k`, `u_i^k`; `z 0`, `u 0` are the starting state and `x 0` is never used.
The `z`-update is an argmin over all `(z_1, …, z_N)` with `∑_i z_i ∈ dom g`. -/
structure IsSharingADMMRun {n N : ℕ} (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (Cg : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ)
    (x z u : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) : Prop where
  x_mem : ∀ k i, x (k + 1) i ∈ Cf i
  x_min : ∀ k i, ∀ x' ∈ Cf i,
    f i (x (k + 1) i) + (ρ / 2) * ‖x (k + 1) i - z k i + u k i‖ ^ 2 ≤
      f i x' + (ρ / 2) * ‖x' - z k i + u k i‖ ^ 2
  z_mem : ∀ k, (∑ i, z (k + 1) i) ∈ Cg
  z_min : ∀ k, ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), (∑ i, z' i) ∈ Cg →
    sharingZObj g ρ (fun i => u k i + x (k + 1) i) (z (k + 1)) ≤
      sharingZObj g ρ (fun i => u k i + x (k + 1) i) z'
  u_succ : ∀ k i, u (k + 1) i = u k i + x (k + 1) i - z (k + 1) i

end BoydADMM.Consensus


