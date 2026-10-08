-- Prove2me | Definitions.Def_CompOT_W1_Defs
-- name    : CompOT_W1_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:09.560184+00:00
-- url     : https://prove2.me/theorems/05ffeef3-fc0e-4c7b-b331-2422b8691a37
-- title:
--   (5.1), p. 459, and §6.1, pp. 472–473 — the c-transform for the cost c = d, and the discrete objects of (6.2)
-- statement:
--   Let $(\mathcal X,d)$ be a metric space and take $\mathcal Y=\mathcal X$ with the **ground cost** $c(x,y)=d(x,y)$. For a real function $f$ on $\mathcal X$, its **$c$-transform** is the function
--
--   $$
--   f^c(y)=\inf_{x\in\mathcal X}\, d(x,y)-f(x),\qquad y\in\mathcal X,
--   $$
--
--   the infimum being taken in the extended real line $[-\infty,+\infty]$, so that it always exists. A function $f$ is $c$-concave when $f=g^c$ for some $g$.
--
--   For the discrete Kantorovich–Rubinstein formula the file also fixes, for $N$ points $z_1,\dots,z_N$ of $\mathcal X$ and histograms $a,b\in\mathbb R^N$:
--
--   1. the **couplings** $U(a,b)=\{P\in\mathbb R_+^{N\times N}: P\mathbb 1_N=a,\ P^\top\mathbb 1_N=b\}$;
--   2. the pairing $\langle C,P\rangle=\sum_{k,\ell}C_{k,\ell}P_{k,\ell}$, and the predicate "$P$ is an optimal coupling", i.e. $P\in U(a,b)$ attains $L_C(a,b)=\min_{Q\in U(a,b)}\langle C,Q\rangle$;
--   3. the **ground-cost matrix** $D_{k,\ell}=d(z_k,z_\ell)$;
--   4. the **1-Lipschitz potentials**: vectors $\mathbf f\in\mathbb R^N$ with $|\mathbf f_k-\mathbf f_\ell|\le d(z_k,z_\ell)$ for all $(k,\ell)$.
--
--   These are the objects of Proposition 6.1 and of the dual formula (6.2) for $\mathcal W_1$.
--
--   **Formalization Note** The $c$-transform is the published `MongeKantorovichYao.cConjugate` (Villani's $c$-conjugate, with the infimum in `EReal` over all $x$) instantiated at the cost $(x,y)\mapsto d(x,y)$; no junk value enters, since an unbounded-below family has infimum $-\infty$. The square-matrix coupling, pairing, and optimality objects are aliases of the shared Assignment definitions. Indices $\{1,\dots,N\}$ are `Fin N` (0-based).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (5.1), p. 459; §6.1, p. 472 (c(x, y) = d(x, y)); (2.10)–(2.11), pp. 370–371; (6.2), p. 473. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.W1

/-- §6.1, p. 472: the ground cost `c(x, y) = d(x, y)` on `X = Y`, as a function on `X × X`. -/
def distCost (X : Type*) [MetricSpace X] : X × X → ℝ :=
  fun p => dist p.1 p.2

/-- (5.1), p. 459, for the cost `c = d` on `X = Y`: the `c`-transform
`f^c(y) = inf_{x ∈ X} d(x, y) - f(x)`. It is the published
`MongeKantorovichYao.cConjugate` of `f` for the cost `distCost X`; the infimum is taken in
`EReal` over all `x ∈ X`, so it always exists (it is `⊥` when the family is unbounded below
and `⊤` only when `X` is empty). -/
noncomputable def cTransform {X : Type*} [MetricSpace X] (f : X → ℝ) (y : X) : EReal :=
  MongeKantorovichYao.cConjugate (distCost X) (fun x => (f x : EReal)) y

/-- (2.10), p. 370, for `n = m = N`: the couplings `U(a, b)`, nonnegative `N × N` matrices with
row sums `a` and column sums `b`. -/
def couplings {N : ℕ} (a b : Fin N → ℝ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  CompOT.Assignment.couplings a b

/-- The pairing `⟨C, P⟩ = ∑_{k,l} C_{k,l} P_{k,l}`. -/
def frob {N : ℕ} (C P : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  CompOT.Assignment.frob C P

/-- (2.11), p. 371: `P` attains the minimum `L_C(a, b)` of `⟨C, P⟩` over `U(a, b)`. -/
def IsOptimalCoupling {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N → ℝ)
    (P : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  CompOT.Assignment.IsOptimalCoupling C a b P

/-- The ground-cost matrix `D_{k,l} = d(z_k, z_l)` of points `z₁, …, z_N` of `X`. -/
def distMatrix {X : Type*} [MetricSpace X] {N : ℕ} (z : Fin N → X) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun k l => dist (z k) (z l)

/-- The constraint of (6.2), p. 473: `|f_k - f_l| ≤ d(z_k, z_l)` for all `(k, l)`. -/
def IsLipschitzPotential {X : Type*} [MetricSpace X] {N : ℕ} (z : Fin N → X)
    (f : Fin N → ℝ) : Prop :=
  ∀ k l, |f k - f l| ≤ dist (z k) (z l)

end CompOT.W1


