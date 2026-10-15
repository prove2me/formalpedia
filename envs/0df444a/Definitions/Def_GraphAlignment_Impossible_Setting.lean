-- Prove2me | Definitions.Def_GraphAlignment_Impossible_Setting
-- name    : GraphAlignment_Impossible_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:45.194981+00:00
-- url     : https://prove2.me/theorems/901f12ed-9b07-4ac0-869a-47186f18d75c
-- title:
--   §2.2, §2.4, §3.1 — the correlated Erdős–Rényi model (n, q, s) with planted π*, the overlap β, the laws P, Q (3)–(4), algorithms, ℙ[β(π̂, π*) < α], M_α and the reference law 𝒬
-- statement:
--   This module sets up the correlated Erdős–Rényi model of Hall and Massoulié (§2.2, pp. 5–6; §2.4, p. 7) and the objects of the impossibility proof (§3).
--
--   **Edge laws.** Fix $q,s$ (the theorems assume $0\le q<s\le1$). The pair $(A_{ij},B'_{ij})\in\{0,1\}^2$ of a vertex pair has law $P$ of (3),
--   $$
--   p_{00}=1-2q+qs,\quad p_{01}=p_{10}=q(1-s),\quad p_{11}=qs,
--   $$
--   and two independent Bernoulli$(q)$ edges have law $Q$ of (4),
--   $$
--   q_{00}=1-2q+q^2,\quad q_{01}=q_{10}=q(1-q),\quad q_{11}=q^2 .
--   $$
--   $D(P\|Q)=\sum_{x}P(x)\log(P(x)/Q(x))$ (p. 8).
--
--   **The model.** The vertex set is $\{0,\dots,n-1\}$. A configuration $\omega$ assigns to every unordered pair $e=\{i,j\}$, $i\ne j$, a state $\omega_e=(A_e,B'_e)\in\{0,1\}^2$, and has probability $\prod_e P(\omega_e)$: the pairs are independent with law $P$. This gives the adjacency matrices $A$ of $G_A$ and $B'$ of $G_{B'}$ (symmetric, zero diagonal). For a permutation $\pi^*$, the graph $G_B$ relabels $G_{B'}$ by $\pi^*$: $B_{\pi^*(i)\pi^*(j)}=B'_{ij}$, i.e. $B_{kl}=B'_{\pi^{*-1}(k)\pi^{*-1}(l)}$. The observation is the pair $(A,B)$.
--
--   **Overlap** (p. 6). For permutations $\pi,\pi^*$,
--   $$
--   \beta(\pi,\pi^*)=\frac1n\sum_{i=1}^n\mathbf 1_{\pi(i)=\pi^*(i)} .
--   $$
--
--   **Algorithms and failure probability.** An algorithm on $n$ vertices is a stochastic kernel from observations $(A,B)$ to permutations $\hat\pi$; it may be randomized and sees nothing but $(A,B)$. With $\pi^*$ uniform on the $n!$ permutations,
--   $$
--   \mathbb P[\beta(\hat\pi,\pi^*)<\alpha]=\frac1{n!}\sum_{\pi^*}\sum_{\omega}\prod_e P(\omega_e)\sum_{\pi}\mathbb P(\hat\pi=\pi\mid (A,B))\,\mathbf 1\{\beta(\pi,\pi^*)<\alpha\}.
--   $$
--
--   **Laws of the observation.** $\mathbb P((A,B)=o\mid\pi^*)$ is the push-forward of the configuration law; the joint law of $(\pi^*,(A,B))$ multiplies it by $1/n!$. The reference law $\mathcal Q$ (§3.2, p. 12) is the law of the adjacency matrices of two independent Erdős–Rényi graphs $G(n,q)$, i.e. the push-forward of the product law $\prod_e Q(\omega_e)$ through $\omega\mapsto(A,B')$.
--
--   **The count $M_\alpha$** (Corollary 3.2, p. 11): $M_\alpha=\max_{\pi^*}|\{\pi\mid\beta(\pi,\pi^*)\ge\alpha\}|$; $M=n!$.
--
--   **Formalization Note** Vertices are `Fin n`; a vertex pair is an off-diagonal element of `Sym2 (Fin n)`; an edge state is `Bool × Bool` with first coordinate $A$ and second $B'$. $B$ is computed through `πs.symm`. The algorithm is a real stochastic kernel `Obs n → Perm (Fin n) → ℝ` whose argument is the observed pair $(A,B)$ only. For $n=0$ the overlap is $0$ (Lean's $1/0=0$); the asymptotic statements concern large $n$ only. $M_\alpha$ is a natural number computed as a `Finset.sup`.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, pp. 5–7, §2.2, (3)–(4); p. 8, §2.4.1; p. 11, Corollary 3.2; p. 12, §3.2 (𝒬)

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures

namespace GraphAlignment.Impossible

open Finset

/-- The law `P` of the edge pair `(A_ij, B′_ij)` in the correlated Erdős–Rényi model (3):
`p00 = 1 − 2q + qs`, `p01 = p10 = q(1 − s)`, `p11 = qs`. The first coordinate is `A_ij`,
the second `B′_ij`. -/
noncomputable def pLaw (q s : ℝ) : Bool × Bool → ℝ
  | (false, false) => 1 - 2 * q + q * s
  | (false, true) => q * (1 - s)
  | (true, false) => q * (1 - s)
  | (true, true) => q * s

/-- The law `Q` of two independent Bernoulli(`q`) edges (4):
`q00 = 1 − 2q + q²`, `q01 = q10 = q(1 − q)`, `q11 = q²`. -/
noncomputable def qLaw (q : ℝ) : Bool × Bool → ℝ
  | (false, false) => 1 - 2 * q + q ^ 2
  | (false, true) => q * (1 - q)
  | (true, false) => q * (1 - q)
  | (true, true) => q ^ 2

/-- `D(P ‖ Q) = ∑ₓ P(x) log (P(x) / Q(x))` for the laws (3)–(4) (natural logarithm). -/
noncomputable def klPQ (q s : ℝ) : ℝ := kl (pLaw q s) (qLaw q)

/-- Unordered pairs `{i, j}` of distinct vertices of `Fin n`. -/
abbrev Pair (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- A configuration: the edge states `(A_e, B′_e) ∈ Bool × Bool` of every vertex pair `e`. -/
abbrev Config (n : ℕ) := Pair n → Bool × Bool

/-- Product weight of a configuration when every pair independently has law `r`. -/
noncomputable def cfgLaw {n : ℕ} (r : Bool × Bool → ℝ) (ω : Config n) : ℝ :=
  ∏ e, r (ω e)

/-- Probability of a configuration under the correlated Erdős–Rényi model `(n, q, s)`:
`∏_e P(ω_e)`. -/
noncomputable def cfgProb {n : ℕ} (q s : ℝ) (ω : Config n) : ℝ := cfgLaw (pLaw q s) ω

/-- The pair `{i, j}` for `i ≠ j`. -/
def pairOf {n : ℕ} (i j : Fin n) (h : i ≠ j) : Pair n :=
  ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- Adjacency matrix `A` of `G_A` (symmetric, no self-loops). -/
def adjA {n : ℕ} (ω : Config n) (i j : Fin n) : Bool :=
  if h : i = j then false else (ω (pairOf i j h)).1

/-- Adjacency matrix `B′` of `G_{B′}` (symmetric, no self-loops). -/
def adjB' {n : ℕ} (ω : Config n) (i j : Fin n) : Bool :=
  if h : i = j then false else (ω (pairOf i j h)).2

/-- Adjacency matrix `B` of `G_B`, the relabeling of `G_{B′}` by `π*`:
`B_{π*(i) π*(j)} = B′_{ij}`, i.e. `B_{kl} = B′_{π*⁻¹(k) π*⁻¹(l)}`. -/
def adjB {n : ℕ} (πs : Equiv.Perm (Fin n)) (ω : Config n) (k l : Fin n) : Bool :=
  adjB' ω (πs.symm k) (πs.symm l)

/-- The observation space: pairs of adjacency matrices `(A, B)` on `Fin n`. -/
abbrev Obs (n : ℕ) := (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool)

/-- The observed pair `(A, B)` produced by configuration `ω` and planted permutation `π*`. -/
def obs {n : ℕ} (πs : Equiv.Perm (Fin n)) (ω : Config n) : Obs n := (adjA ω, adjB πs ω)

/-- The overlap `β(π, π*) = (1/n) ∑ᵢ 1{π(i) = π*(i)}`. -/
noncomputable def overlap {n : ℕ} (π πs : Equiv.Perm (Fin n)) : ℝ :=
  (1 / (n : ℝ)) * ((univ.filter fun i => π i = πs i).card : ℝ)

/-- A (possibly randomized) alignment algorithm on `n` vertices: a stochastic kernel from the
observed pair `(A, B)` to permutations `π̂` of `Fin n`. -/
abbrev Alg (n : ℕ) := StochKernel (Obs n) (Equiv.Perm (Fin n))

/-- `ℙ[β(π̂, π*) < α]` when `π*` is uniform on the `n!` permutations, `(A, B)` is drawn from the
correlated Erdős–Rényi model `(n, q, s)` with planted `π*`, and `π̂` is drawn from the algorithm's
kernel at `(A, B)`. -/
noncomputable def failProb {n : ℕ} (q s α : ℝ) (alg : Alg n) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ πs : Equiv.Perm (Fin n), ∑ ω : Config n,
    cfgProb q s ω * ∑ π : Equiv.Perm (Fin n),
      alg.k (obs πs ω) π * (if overlap π πs < α then 1 else 0)

/-- Conditional law `ℙ((A, B) = o | π* = πs)` of the observation. -/
noncomputable def condObs {n : ℕ} (q s : ℝ) (πs : Equiv.Perm (Fin n)) (o : Obs n) : ℝ :=
  ∑ ω : Config n, cfgProb q s ω * (if obs πs ω = o then 1 else 0)

/-- Joint law `ℙ(π* = πs, (A, B) = o)` with `π*` uniform on the `n!` permutations. -/
noncomputable def jointObs {n : ℕ} (q s : ℝ) (πs : Equiv.Perm (Fin n)) (o : Obs n) : ℝ :=
  (1 / (n.factorial : ℝ)) * condObs q s πs o

/-- The reference law `𝒬` on observations: the joint law of the adjacency matrices of two
independent Erdős–Rényi graphs `G(n, q)` (every pair independently has law `Q` of (4)). -/
noncomputable def qObs {n : ℕ} (q : ℝ) (o : Obs n) : ℝ :=
  ∑ ω : Config n, cfgLaw (qLaw q) ω * (if (adjA ω, adjB' ω) = o then 1 else 0)

/-- `M_α = max_{π*} |{π | β(π, π*) ≥ α}|`. -/
noncomputable def Mα (n : ℕ) (α : ℝ) : ℕ :=
  univ.sup fun πs : Equiv.Perm (Fin n) => (univ.filter fun π => α ≤ overlap π πs).card

end GraphAlignment.Impossible


