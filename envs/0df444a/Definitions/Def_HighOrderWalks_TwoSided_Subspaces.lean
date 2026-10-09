-- Prove2me | Definitions.Def_HighOrderWalks_TwoSided_Subspaces
-- name    : HighOrderWalks_TwoSided_Subspaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:21.721908+00:00
-- url     : https://prove2.me/theorems/a9deea61-dfa8-440b-9607-6ba94c6d9eb0
-- title:
--   §5.1, §5.3, Thm 5.6, pp. 14, 18–19 — C^k_0, the subspaces V^j_k and U^j_k, weighted projections, the constants ε_k
-- statement:
--   This file fixes the subspaces of §5.3 of Kaufman–Oppenheim, *High Order Random Walks: Beyond Spectral Gap*, on top of the objects of §2–§4 (the definitions file `Setting`).
--
--   **Cochains orthogonal to the constants (§5.1).** For $0\le k\le n-1$,
--   $$C^k_0(X,\mathbb R)=\Big\{\phi\in C^k(X,\mathbb R):\ \sum_{\sigma\in X(k)}m(\sigma)\phi(\sigma)=0\Big\}.$$
--   Orthogonal complements $S^\perp$ and orthogonal projections $P_S$ are taken in $C^k(X,\mathbb R)$ with the weighted inner product $\langle\phi,\psi\rangle=\sum_{\sigma\in X(k)}m(\sigma)\phi(\sigma)\psi(\sigma)$.
--
--   **The subspaces $V^j_k$ (§5.3).** Let $0\le k\le n-1$.
--   1. For $k=0$, $V^0_0=C^0_0(X)$.
--   2. For $1\le k\le n-1$ and $j=0,\dots,k-1$, $V^j_k=d_{k-1}\cdots d_j\big(C^j_0(X)\big)$, and $V^k_k=\ker(d^*_{k-1})$, the $k$-cochains $\phi$ with $d^*\phi=0$ on $X(k-1)$.
--
--   **The subspaces $U^j_k$ (§5.3).**
--   $$U^j_k=\begin{cases}V^0_k & j=0,\\ V^j_k\cap(V^{j-1}_k)^\perp & j=1,\dots,k-1,\\ V^k_k & j=k.\end{cases}$$
--
--   **Projections.** $u=P_S\phi$ means $u\in S$ and $\langle\phi-u,w\rangle=0$ for every $w\in S$.
--
--   **The constants of Theorem 5.6.** For $\lambda\in\mathbb R$,
--   $$\varepsilon_0=\lambda,\qquad \varepsilon_k=2k\big(1+2k\sqrt k\big)\varepsilon_{k-1}+(k+1)\lambda\quad(k>0).$$
--
--   **Incidence operator (§5.3, p. 18).** For $0\le j<k\le n$ and $\sigma\in X(k)$, $d_{j\nearrow k}\phi(\sigma)=\sum_{\tau\in X(j),\ \tau\subset\sigma}\phi(\tau)$.
--
--   These objects carry the statements of Theorem 5.6, Corollary 5.8 and Theorem 5.9: the spaces $U^j_k$ are the approximate eigenspaces of the upper random walk $M^+_k$.
--
--   **Formalization Note.** Cochains are functions `Finset V → ℝ`; `Supp X c φ` says that $\phi$ vanishes off the faces with $c$ vertices, so a $k$-cochain is a function with `Supp X (k + 1)`. Every subspace above consists of such functions: `C0`, `wPerp` and the kernel clause of `Vsp` carry `Supp` explicitly, and the images $d_{k-1}\cdots d_j(C^j_0)$ are supported on $X(k)$ because $d$ maps cochains on $X(j)$ to cochains on $X(j+1)$. Without `Supp`, a function living off the faces would have norm $0$ and enter every subspace. The page also writes $V^k_k=(V^{k-1}_k)^\perp$; the kernel form is used, which equals $(V^{k-1}_k)^\perp\cap C^k_0(X)$. The orthogonal projection is not defined as an operator: `IsWProj X m c S φ u` says $u=P_S\phi$, and statements read "for every $u$ with `IsWProj … φ u`"; on these finite-dimensional subspaces the weighted projection exists and is unique (the weight is positive on faces). `eps lam k` is $\varepsilon_k$, defined by the recursion with the index shifted by one: `eps lam (k + 1)` $=2(k+1)(1+2(k+1)\sqrt{k+1})\varepsilon_k+(k+2)\lambda$. `dUp X j φ` is $d_{j\nearrow k}\phi$, the degree $k$ being read from the face $\sigma$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, pp. 14, 18–19, §5.1 (C^k_0, p. 14), §5.3 (V^j_k, U^j_k, d_{j↗k}, p. 18), Theorem 5.6 (ε_k, p. 19)

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

namespace HighOrderWalks.TwoSided

/-- A cochain on the faces with `c` vertices: `φ` vanishes off `cells X c`. A `k`-cochain of the
paper is a function on `X(k) = HighOrderWalks.OneSided.cells X (k + 1)`; this predicate is what makes a function
`Finset V → ℝ` one, so that subspaces, eigenvectors and orthogonal complements are those of
`C^k(X, ℝ)`. -/
def Supp {V : Type*} (X : Finset (Finset V)) (c : ℕ) (φ : Finset V → ℝ) : Prop :=
  ∀ σ, φ σ ≠ 0 → σ ∈ HighOrderWalks.OneSided.cells X c

/-- §5.1, p. 14: `C^{c-1}_0(X, ℝ)`, the cochains on the faces with `c` vertices with
`Σ_{σ ∈ X(c-1)} m(σ) φ(σ) = 0` (weighted orthogonality to the constants). -/
def C0 {V : Type*} (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) : Set (Finset V → ℝ) :=
  {φ | Supp X c φ ∧ HighOrderWalks.OneSided.ip X m c φ (fun _ => 1) = 0}

/-- The `m`-weighted orthogonal complement `S^⊥` inside the cochains on the faces with `c`
vertices. -/
def wPerp {V : Type*} (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (S : Set (Finset V → ℝ)) : Set (Finset V → ℝ) :=
  {φ | Supp X c φ ∧ ∀ ψ ∈ S, HighOrderWalks.OneSided.ip X m c φ ψ = 0}

/-- §5.3, p. 18: the subspaces `V^j_k ⊆ C^k_0(X)` (`k`-cochains live on `cells X (k + 1)`):
1. for `k = 0`, `V^0_0 = C^0_0(X)`;
2. for `k ≥ 1` and `j < k`, `V^j_k = d_{k-1} ⋯ d_j (C^j_0(X))`;
3. for `k ≥ 1`, `V^k_k = ker(d*_{k-1})`, the `k`-cochains `φ` with `d*φ(τ) = 0` for every
   `τ ∈ X(k-1)`.
Only `j ≤ k` is meaningful; for `j > k` the value is the third clause and is never used. -/
noncomputable def Vsp {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ)
    (k j : ℕ) : Set (Finset V → ℝ) :=
  if k = 0 then C0 X m 1
  else if j < k then (HighOrderWalks.OneSided.dS X)^[k - j] '' C0 X m (j + 1)
  else {φ | Supp X (k + 1) φ ∧ ∀ τ ∈ HighOrderWalks.OneSided.cells X k, HighOrderWalks.OneSided.dStar X m φ τ = 0}

/-- §5.3, p. 18: `U^0_k = V^0_k`, `U^j_k = V^j_k ∩ (V^{j-1}_k)^⊥` for `0 < j < k` (weighted
complement inside `C^k(X)`), and `U^k_k = V^k_k`. -/
noncomputable def Usp {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ)
    (k j : ℕ) : Set (Finset V → ℝ) :=
  if j = 0 then Vsp X m k 0
  else if j < k then Vsp X m k j ∩ wPerp X m (k + 1) (Vsp X m k (j - 1))
  else Vsp X m k k

/-- `u` is the `m`-weighted orthogonal projection `P_S φ` of `φ` onto `S` (inner product of
cochains on the faces with `c` vertices): `u ∈ S` and `φ - u ⊥ S`. -/
def IsWProj {V : Type*} (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (S : Set (Finset V → ℝ)) (φ u : Finset V → ℝ) : Prop :=
  u ∈ S ∧ ∀ w ∈ S, HighOrderWalks.OneSided.ip X m c (φ - u) w = 0

/-- Theorem 5.6, p. 19: the constants `ε_0 = λ`, `ε_k = 2k(1 + 2k√k) ε_{k-1} + (k + 1) λ` for
`k > 0`; here written with the index shifted by one, `eps lam (k + 1) = ε_{k+1}`. -/
noncomputable def eps (lam : ℝ) : ℕ → ℝ
  | 0 => lam
  | k + 1 => 2 * ((k : ℝ) + 1) * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) * eps lam k +
      ((k : ℝ) + 2) * lam

/-- §1 p. 4 and §5.3, p. 18: the incidence operator `d_{j↗k}` of the `j`-simplices in the
`k`-simplices, `d_{j↗k}φ(σ) = Σ_{τ ∈ X(j), τ ⊂ σ} φ(τ)`. Zero off `X`. -/
def dUp {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (j : ℕ) (φ : Finset V → ℝ) :
    Finset V → ℝ :=
  fun σ => if σ ∈ X then ∑ τ ∈ (HighOrderWalks.OneSided.cells X (j + 1)).filter (fun τ => τ ⊆ σ), φ τ else 0

end HighOrderWalks.TwoSided


