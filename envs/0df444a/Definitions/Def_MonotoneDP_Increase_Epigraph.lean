-- Prove2me | Definitions.Def_MonotoneDP_Increase_Epigraph
-- name    : MonotoneDP_Increase_Epigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:56:10.036612+00:00
-- url     : https://prove2.me/theorems/7e05247e-9062-497f-b3b0-8fcb963ebaaf
-- title:
--   Epigraphs E(J), the sets C_k, projections P(·) and the closure in λ of P(·)
-- statement:
--   The sets Bertsekas (1977) uses to characterize convergence of the dynamic programming algorithm under Assumption I. Throughout, $\lambda$ ranges over the real line $(-\infty,\infty)$.
--
--   1. The **epigraph** of $J\in F$:
--   $$E(J)=\{(x,\lambda)\in S\times(-\infty,\infty)\mid J(x)\le\lambda\}.$$
--   2. For each $k\ge1$, the subset of $S\times C\times(-\infty,\infty)$
--   $$C_k=\{(x,u,\lambda)\mid H[x,u,T^{k-1}(\bar J)]\le\lambda,\ x\in S,\ u\in U(x)\}.$$
--   3. The **projection** of a set $A\subseteq S\times C\times(-\infty,\infty)$ on $S\times(-\infty,\infty)$ through admissible controls:
--   $$P(A)=\{(x,\lambda)\mid\exists u\in U(x)\ \text{s.t.}\ (x,u,\lambda)\in A\}.$$
--   It is applied to $A=C_k$ and to $A=\bigcap_{k=1}^\infty C_k$.
--   4. For $B\subseteq S\times(-\infty,\infty)$, the set
--   $$\overline{B}=\{(x,\lambda)\mid\exists\{\lambda_n\}\ \text{s.t.}\ \lambda_n\to\lambda,\ (x,\lambda_n)\in B,\ n=0,1,\dots\},$$
--   applied to $B=P(C_k)$ and $B=P(\bigcap_{k=1}^\infty C_k)$.
--
--   $\overline{P(C_k)}$ adds to $P(C_k)$, for each $x$, the possibly missing end point of the half line $\{\lambda\mid(x,\lambda)\in P(C_k)\}$. Comparing $P(\cdot)$ and $\overline{P(\cdot)}$ of $\bigcap_k C_k$ with the intersections of $\overline{P(C_k)}$ expresses whether projection and intersection may be interchanged, which is how the paper characterizes $J_\infty=J^*$.
--
--   **Formalization Note** $\overline{B}$ is a sequential closure in $\lambda$ at a fixed state $x$, with real $\lambda_n$ converging in $\mathbb R$; it is not the topological closure in $S\times\mathbb R$ (no topology on $S$ is involved). $C_k$ is defined for every natural $k$ with $T^{k-1}$ computed by natural-number subtraction, so the value at $k=0$ is a placeholder; every statement uses only $k\ge1$. $E$ and $\overline{\,\cdot\,}$ do not depend on the model and are stated for any type $S$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 456 (PDF p. 19), eq. (53); p. 457 (PDF p. 20), eqs. (55)–(57); p. 458 (PDF p. 21), eqs. (62)–(63). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model

namespace MonotoneDP.Increase

open Filter Topology

/-- The epigraph of `J ∈ F`, eq. (53): `E(J) = {(x, λ) | J(x) ≤ λ} ⊆ S × (−∞, ∞)`. -/
def E {S : Type*} (J : S → EReal) : Set (S × ℝ) := {p | J p.1 ≤ (p.2 : EReal)}

/-- The closure in `λ` at fixed `x` of eqs. (57) and (63):
`\overline{B} = {(x, λ) | ∃ {λ_n} s.t. λ_n → λ, (x, λ_n) ∈ B, n = 0, 1, …}`, with real `λ_n`
converging in `ℝ`. This is not the topological closure in `S × ℝ`. -/
def Pbar {S : Type*} (B : Set (S × ℝ)) : Set (S × ℝ) :=
  {p | ∃ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 p.2) ∧ ∀ n, (p.1, lam n) ∈ B}

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `C_k ⊆ S × C × (−∞, ∞)` of eq. (55), for `k ≥ 1`:
`C_k = {(x, u, λ) | H[x, u, T^{k−1}(J̄)] ≤ λ, x ∈ S, u ∈ U(x)}`.
Only indices `k ≥ 1` are used (at `k = 0` the natural-number subtraction makes `Ck 0 = Ck 1`,
which never occurs in a statement). -/
def Ck (k : ℕ) : Set (S × C × ℝ) :=
  {p | p.2.1 ∈ m.U p.1 ∧ m.H p.1 p.2.1 ((m.T)^[k - 1] m.Jbar) ≤ (p.2.2 : EReal)}

/-- The projection of `A ⊆ S × C × (−∞, ∞)` on `S × (−∞, ∞)` through admissible controls,
eqs. (56) and (62): `P(A) = {(x, λ) | ∃ u ∈ U(x) s.t. (x, u, λ) ∈ A}`. -/
def P (A : Set (S × C × ℝ)) : Set (S × ℝ) := {p | ∃ u ∈ m.U p.1, (p.1, u, p.2) ∈ A}

end Model

end MonotoneDP.Increase


