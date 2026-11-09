-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Correlation
-- name    : ParityBarrier563_Trilinear_Correlation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:00.090052+00:00
-- url     : https://prove2.me/theorems/2d737e34-4b83-4d1c-b99b-38ff8ea880f8
-- title:
--   §2, §4 — the CNF norm size_b, the correlation corr_b, the closure cl_b(S) and closure decompositions
-- statement:
--   Fix a finite set $V$ and an integer $b\ge0$.
--
--   1. For $b\ge1$ and $F:\{0,1\}^V\to\mathbb R$, the **CNF norm** $\mathrm{size}_b(F)$ is the smallest value of $\sum_j|c_j|$ over all ways to write $F=\sum_j c_jJ_j$ as a finite sum with real coefficients $c_j$ and indicators $J_j$ of $b$-CNFs on $\{0,1\}^V$.
--   2. For $\psi:\{0,1\}^V\to\mathbb R$, its **correlation against $b$-CNF tests** is
--   $$\mathrm{corr}_b(\psi)=\max_J\,\bigl|\mathbb E[\psi J]\bigr|,$$
--   the maximum over the Boolean indicators $J$ of $b$-CNFs on $\{0,1\}^V$.
--   3. For a set $S\subseteq\{0,1\}^V$, the **closure** $\mathrm{cl}_b(S):\{0,1\}^V\to\{0,1\}$ is the AND of all clauses of width at most $b$ that are satisfied by every point of $S$. It is a function on the whole cube; $\mathrm{cl}_b(\emptyset)$ is the constant $0$.
--   4. For real numbers $N,L$, every $b$-CNF on $\{0,1\}^V$ **is a sum of at most $N$ functions $\mathrm{cl}_b(S)$ with $|S|\le L$** if for each $b$-CNF $H$ there are $m\le N$ sets $S_1,\dots,S_m$ with $|S_i|\le L$ and $H=\sum_{i=1}^m\mathrm{cl}_b(S_i)$ pointwise as real numbers (so the pieces accept pairwise disjoint sets of points).
--
--   $\mathrm{size}_b$ measures how expensive a function is for $b$-CNF tests, by the inequality $|\mathbb E[\psi F]|\le\mathrm{size}_b(F)\,\mathrm{corr}_b(\psi)$; closures are the short descriptions that make a union bound over all $b$-CNFs affordable.
--
--   **Formalization Note** $\mathrm{size}_b$ is an infimum over representations; for $b\ge1$ (every use in the mission) representations exist (point indicators are $1$-CNFs), and the infimum is attained, since only finitely many functions on the cube are $b$-CNFs. $\mathrm{corr}_b$ is the supremum of a finite set that contains the value at the constant $1$ (the empty CNF), hence a maximum.
--
--   At $b=0$, a nonconstant function has no such representation and Lean returns $0$ for its empty real infimum; no theorem in this mission uses that out-of-domain value. For $b\ge1$ the representation costs are nonempty and bounded below by $0$. The point-list condition automatically forces every point of each $S_i$ to satisfy $H$, since $S_i$ is contained in its closure.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, §2 Preliminaries, printed p.10 (PDF p.12) for size_b and corr_b; §4, printed p.14 (PDF p.16) for cl_b(S); the decomposition property as in Corollary 4.3, printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_CNF

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! §2, printed p.10 / PDF 12 (`size_b`, `corr_b`) and §4, printed p.14 / PDF 16 (`cl_b(S)`). -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `size_b(F)`: the infimum of `∑_j |c_j|` over all finite representations
`F = ∑_j c_j J_j` with real coefficients `c_j` and Boolean indicators `J_j` of `b`-CNFs on
`{0,1}^V`. (For `b ≥ 1` representations exist, and the infimum is attained, since only finitely
many functions on `{0,1}^V` are `b`-CNFs.) -/
noncomputable def sizeB (b : ℕ) (F : RealFn V) : ℝ :=
  sInf {r : ℝ | ∃ (N : ℕ) (c : Fin N → ℝ) (J : Fin N → BoolFn V),
    (∀ j, IsCNF b (J j)) ∧ (∀ x, F x = ∑ j, c j * ind (J j) x) ∧ r = ∑ j, |c j|}

/-- `corr_b(ψ) = max_J |E[ψ J]|`, the maximum over the Boolean indicators `J` of `b`-CNFs on
`{0,1}^V` (a finite set containing the constant `1`, so this is a maximum). -/
noncomputable def corr (b : ℕ) (ψ : RealFn V) : ℝ :=
  sSup ((fun J : BoolFn V => |avg (fun x => ψ x * ind J x)|) '' {J | IsCNF b J})

/-- `cl_b(S) : {0,1}^V → {0,1}`, the AND of all clauses of width at most `b` that are satisfied
by every point of `S` (a function on the whole cube; `cl_b(∅)` is the constant false, since the
empty clause is satisfied by every point of `∅`). -/
noncomputable def closure (b : ℕ) (S : Finset (V → Bool)) : BoolFn V := by
  classical exact fun x => decide (∀ C : LitSet V, width C ≤ b →
    (∀ y ∈ S, ClauseSat C y) → ClauseSat C x)

/-- Every `b`-CNF on `{0,1}^V` is a sum of at most `N` functions `cl_b(S)` with `|S| ≤ L`:
pointwise, its `{0,1}` indicator equals the sum of the indicators of the pieces. -/
def HasClosureDecomp (b : ℕ) (V : Type) [Fintype V] [DecidableEq V] (N L : ℝ) : Prop :=
  ∀ H : BoolFn V, IsCNF b H → ∃ (m : ℕ) (S : Fin m → Finset (V → Bool)),
    (m : ℝ) ≤ N ∧ (∀ i, ((S i).card : ℝ) ≤ L) ∧
      ∀ x, ind H x = ∑ i, ind (closure b (S i)) x

end ParityBarrier563.Trilinear


