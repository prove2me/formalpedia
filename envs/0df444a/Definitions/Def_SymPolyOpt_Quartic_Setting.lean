-- Prove2me | Definitions.Def_SymPolyOpt_Quartic_Setting
-- name    : SymPolyOpt_Quartic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:54.667783+00:00
-- url     : https://prove2.me/theorems/99a1e6d4-a83c-442b-971e-1d0456d4c7ed
-- title:
--   §5, pp. 21–22 — r-partitions ω, the restrictions f^ω, the sets K, K^ω and A_r, and the degree bound r
-- statement:
--   This file fixes the objects of §5 of Riener–Theobald–Jansson Andrén–Lasserre.
--
--   1. **r-partitions.** For $n, r \in \mathbb N$, an $r$-partition of $n$ is a vector $\omega = (\omega_1, \dots, \omega_r)$ of positive, non-increasing integers with $\omega_1 + \dots + \omega_r = n$; $\Omega$ is the set of all of them. An $r$-partition is encoded by its *block map* $b : \{1,\dots,n\} \to \{1,\dots,r\}$, which sends the first $\omega_1$ coordinates to block $1$, the next $\omega_2$ to block $2$, and so on. A map $b$ is a block map exactly when it is monotone, onto, and its fibre sizes $\omega_k = |b^{-1}(k)|$ are non-increasing in $k$; this is a bijection with $\Omega$.
--   2. **Restriction.** For $f \in \mathbb R[X_1, \dots, X_n]$ and an $r$-partition $\omega$ with block map $b$,
--   $$f^\omega := f(\underbrace{T_1, \dots, T_1}_{\omega_1}, \underbrace{T_2, \dots, T_2}_{\omega_2}, \dots, \underbrace{T_r, \dots, T_r}_{\omega_r}) = f(T_{b(1)}, \dots, T_{b(n)}) \in \mathbb R[T_1, \dots, T_r].$$
--   3. **Feasible sets.** For polynomials $g_1, \dots, g_m$ in $k$ variables, $K = \{x \in \mathbb R^k : g_1(x) \ge 0, \dots, g_m(x) \ge 0\}$ (all of $\mathbb R^k$ when $m = 0$). With $k = r$ and $g_j^\omega$ in place of $g_j$ this is $K^\omega$.
--   4. **Points with few distinct components.** $A_r \subseteq \mathbb R^n$ is the set of points with at most $r$ distinct components.
--   5. **The degree bound.** $r := \max\{2, \lfloor (\deg f)/2 \rfloor, \deg g_1, \dots, \deg g_m\}$, with $\deg$ the total degree.
--
--   These are the objects in which the degree principle (Proposition 5.1), the reduction (5.1) and Theorem 5.5 are stated.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin n) ℝ`, so variables and blocks are $0$-indexed. $f^\omega$ is `aeval (fun i => X (b i)) f`. The floor $\lfloor (\deg f)/2 \rfloor$ is natural-number division, which is the floor. The maximum over an empty list of constraints is $0$, so for $m = 0$ the bound is $\max\{2, \lfloor(\deg f)/2\rfloor\}$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 21, Proposition 5.1 and the definition of r-partitions and f^ω; p. 22, the definition of K^ω

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- An `r`-partition `ω = (ω_1, …, ω_r)` of `n` (positive, non-increasing parts summing to `n`),
encoded by its block map `b : Fin n → Fin r`: coordinate `i` lies in block `b i`. The map is
monotone (the blocks are consecutive runs of coordinates, filled in order), surjective (every part
`ω_k` is positive), and the block sizes `ω_k = #b⁻¹(k)` are non-increasing in `k`. -/
def IsBlockMap {n r : ℕ} (b : Fin n → Fin r) : Prop :=
  Monotone b ∧ Function.Surjective b ∧
    Antitone (fun k : Fin r => (Finset.univ.filter (fun i => b i = k)).card)

/-- `f^ω := f(T_1, …, T_1, T_2, …, T_2, …, T_r, …, T_r) ∈ ℝ[T_1, …, T_r]`, where `T_k` is
substituted for every variable `X_i` of block `k = b i`. -/
noncomputable def restrict {n r : ℕ} (b : Fin n → Fin r) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin r) ℝ :=
  aeval (fun i => (X (b i) : MvPolynomial (Fin r) ℝ)) f

/-- `A_r`: the points of `ℝ^n` with at most `r` distinct components. -/
def A (n r : ℕ) : Set (Fin n → ℝ) :=
  {x | (Finset.univ.image x).card ≤ r}

/-- `r := max{2, ⌊(deg f)/2⌋, deg g_1, …, deg g_m}` (degree = total degree; the floor is natural
number division). -/
noncomputable def degreeR {n m : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (g : Fin m → MvPolynomial (Fin n) ℝ) : ℕ :=
  max 2 (max (f.totalDegree / 2) (Finset.univ.sup fun j => (g j).totalDegree))

end SymPolyOpt.Quartic


