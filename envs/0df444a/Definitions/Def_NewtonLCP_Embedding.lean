-- Prove2me | Definitions.Def_NewtonLCP_Embedding
-- name    : NewtonLCP_Embedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:58.544638+00:00
-- url     : https://prove2.me/theorems/04dfd360-cca1-4074-b473-0eed0cf247c5
-- title:
--   The embedded system LCP$(\widehat M,\hat q)$ and its starting point (52)
-- statement:
--   Given $M\in\mathbb R^{n\times n}$, $q\in\mathbb R^n$ and $\Delta>0$, the **embedded system** is the LCP of size $2n$ with
--
--   $$\widehat M=\begin{pmatrix}M&I_n\\-I_n&0\end{pmatrix},\qquad \hat q=\begin{pmatrix}q\\\tilde q\end{pmatrix},$$
--
--   where, by (52),
--
--   $$x^0=2\Delta 1_n,\quad s^0=4\Delta^2n1_n,\quad \tilde x^0=s^0-Mx^0-q,\quad \tilde s^0=\frac{8n\Delta^3}{\tilde x^0},\quad \tilde q=x^0+\tilde s^0,\quad \hat\mu^0=8n\Delta^3,$$
--
--   and the starting point is $\hat x^0=(x^0,\tilde x^0)$, $\hat s^0=(s^0,\tilde s^0)$. Lemma 8.4 shows that this point lies on the central path of the embedded system and that solutions of the embedded system either solve LCP$(M,q)$ or certify that it has no solution.
--
--   **Formalization Note** The embedded index set is the disjoint union of two copies of $[n]$; $n$ in (52) is the original size. $\tilde s^0$ is an entrywise quotient.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), display (LCP(M̂, q̂)), p.29; Lemma 8.4, display (52), p.30

import Mathlib

open Matrix

namespace NewtonLCP

/-!
# The embedded system LCP(M̂, q̂) and its starting point (52)

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), §8.1, display (LCP(M̂, q̂)), p.29; Lemma 8.4,
display (52), p.30.

`M̂ = [[M, Iₙ], [−Iₙ, 0]]`, `q̂ = (q, q̃)`, and for a bound `∆`:
`x⁰ = 2∆1ₙ`, `s⁰ = 4∆²n1ₙ`, `x̃⁰ = s⁰ − Mx⁰ − q`, `s̃⁰ = 8n∆³/x̃⁰` (entrywise),
`q̃ = x⁰ + s̃⁰`, `µ̂⁰ = 8n∆³`; the starting point is `x̂⁰ = (x⁰, x̃⁰)`, `ŝ⁰ = (s⁰, s̃⁰)`.

**Formalization Note.** The embedded index set is `ι ⊕ ι` (first block `x`, second block `x̃`),
of size `2n`; `n = Fintype.card ι` is the original size, used in (52). Division is entrywise
real division.
-/

variable {ι : Type*} [Fintype ι]

/-- `M̂ = [[M, Iₙ], [−Iₙ, 0]]` (p.29). -/
def embedM [DecidableEq ι] (M : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks M 1 (-1) 0

/-- `x⁰ = 2∆1ₙ` (52). -/
def embX0 (Δ : ℝ) : ι → ℝ := fun _ => 2 * Δ

/-- `s⁰ = 4∆²n1ₙ` (52). -/
def embS0 (Δ : ℝ) : ι → ℝ := fun _ => 4 * Δ ^ 2 * (Fintype.card ι : ℝ)

/-- `x̃⁰ = s⁰ − Mx⁰ − q` (52). -/
def embXt0 (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι → ℝ :=
  embS0 Δ - M *ᵥ embX0 Δ - q

/-- `s̃⁰ = 8n∆³/x̃⁰` entrywise (52). -/
noncomputable def embSt0 (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι → ℝ :=
  fun i => 8 * (Fintype.card ι : ℝ) * Δ ^ 3 / embXt0 M q Δ i

/-- `q̃ = x⁰ + s̃⁰` (52). -/
noncomputable def embQt (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι → ℝ :=
  embX0 Δ + embSt0 M q Δ

/-- `q̂ = (q, q̃)` (p.29 with (52)). -/
noncomputable def embedQ (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim q (embQt M q Δ)

/-- `x̂⁰ = (x⁰, x̃⁰)` (52). -/
def embedX0 (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim (embX0 Δ) (embXt0 M q Δ)

/-- `ŝ⁰ = (s⁰, s̃⁰)` (52). -/
noncomputable def embedS0 (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim (embS0 Δ) (embSt0 M q Δ)

/-- `µ̂⁰ = 8n∆³` (52); `n` is the original size (`Fintype.card ι` in the statements). -/
def embedMu0 (n : ℕ) (Δ : ℝ) : ℝ :=
  8 * (n : ℝ) * Δ ^ 3

end NewtonLCP


