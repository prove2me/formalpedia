-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_Supplement_Letac
-- name    : GoldieRenewal_Implicit_Supplement_Letac
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:12:06.312005+00:00
-- url     : https://prove2.me/theorems/a5d60a77-0ded-4901-b61f-30d85e87429f
-- title:
--   Letac iterates (p. 128): backward Z_n(t) = Ψ₁ ∘ ⋯ ∘ Ψ_n(t) and forward W_n(t) = Ψ_n ∘ ⋯ ∘ Ψ₁(t)
-- statement:
--   Let $\Psi:\mathbb R\times\Omega\to\mathbb R$ be a random map and let $\Psi_1,\Psi_2,\dots$ be copies of it. The **backward iterates** are
--   $$
--   Z_n(t) := \Psi_1\circ\Psi_2\circ\cdots\circ\Psi_n(t) = \Psi_1(\Psi_2(\cdots\Psi_n(t)\cdots)),\qquad n=1,2,\dots,
--   $$
--   and the **forward iterates** are
--   $$
--   W_n(t) := \Psi_n\circ\Psi_{n-1}\circ\cdots\circ\Psi_1(t).
--   $$
--   Both start from $Z_0(t)=W_0(t)=t$. In $Z_n$ the newest map $\Psi_n$ is applied first, so $Z_{n+1}(t)=Z_n(\Psi_{n+1}(t))$; in $W_n$ it is applied last, so $W_{n+1}(t)=\Psi_{n+1}(W_n(t))$.
--
--   These are the sequences of Letac's principle (Theorem 2.1): the a.s. limit of $Z_n(t)$ gives the solution of the random equation $R\overset{L}{=}\Psi(R)$, and $W_n(t)$ is the corresponding random recurrence.
--
--   **Formalization Note** The random map is stored curried ($\Psi\,t\,\omega=\Psi(t,\omega)$) and the sequence of copies 0-based: the Lean index $i$ stands for the paper's $\Psi_{i+1}$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 128, §2 (iterates Z_n) and Theorem 2.1 (iterates W_n)

import Mathlib

namespace GoldieRenewal.Implicit.Supplement

/-! The iterates of Letac's principle (Goldie 1991, §2, p. 128).

A random map `Ψ : ℝ × Ω → ℝ` is stored curried, `Ψ : ℝ → Ω → ℝ` (`Ψ t ω = Ψ(t, ω)`). A sequence of
copies `Ψ₁, Ψ₂, …` is stored 0-based: `Ψs i` stands for the paper's `Ψ_{i+1}`. -/

/-- **Backward iterates** `Z_n(t) := Ψ₁ ∘ Ψ₂ ∘ ⋯ ∘ Ψ_n(t)` (Goldie 1991, p. 128). With 0-based
storage, `Z_0(t) = t` and `Z_{n+1}(t) = Z_n(Ψ_{n+1}(t))`, i.e. the newest map is applied first. -/
def backwardIter {Ω : Type*} (Ψs : ℕ → ℝ → Ω → ℝ) : ℕ → ℝ → Ω → ℝ
  | 0 => fun t _ => t
  | n + 1 => fun t ω => backwardIter Ψs n (Ψs n t ω) ω

/-- **Forward iterates** `W_n(t) := Ψ_n ∘ Ψ_{n−1} ∘ ⋯ ∘ Ψ₁(t)` (Goldie 1991, Theorem 2.1, p. 128).
With 0-based storage, `W_0(t) = t` and `W_{n+1}(t) = Ψ_{n+1}(W_n(t))`. -/
def forwardIter {Ω : Type*} (Ψs : ℕ → ℝ → Ω → ℝ) : ℕ → ℝ → Ω → ℝ
  | 0 => fun t _ => t
  | n + 1 => fun t ω => Ψs n (forwardIter Ψs n t ω) ω

end GoldieRenewal.Implicit.Supplement


