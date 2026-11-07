-- Prove2me | Definitions.Def_BlockSSM_Tracker
-- name    : BlockSSM_Tracker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:22.914146+00:00
-- url     : https://prove2.me/theorems/359e549b-0a44-4a15-835d-b5d749361d1b
-- title:
--   One-layer block-diagonal affine tracker
-- statement:
--   Let $G$ be a group of input symbols and $b$ a block bound. A **one-layer tracker** consists of a block partition $n=n_1+\dots+n_m$ with every $n_i\le b$, fixed across all symbols; for every $g\in G$ an affine transition
--   $$
--   f_g(h)=A_gh+c_g,\qquad A_g=\mathrm{diag}\bigl(A_g^{(1)},\dots,A_g^{(m)}\bigr),\quad A_g^{(i)}\in\mathbb C^{n_i\times n_i},\quad c_g\in\mathbb C^n;
--   $$
--   a start state $h_0\in\mathbb C^n$; and a decoder $\mathrm{dec}:\mathbb C^n\to G$. For a word $s=g_1\cdots g_T$ the **word map** is $F_s=f_{g_T}\circ\dots\circ f_{g_1}$, so the first letter acts first. The **hidden dimension** is $n=\sum_i n_i$, the number of complex scalar coordinates.
--
--   Transitions may be singular, and biases and decoder are unrestricted. This is the model whose minimal dimension the mission computes.
--
--   **Formalization Note** The bound $b$ lies in $\mathbb N\cup\{\infty\}$. The state space is the product of the spaces $\mathbb C^{n_i}$, and $m=0$ or a block of size $0$ is allowed, which gives hidden dimension zero. A word is a list with $g_1$ at the head.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3)

import Mathlib

universe u

namespace BlockSSM

/-- The hidden state space `ℂⁿ = ℂ^{n₁} × ⋯ × ℂ^{n_m}` of a block partition `n₁, …, n_m`. -/
abbrev State {m : ℕ} (n : Fin m → ℕ) : Type := ∀ i, Fin (n i) → ℂ

/-- **One-layer tracker.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3):
"Fix a block partition n = n₁ + ⋯ + n_m, with nᵢ ≤ b. For each g ∈ G, choose
f_g(h) = A_g h + c_g, A_g = diag(A_g⁽¹⁾, …, A_g⁽ᵐ⁾), A_g⁽ⁱ⁾ ∈ ℂ^{nᵢ×nᵢ}. Starting from h₀ ∈ ℂⁿ …"

A tracker over the alphabet `G` with block bound `b` consists of one partition `n` (the same for
all symbols), for every symbol one family of block matrices and one bias, a start state and a
decoder. "The partition is fixed across symbols. Individual transitions may be singular; biases and
the decoder are unrestricted."

**Formalization Note.** `b : ℕ∞`, so that every finite bound and the unbounded case are one
definition. The state space is `∀ i, Fin (n i) → ℂ`, so the linear part is block-diagonal by
construction. `m = 0` and blocks of size `0` are allowed (hidden dimension zero). -/
structure Tracker (G : Type u) (b : ℕ∞) where
  /-- The number of blocks. -/
  m : ℕ
  /-- The block sizes. -/
  n : Fin m → ℕ
  /-- Every block has size at most `b`. -/
  n_le : ∀ i, (n i : ℕ∞) ≤ b
  /-- The block matrices `A_g⁽ⁱ⁾`. -/
  A : G → ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ
  /-- The biases `c_g`. -/
  c : G → State n
  /-- The start state `h₀`. -/
  h₀ : State n
  /-- The decoder, an arbitrary function. -/
  dec : State n → G

variable {G : Type u} {b : ℕ∞}

/-- The transition `f_g(h) = A_g h + c_g`, computed block by block. -/
def Tracker.step (T : Tracker G b) (g : G) (h : State T.n) : State T.n :=
  fun i => (T.A g i).mulVec (h i) + T.c g i

/-- The word map `F_s = f_{g_T} ∘ ⋯ ∘ f_{g₁}` of the word `s = [g₁, …, g_T]`: the first letter of
the list is applied first. -/
def Tracker.wordMap (T : Tracker G b) (s : List G) (h : State T.n) : State T.n :=
  s.foldl (fun x g => T.step g x) h

/-- The hidden dimension `n = n₁ + ⋯ + n_m`: "Hidden dimension counts complex scalar coordinates." -/
def Tracker.hiddenDim (T : Tracker G b) : ℕ := ∑ i, T.n i

end BlockSSM


