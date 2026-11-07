-- Prove2me | Definitions.Def_RobustQSC_fourier
-- name    : RobustQSC_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:33.961187+00:00
-- url     : https://prove2.me/theorems/fff58ecb-2bf7-48e0-8dfc-1537b8d2e6a7
-- title:
--   Bit flip $x+i$ and the unitary Walsh–Hadamard transform $\hat f$
-- statement:
--   For $x\in\{0,1\}^n$ and $i\in[n]$, the string $x+i$ is $x$ with its $i$-th bit flipped. For $f:\{0,1\}^n\to\mathbb C$, the Fourier (Walsh–Hadamard) transform with the unitary normalization is
--
--   $$
--   \hat f(s)=2^{-n/2}\sum_{x\in\{0,1\}^n}f(x)(-1)^{s\cdot x},
--   $$
--
--   that is, $|\hat f\rangle=H^{\otimes n}|f\rangle$.
--
--   These two operations carry the whole paper: the local tests compare $f(x)$ with $f(x+i)$, and the $X$-basis test is the same test applied to $\hat f$.
--
--   **Formalization Note** Registers are the published `Qubits n = Fin n → Bool`, with `false` for $0$; $H^{\otimes n}$ is the published `hadamardN`.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §2.3, p.8; §3.1, pp.18–19; §4, p.21

import Definitions.Def_QAlgorithms_Defs_Gates

namespace RobustQSC

open QAlgorithms

/-- `x + i`: the string `x ∈ {0,1}ⁿ` with its `i`-th bit flipped.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §2.3, p.8 ("we use the shorthand
notation x + i to denote the string where we flip the i-th bit of x"); §3.1, p.19. -/
def flip {n : ℕ} (x : Qubits n) (i : Fin n) : Qubits n :=
  Function.update x i (!x i)

/-- The Fourier (Walsh–Hadamard) transform with the unitary normalization,
`f̂(s) = 2^{-n/2} Σ_x f(x) (-1)^{s·x}`, i.e. `|f̂⟩ = H^{⊗n}|f⟩`.

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), §2.3, p.8 ("the Fourier
transform b· will throughout bear the unitary normalization"), §3.1, p.18, §4, p.21
("Let |f̂⟩ = H^{⊗n}|f⟩").

**Formalization Note.** `hadamardN n` is the published `H^{⊗n}` with entries
`2^{-n/2}(-1)^{s·x}`. -/
noncomputable def fourier {n : ℕ} (f : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits n) :=
  act (hadamardN n) f

/-! ### Sanity tests -/

example {n : ℕ} (x : Qubits n) (i : Fin n) : flip (flip x i) i = x := by
  ext k
  by_cases h : k = i
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

example {n : ℕ} (x : Qubits n) (i : Fin n) : flip x i ≠ x := by
  intro h
  have := congrFun h i
  simp [flip] at this

end RobustQSC


