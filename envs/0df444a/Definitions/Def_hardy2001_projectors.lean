-- Prove2me | Definitions.Def_hardy2001_projectors
-- name    : hardy2001_projectors
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T10:06:09.977792+00:00
-- url     : https://prove2.me/theorems/214a9f4f-7c2a-43a8-bdad-60cb5d9ee00d
-- title:
--   Hardy's $N^2$ fiducial projectors $|n\rangle\langle n|$, $|mn\rangle_x\langle mn|$, $|mn\rangle_y\langle mn|$
-- statement:
--   Let $|1\rangle,\dots,|N\rangle$ be the standard orthonormal basis of $\mathbb C^N$. For $m<n$ put
--
--   $$|mn\rangle_x=\frac1{\sqrt2}\big(|m\rangle+|n\rangle\big),\qquad |mn\rangle_y=\frac1{\sqrt2}\big(|m\rangle+i|n\rangle\big).$$
--
--   For a vector $v\in\mathbb C^N$, $|v\rangle\langle v|$ denotes the $N\times N$ matrix with entries $v_j\overline{v_k}$. Hardy's **fiducial projectors** are the operators
--
--   $$|n\rangle\langle n|\ \ (1\le n\le N),\qquad |mn\rangle_x\langle mn|,\ \ |mn\rangle_y\langle mn|\ \ (1\le m<n\le N),$$
--
--   which number $N+2\binom N2=N^2$ in total. They are indexed by the disjoint union of $\{1,\dots,N\}$ with two copies of the set of pairs $m<n$.
--
--   Section 5 uses these projectors to put quantum theory in a form resembling classical probability theory: the state is the vector of the $N^2$ probabilities $p_k=\mathrm{tr}(\hat P_k\hat\rho)$.
--
--   **Formalization Note** Indices are `Fin N`, so $|n\rangle$ is `ket (n-1)`. The two copies of the pairs are labelled `false` ($x$) and `true` ($y$). The paper writes $|mn\rangle_x\langle mn|$ for the projector onto $|mn\rangle_x$, and similarly for $y$. `ket`, `ketX`, `ketY` and `proj` are also used directly in other statements of this mission.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 8, Section 5, Eqs. (26)–(27) and the surrounding text

import Mathlib

namespace HardyFiveAxioms

/-- The orthonormal basis vector `|n⟩ ∈ ℂᴺ`. -/
def ket {N : ℕ} (n : Fin N) : Fin N → ℂ :=
  Pi.single n 1

/-- `|mn⟩ₓ = (|m⟩ + |n⟩)/√2` (Hardy 2001, Section 5). -/
noncomputable def ketX {N : ℕ} (m n : Fin N) : Fin N → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (ket m + ket n)

/-- `|mn⟩_y = (|m⟩ + i|n⟩)/√2` (Hardy 2001, Section 5). -/
noncomputable def ketY {N : ℕ} (m n : Fin N) : Fin N → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (ket m + Complex.I • ket n)

/-- The operator `|v⟩⟨v|` on `ℂᴺ`, as the matrix with entries `vᵢ · conj(vⱼ)`. -/
def proj {N : ℕ} (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.vecMulVec v (star v)

/-- Index set of Hardy's `N²` fiducial projectors: one for each basis vector `n`, and two
(labelled `x` = `false`, `y` = `true`) for each pair `m < n`. -/
abbrev FiducialIndex (N : ℕ) : Type :=
  Fin N ⊕ ({p : Fin N × Fin N // p.1 < p.2} × Bool)

/-- Hardy's `N²` fiducial projectors (Hardy 2001, Eqs. (26)–(27)):
`|n⟩⟨n|` for `n = 1, …, N`, and `|mn⟩ₓ⟨mn|`, `|mn⟩_y⟨mn|` for `m < n`. -/
noncomputable def fiducialProjector {N : ℕ} : FiducialIndex N → Matrix (Fin N) (Fin N) ℂ
  | Sum.inl n => proj (ket n)
  | Sum.inr (p, false) => proj (ketX p.1.1 p.1.2)
  | Sum.inr (p, true) => proj (ketY p.1.1 p.1.2)

end HardyFiveAxioms


