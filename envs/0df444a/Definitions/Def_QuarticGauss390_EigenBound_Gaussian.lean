-- Prove2me | Definitions.Def_QuarticGauss390_EigenBound_Gaussian
-- name    : QuarticGauss390_EigenBound_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:41.728325+00:00
-- url     : https://prove2.me/theorems/f5a34daa-a05e-4b50-a89a-5a5fc9957395
-- title:
--   Def. 2.4 — pure fermionic Gaussian states, the Gaussian cone $\mathcal C_G$, and the Gaussian optimum $G(X)$
-- statement:
--   Fix a CAR system $c_1,\dots,c_{2n}$. For a real orthogonal matrix $O\in O(d)$ (either determinant), the rotated Majoranas and annihilation operators are
--   $$\tilde c_a=\sum_i O_{ai}c_i,\qquad \tilde a_j=\frac{\tilde c_{2j-1}+i\,\tilde c_{2j}}{2}\quad(j=1,\dots,n).$$
--   A state $|g\rangle$ (a unit vector) is a **pure Gaussian state** if for some $O\in O(d)$ it is a common vacuum: $\tilde a_j|g\rangle=0$ for all $j$.
--
--   The **Gaussian cone** $\mathcal C_G$ is the set of all complex multiples $\alpha|g\rangle$ of Gaussian states, including $0$. The **Gaussian optimum** of a Hermitian operator $X$ is
--   $$G(X)=\max_{|g\rangle\ \text{Gaussian}}\langle g|X|g\rangle .$$
--
--   Allowing both $\det O=\pm1$ includes both fermion parities (every Fock basis state is Gaussian). These notions define the benchmark $G(H)$ in the mission's goal.
--
--   **Formalization Note.** Paper indices $2j-1,2j$ become Lean indices $2j,2j+1$ with $j:\mathrm{Fin}\,n$. $G$ is the supremum of $\operatorname{Re}\langle g|X|g\rangle$ over Gaussian states; the set is nonempty (a CAR vacuum exists in dimension $2^n$) and bounded, and the paper notes the maximum is attained by compactness.
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.8, Definition 2.4; p.2, eq. (1.4) (G)

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lean index of the paper's Majorana `2j - 1` for mode `j` (paper `j = 1, …, n`; Lean `j : Fin n`). -/
def evenIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * j.val, by have := j.isLt; omega⟩

/-- Lean index of the paper's Majorana `2j` for mode `j`. -/
def oddIdx {n : ℕ} (j : Fin n) : Fin (2 * n) := ⟨2 * j.val + 1, by have := j.isLt; omega⟩

/-- Def. 2.4, p.8: rotated Majoranas `c̃_a = ∑_i O_{ai} c_i`. -/
noncomputable def rotMajorana {n : ℕ} (C : CAR n) (O : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) : Op n :=
  ∑ i, ((O a i : ℝ) : ℂ) • C.c i

/-- Def. 2.4, p.8: rotated annihilation operators `ã_j = (c̃_{2j-1} + i c̃_{2j}) / 2`. -/
noncomputable def rotAnnihilation {n : ℕ} (C : CAR n)
    (O : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (j : Fin n) : Op n :=
  (1 / 2 : ℂ) • (rotMajorana C O (evenIdx j) + Complex.I • rotMajorana C O (oddIdx j))

/-- Def. 2.4, p.8: a pure Gaussian state is a unit vector that is a common vacuum
`ã_j |g⟩ = 0` (all `j`) for some real orthogonal `O ∈ O(d)` (both determinants allowed). -/
def IsGaussian {n : ℕ} (C : CAR n) (g : Vec n) : Prop :=
  IsState g ∧ ∃ O ∈ Matrix.orthogonalGroup (Fin (2 * n)) ℝ,
    ∀ j : Fin n, rotAnnihilation C O j *ᵥ g = 0

/-- Def. 2.4, p.8: the Gaussian cone `𝒞_G`: all complex multiples of Gaussian states,
including zero. -/
def InGaussianCone {n : ℕ} (C : CAR n) (v : Vec n) : Prop :=
  v = 0 ∨ ∃ (α : ℂ) (g : Vec n), IsGaussian C g ∧ v = α • g

/-- eq. (1.4), p.2: the Gaussian optimum `G(X) = max_{|g⟩ Gaussian} ⟨g|X|g⟩`, as a supremum
(real part taken; the value is real for Hermitian `X`). -/
noncomputable def gaussOpt {n : ℕ} (C : CAR n) (X : Op n) : ℝ :=
  sSup {e : ℝ | ∃ g : Vec n, IsGaussian C g ∧ e = (star g ⬝ᵥ (X *ᵥ g)).re}

end QuarticGauss390.EigenBound


