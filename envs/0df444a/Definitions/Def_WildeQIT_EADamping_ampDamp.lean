-- Prove2me | Definitions.Def_WildeQIT_EADamping_ampDamp
-- name    : WildeQIT_EADamping_ampDamp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:53.488059+00:00
-- url     : https://prove2.me/theorems/bf436e3b-ca7b-4422-abd3-48c125f76462
-- title:
--   Amplitude damping channel $\mathcal N_{AD}$ with damping parameter $\gamma\in[0,1]$
-- statement:
--   For a damping parameter $\gamma\in[0,1]$, the **amplitude damping channel** $\mathcal N_{AD}$ acts on a qubit state $\rho$ as
--
--   $$
--   \mathcal N_{AD}(\rho)=A_0\rho A_0^\dagger+A_1\rho A_1^\dagger,\qquad A_0\equiv|0\rangle\langle0|+\sqrt{1-\gamma}\,|1\rangle\langle1|,\quad A_1\equiv\sqrt\gamma\,|0\rangle\langle1| .
--   $$
--
--   The Kraus operators satisfy $A_0^\dagger A_0+A_1^\dagger A_1=I$, so $\mathcal N_{AD}$ is a quantum channel. It models the decay of an excited state $|1\rangle$ to the ground state $|0\rangle$ with probability $\gamma$.
--
--   **Formalization Note** The qubit is indexed by `Fin 2` in the computational basis $|0\rangle,|1\rangle$, and the channel is a published `WildeQIT.QChannel` (Kraus form) with Kraus index `Fin 2`. The completeness relation needs $0\le\gamma\le1$, so the definition takes the hypothesis $\gamma\in[0,1]$ as an argument.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.6.2, p. 610, (21.150)–(21.151)

import Definitions.Def_WildeQIT_QChannel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.6.2, p. 610, (21.150)–(21.151)
(the amplitude damping channel; also §4.7).
-/

open Matrix

namespace WildeQIT.EADamping

/-- **Amplitude damping channel `N_AD`** with damping parameter `γ ∈ [0, 1]` (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.6.2, p. 610, (21.150)–(21.151)):
`N_AD(ρ) = A₀ ρ A₀† + A₁ ρ A₁†` on a qubit, with
`A₀ ≡ |0⟩⟨0| + √(1 − γ) |1⟩⟨1|` and `A₁ ≡ √γ |0⟩⟨1|`.

**Formalization Note.** The qubit is indexed by `Fin 2` (computational basis `|0⟩, |1⟩`); the
Kraus index is `Fin 2` with `K 0 = A₀`, `K 1 = A₁`. The completeness relation
`A₀†A₀ + A₁†A₁ = I` uses `0 ≤ γ ≤ 1`, the book's range, which is a hypothesis of the definition. -/
noncomputable def ampDamp (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : QChannel (Fin 2) (Fin 2) where
  ι := Fin 2
  K i := if i = 0 then !![1, 0; 0, ((Real.sqrt (1 - γ) : ℝ) : ℂ)]
    else !![0, ((Real.sqrt γ : ℝ) : ℂ); 0, 0]
  complete := by
    obtain ⟨h0, h1⟩ := hγ
    have e1 : ((Real.sqrt (1 - γ) : ℝ) : ℂ) * ((Real.sqrt (1 - γ) : ℝ) : ℂ) = 1 - γ := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
    have e2 : ((Real.sqrt γ : ℝ) : ℂ) * ((Real.sqrt γ : ℝ) : ℂ) = γ := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply, e1, e2,
        Complex.conj_ofReal]

end WildeQIT.EADamping


