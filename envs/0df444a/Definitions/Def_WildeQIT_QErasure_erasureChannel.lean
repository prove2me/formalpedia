-- Prove2me | Definitions.Def_WildeQIT_QErasure_erasureChannel
-- name    : WildeQIT_QErasure_erasureChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:20.782446+00:00
-- url     : https://prove2.me/theorems/258f5a81-db97-4be1-a429-5f8e73a1c4a2
-- title:
--   The quantum erasure channel with erasure probability $\varepsilon$
-- statement:
--   Let $A'$ be a finite-dimensional input system with orthonormal basis $\{|i\rangle\}_{i\in a}$, so $d_A=|a|$, and let $\varepsilon\in[0,1]$. The **quantum erasure channel** $\mathcal N_{A'\to B}$ maps an input density operator $\rho_{A'}$ to
--
--   $$
--   \rho_{A'}\;\longmapsto\;(1-\varepsilon)\,\rho_B+\varepsilon\,|e\rangle\langle e|_B ,
--   $$
--
--   where the output system $B$ is spanned by the input basis together with an erasure state $|e\rangle_B$ orthogonal to the support of every input state. With probability $1-\varepsilon$ the state arrives intact, and with probability $\varepsilon$ it is replaced by the erasure flag.
--
--   This is the channel whose quantum capacity the mission computes.
--
--   **Formalization Note** The output basis is indexed by `Option a`: `some i` is $|i\rangle$ and `none` is $|e\rangle$. The channel is given in Kraus form by $\sqrt{1-\varepsilon}\,\iota$ ($\iota$ the inclusion of the input space) and $\sqrt\varepsilon\,|e\rangle\langle i|$ for $i\in a$, so that $\mathcal N(\rho)=(1-\varepsilon)\iota\rho\iota^\dagger+\varepsilon\,\mathrm{Tr}\{\rho\}|e\rangle\langle e|$, which is the map above on every density operator.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.7.1, (24.121), p. 677

import Definitions.Def_WildeQIT_QChannel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.7.1, p. 677, eq. (24.121)
(the quantum erasure channel).
-/

open Matrix

namespace WildeQIT.QErasure

/-- **The quantum erasure channel** `N_{A′→B}` with erasure probability `ε` (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.7.1, p. 677, (24.121)):
`ρ_{A′} ↦ (1 − ε) ρ_B + ε |e⟩⟨e|_B`, "where `ε ∈ [0, 1]` is the erasure probability and `|e⟩_B` is
an erasure state that is orthogonal to the support of any input state `ρ`".

**Formalization Note.** The input system `A′` is indexed by an arbitrary finite type `a`, so its
dimension is `d_A = |a|`. The output system `B` is indexed by `Option a`: `some i` is the input basis
vector `|i⟩` and `none` is the erasure state `|e⟩`, orthogonal to the input space. The channel is
given by the Kraus operators `√(1 − ε) ι` (label `none`, `ι` the inclusion of the input space) and
`√ε |e⟩⟨i|` (label `some i`), so that `N(ρ) = (1 − ε) ι ρ ι† + ε Tr{ρ} |e⟩⟨e|`, which is
`(1 − ε) ρ + ε |e⟩⟨e|` on every density operator. The hypotheses `0 ≤ ε ≤ 1` are the book's
`ε ∈ [0, 1]`. -/
noncomputable def erasureChannel (a : Type) [Fintype a] [DecidableEq a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) : QChannel a (Option a) where
  ι := Option a
  K k := match k with
    | none => Matrix.of fun y x => if y = some x then ((Real.sqrt (1 - ε) : ℝ) : ℂ) else 0
    | some i => Matrix.of fun y x => if y = none ∧ x = i then ((Real.sqrt ε : ℝ) : ℂ) else 0
  complete := by
    ext x x'
    have hs1 : ((Real.sqrt (1 - ε) : ℝ) : ℂ) * ((Real.sqrt (1 - ε) : ℝ) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hs2 : ((Real.sqrt ε : ℝ) : ℂ) * ((Real.sqrt ε : ℝ) : ℂ) = ((ε : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
    simp only [Matrix.sum_apply, Fintype.sum_option, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    by_cases hx : x = x'
    · subst hx
      simp [hs1, hs2, apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq]
    · simp [hx, apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, Matrix.one_apply_ne hx]
      intro h
      exact absurd h.symm hx

end WildeQIT.QErasure


