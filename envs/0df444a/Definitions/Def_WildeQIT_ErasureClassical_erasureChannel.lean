-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_erasureChannel
-- name    : WildeQIT_ErasureClassical_erasureChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:00.926485+00:00
-- url     : https://prove2.me/theorems/f7dce4b4-5aef-43fe-8d01-68cc4e771752
-- title:
--   The $d$-dimensional quantum erasure channel $\mathcal N^{\varepsilon}$
-- statement:
--   Let $d\ge 1$ and $\varepsilon\in[0,1]$. The **quantum erasure channel** $\mathcal N^{\varepsilon}$ takes a state $\rho$ of a $d$-dimensional system to
--
--   $$
--   \rho\;\longmapsto\;(1-\varepsilon)\,\rho+\varepsilon\,|e\rangle\langle e|,
--   $$
--
--   where $|e\rangle$ is an erasure symbol orthogonal to the input space. The output space is the $(d+1)$-dimensional space spanned by the input basis $|0\rangle,\dots,|d-1\rangle$ and $|e\rangle$. With probability $1-\varepsilon$ the state passes unchanged, and with probability $\varepsilon$ it is replaced by the flag $|e\rangle$, so that the receiver knows when an erasure occurred.
--
--   This is the channel whose classical capacity the mission computes.
--
--   **Formalization Note** The input is indexed by `Fin d` and the output by `Option (Fin d)`, with `some i` the basis vector $|i\rangle$ and `none` the erasure symbol $|e\rangle$. The channel is given in Kraus form by $\sqrt{1-\varepsilon}\,\iota$ (the inclusion of the input space) and $\sqrt\varepsilon\,|e\rangle\langle i|$ for $i<d$, so that $\mathcal N^\varepsilon(\rho)=(1-\varepsilon)\rho+\varepsilon\,\mathrm{Tr}\{\rho\}|e\rangle\langle e|$, which is the map above on every density operator. The hypotheses $0\le\varepsilon\le1$ are the book's and give the completeness relation.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.4.3, (20.85), p. 575 (recalled from §4.7.6)

import Definitions.Def_WildeQIT_QChannel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.4.3, p. 575, eq. (20.85)
(the qudit erasure channel, recalled from §4.7.6).
-/

open Matrix

namespace WildeQIT.ErasureClassical

/-- **The `d`-dimensional quantum erasure channel** `N^ε` (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §20.4.3, p. 575, (20.85)): `ρ ↦ (1 − ε)ρ + ε|e⟩⟨e|`, "where
`ρ` is a `d`-dimensional qudit input state, `ε ∈ [0, 1]`, and `|e⟩` is an erasure symbol
orthogonal to the input space of the channel".

**Formalization Note.** The input space is indexed by `Fin d`; the output space is indexed by
`Option (Fin d)`, where `some i` is the input basis vector `|i⟩` and `none` is the erasure
symbol `|e⟩`, orthogonal to the input space (output dimension `d + 1`). The channel is given by
the Kraus operators `√(1 − ε) ι` (Kraus label `none`, `ι` the inclusion of the input space) and
`√ε |e⟩⟨i|` (Kraus label `some i`), so that `N^ε(ρ) = (1 − ε) ι ρ ι† + ε Tr{ρ} |e⟩⟨e|`, which
is `(1 − ε)ρ + ε|e⟩⟨e|` on every density operator. The hypotheses `0 ≤ ε ≤ 1` are the book's
`ε ∈ [0, 1]` and are needed for the completeness relation. -/
noncomputable def erasureChannel (d : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    QChannel (Fin d) (Option (Fin d)) where
  ι := Option (Fin d)
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

end WildeQIT.ErasureClassical


