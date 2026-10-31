-- Prove2me | Definitions.Def_RecursiveStopping_extendTop
-- name    : RecursiveStopping_extendTop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:23.134995+00:00
-- url     : https://prove2.me/theorems/663f986f-5dfd-4c29-87db-f0a68c9b19ae
-- title:
--   The filtration on $[0,\infty]$ with $\mathcal F_\infty=\bigvee_t\mathcal F_t$
-- statement:
--   Given a filtration $(\mathcal F_t)_{t\ge0}$, this is the filtration indexed by $[0,\infty]$ that equals $\mathcal F_t$ at finite times and $\mathcal F_\infty:=\bigvee_{t\ge0}\mathcal F_t$ at $t=\infty$.
--
--   It is the filtration with respect to which the paper's supermartingales "for $t\in[0,\infty]$" (p.9, Theorem 3.1, Lemma 3.3 (18)) are understood.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, p.5 (F_∞); p.9; Theorem 3.1, p.10; (18), p.11

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- The filtration `(F_t)_{t ∈ [0, ∞]}` obtained from `(F_t)_{t ≥ 0}` by adjoining
`F_∞ = ⋁_{t ≥ 0} F_t` (Colaneri & De Angelis, arXiv:1905.02650v4, p.5). It is the filtration of
the supermartingales "for `t ∈ [0, ∞]`" of p.9, Theorem 3.1 (p.10) and Lemma 3.3 (18) (p.11). -/
noncomputable def extendTop {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝔽 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0∞ mΩ where
  seq t := if t = ⊤ then ⨆ s, 𝔽 s else 𝔽 t.toNNReal
  mono' := by
    intro i j hij
    by_cases hj : j = ⊤
    · by_cases hi : i = ⊤
      · simp [hi, hj]
      · simp only [hi, hj, if_true, if_false]
        exact le_iSup (fun s => 𝔽 s) i.toNNReal
    · have hi : i ≠ ⊤ := ne_top_of_le_ne_top hj hij
      simp only [hi, hj, if_false]
      exact 𝔽.mono (ENNReal.toNNReal_mono hj hij)
  le' := by
    intro i
    by_cases hi : i = ⊤
    · simp only [hi, if_true]
      exact iSup_le 𝔽.le
    · simp only [hi, if_false]
      exact 𝔽.le _

end RecursiveStopping


