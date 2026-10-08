-- Prove2me | Definitions.Def_MartOT_Var_BadTuples
-- name    : MartOT_Var_BadTuples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:20.694442+00:00
-- url     : https://prove2.me/theorems/4e63c60b-0872-4f72-aa69-1efc91786dc9
-- title:
--   Proof of Lemma 1.11, p. 17 — the set M of n-tuples that carry a non-optimal finite measure
-- statement:
--   Fix a cost $c:\mathbb R\times\mathbb R\to\mathbb R$ and $n\in\mathbb N$. The set $M\subseteq(\mathbb R\times\mathbb R)^n$ consists of the $n$-tuples $p=((x_i,y_i))_{i=1}^n$ for which there is a finite measure $\alpha$ on $\mathbb R\times\mathbb R$ concentrated on $\{(x_i,y_i):i=1,\dots,n\}$ and a competitor $\alpha'$ of $\alpha$ (Definition 1.10) with strictly smaller cost:
--   $$M=\Big\{(x_i,y_i)_{i=1}^n:\ \exists\,\alpha,\ \operatorname{spt}\alpha\subseteq\{(x_i,y_i):i\le n\},\ \exists\,\alpha' \text{ competitor of }\alpha \text{ with } \int c\,d\alpha'<\int c\,d\alpha\Big\}.$$
--
--   These are the configurations of at most $n$ points that an optimal martingale transport plan must avoid; the proof of the variational lemma shows that an optimal plan gives them no room.
--
--   **Formalization Note** "$\operatorname{spt}\alpha\subseteq F$" for the finite (hence closed) set $F$ is written $\alpha(F^c)=0$, which is equivalent. The measure $\alpha$ is required to be finite; the page says "a measure", and its proof only uses finite ones (the uniform measures $\alpha_p$). Costs are extended-real integrals; for the finite, finitely supported measures involved they are finite sums.
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, p. 17 (definition of the Borel set M)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Var

open MeasureTheory

/-- The set `M` of the proof of Lemma 1.11 (§3, p. 17), for a fixed `n`: the `n`-tuples
`p = ((x_i, y_i))_{i=1}^n` of points of `ℝ × ℝ` that carry a finite measure `α` concentrated on
`{p_1, …, p_n}` which some competitor `α'` beats, `∫ c dα' < ∫ c dα`. -/
def BadTuples (c : ℝ → ℝ → ℝ) (n : ℕ) : Set (Fin n → ℝ × ℝ) :=
  {p | ∃ α : Measure (ℝ × ℝ), IsFiniteMeasure α ∧ α (Set.range p)ᶜ = 0 ∧
    ∃ α' : Measure (ℝ × ℝ), IsCompetitor α α' ∧ cost c α' < cost c α}

end MartOT.Var


