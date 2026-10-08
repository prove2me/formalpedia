-- Prove2me | Definitions.Def_MatousekLP_Codes_BoseMesner
-- name    : MatousekLP_Codes_BoseMesner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:02:18.07173+00:00
-- url     : https://prove2.me/theorems/ef05e3a8-285e-481f-89fa-e0a00e6d75a6
-- title:
--   Delsarte's matrices $M_i$, the quantities $\tilde y_i(C)$ and $\tilde M = \sum_i \tilde y_i M_i$
-- statement:
--   For $i \in \{0,\dots,n\}$, $M_i$ is the $2^n \times 2^n$ matrix whose rows and columns are indexed by the words of $\{0,1\}^n$ and
--   $$
--   (M_i)_{\mathbf v,\mathbf w} = \begin{cases} 1 & \text{if } d_H(\mathbf v,\mathbf w) = i,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   For a code $C \subseteq \{0,1\}^n$ and $i = 0,\dots,n$,
--   $$
--   \tilde y_i = \frac{\bigl|\{(\mathbf w,\mathbf w') \in C^2 : d_H(\mathbf w,\mathbf w') = i\}\bigr|}{2^n \binom{n}{i}},
--   $$
--   the probability that a random pair of words at Hamming distance $i$ is a pair of code words, and
--   $$
--   \tilde M = \sum_{i=0}^n \tilde y_i M_i .
--   $$
--   These are the objects of Delsarte's original proof of the linear programming bound, in which the matrices $M_i$ span the Bose–Mesner algebra of the Hamming scheme.
--
--   **Formalization Note** Matrices are real, indexed by `Fin n → Bool`. For $0 \le i \le n$ the denominator $2^n\binom ni$ is positive.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 163 (matrices M_i), p. 164 (ỹ_i), p. 165, Lemma 8.4.7 (M̃)

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic

open Finset

namespace MatousekLP.Codes

/-- The `2^n × 2^n` distance matrix `M_i` of p. 163, rows and columns indexed by the words
of `{0,1}^n`: `(M_i)_{v,w} = 1` if `d_H(v, w) = i` and `0` otherwise. -/
def distMatrix (n i : ℕ) : Matrix (Word n) (Word n) ℝ :=
  fun v w => if hammingDist v w = i then 1 else 0

/-- The quantity `ỹ_i` of p. 164 for a code `C`: the number of ordered pairs
`(w, w') ∈ C²` with `d_H(w, w') = i`, divided by `2^n (n choose i)`. For `0 ≤ i ≤ n` the
denominator is positive. -/
noncomputable def ytilde {n : ℕ} (C : Finset (Word n)) (i : ℕ) : ℝ :=
  (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ) / ((2 : ℝ) ^ n * (n.choose i : ℝ))

/-- The matrix `M̃ = ∑_{i=0}^n ỹ_i M_i` of Lemma 8.4.7 (p. 165). -/
noncomputable def Mtilde {n : ℕ} (C : Finset (Word n)) : Matrix (Word n) (Word n) ℝ :=
  ∑ i ∈ Finset.range (n + 1), ytilde C i • distMatrix n i

end MatousekLP.Codes


