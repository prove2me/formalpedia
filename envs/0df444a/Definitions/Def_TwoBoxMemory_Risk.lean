-- Prove2me | Definitions.Def_TwoBoxMemory_Risk
-- name    : TwoBoxMemory_Risk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:03.81962+00:00
-- url     : https://prove2.me/theorems/98c5e399-dc3c-469c-8d4c-3505895fff20
-- title:
--   Conditional risks $J_A,J_B$ of command words and laws, and the value $V$
-- statement:
--   A stationary target is hidden at one of two locations $A$, $B$. A search at the correct location fails with probability $r$ (at $A$) or $s$ (at $B$), $r,s\in(0,1)$; a search at the wrong location always fails. Command $A$ costs $C>0$, command $B$ costs $D>0$, and the successful command is charged.
--
--   For an infinite command word $w=w_0w_1\cdots$ let $N_A(h)$, $N_B(h)$ be the numbers of $A$ and $B$ commands strictly before position $h$. Its **conditional risks** are
--
--   $$J_A(w)=\sum_{h\ge0}c(w_h)\,r^{N_A(h)},\qquad J_B(w)=\sum_{h\ge0}c(w_h)\,s^{N_B(h)},\qquad c(A)=C,\ c(B)=D.$$
--
--   For a probability law $P$ on infinite words, $J_h(P)=\mathbb E_P\,J_h(X)$. The **unrestricted value** is
--
--   $$V=\inf_{P}\max\bigl(J_A(P),J_B(P)\bigr),$$
--
--   the infimum over all probability laws on infinite words.
--
--   These are the risks against which every memory bound of the mission is measured.
--
--   **Formalization Note** Commands are `Fin 2` with $0=A$, $1=B$. The word risk reuses the published `DiscreteSearchGame.Optimal.V` with time vector $(C,D)$ and detection probabilities $(1-r,1-s)$, whose terms are $c(w_m)(1-(1-r))^{N_A(m)}$. Risks take values in $[0,\infty]$; laws are probability measures on $\{A,B\}^{\mathbb N}$ with the product $\sigma$-algebra.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §2, display (2.1), p.2 (PDF 4); (B.4), p.21 (PDF 23)

import Mathlib
import Definitions.Def_DiscreteSearchGame_Optimal_Model

namespace TwoBoxMemory

/-!
# Conditional risks of command words and laws, and the unrestricted value `V`

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§2, display (2.1), p.2 (PDF 4); (B.4), p.21 (PDF 23).

A target sits at location `A` or `B`. A search at the correct location fails with probability `r`
(at `A`) or `s` (at `B`); a search at the wrong location always fails. Commands cost `C` (for `A`)
and `D` (for `B`), the successful command included. For an infinite command word `w`, with
`N_A(h)`, `N_B(h)` the numbers of `A`, `B` commands strictly before position `h`,
`J_A(w) = ∑_{h ≥ 0} c(w_h) r^{N_A(h)}` and `J_B(w) = ∑_{h ≥ 0} c(w_h) s^{N_B(h)}`.
Integration defines the risks of a probability law on words, and `V` is the smaller achievable
worst risk.

**Formalization Note.**
* Commands are `Fin 2` with `0 = A`, `1 = B`; times and counts are 0-based.
* `wordRisk` reuses the published `DiscreteSearchGame.Optimal.V` with time vector `![C, D]` and
  detection probabilities `![1 - r, 1 - s]`: its terms are `c(w_m) (1 - (1 - r))^{N_A(m)}`,
  i.e. exactly (2.1). `searchCount w m i` counts the positions `< m` carrying command `i`.
* Risks are in `ℝ≥0∞` (a word that neglects a location has infinite risk there).
* `value` is the infimum over **all** probability measures on `ℕ → Fin 2` (product σ-algebra of
  the discrete σ-algebra on `Fin 2`) of the larger of the two law risks. The index set is nonempty
  (Dirac masses) and the infimum is in `ℝ≥0∞`, so no junk value arises.
-/

open MeasureTheory

noncomputable section

/-- `J_h(w)` of (2.1): the conditional risk of the command word `w` when the target is at
location `h` (`0 = A`, `1 = B`). -/
def wordRisk (r s C D : ℝ) (h : Fin 2) (w : ℕ → Fin 2) : ENNReal :=
  DiscreteSearchGame.Optimal.V ![C, D] ![1 - r, 1 - s] h w

/-- `J_h(P) = 𝔼_P J_h(X)` of (B.4): the conditional risk of a law `P` on command words. -/
def lawRisk (r s C D : ℝ) (h : Fin 2) (P : Measure (ℕ → Fin 2)) : ENNReal :=
  ∫⁻ w, wordRisk r s C D h w ∂P

/-- The unrestricted minimax value `V`: the infimum over all probability laws on infinite command
words of the worst conditional risk `max(J_A, J_B)`. -/
def value (r s C D : ℝ) : ENNReal :=
  ⨅ (P : Measure (ℕ → Fin 2)) (_ : IsProbabilityMeasure P),
    max (lawRisk r s C D 0 P) (lawRisk r s C D 1 P)

end

end TwoBoxMemory


