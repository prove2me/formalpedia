-- Prove2me | Definitions.Def_SpencerEight_PrefixRun
-- name    : SpencerEight_PrefixRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:11.495276+00:00
-- url     : https://prove2.me/theorems/34b65bd8-07ef-4076-b152-7b2156af3da6
-- title:
--   Prefix of a signing schedule (Lemma 8.45)
-- statement:
--   A run of $r$ partial signings with congruence replacement, starting from a family $A$ of $n\times n$ matrices:
--
--   1. the level-$0$ family is $A$ and every index is active;
--   2. at step $i$, a partial signing with values in $\{-1,0,1\}$ of the active set of level $i-1$ produces $M_i:=\sum_j y_jB^{(i-1)}_j$, and the active set of level $i$ is the set of zero coordinates;
--   3. $\|M_i\|\le L_i\sqrt n$, $L_i>0$ and $C_i>0$;
--   4. every coefficient is replaced by $C_i\sqrt n\,H_i^{-1/2}B\,H_i^{-1/2}$, where $H_i:=C_{i-1}\sqrt n\,I-|M_i|$.
--
--   **Formalization Note** Steps are numbered from $0$ in the Lean index: index $i<r$ is step $i+1$. The equations determine the active sets and the coefficient families from $A$, $y$ and $L$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.45, p.106 (PDF p.106)

import Mathlib
import Definitions.Def_SpencerEight_absM
import Definitions.Def_BlockBochner_invSqrt
import Definitions.Def_SpencerEight_reserve
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- The prefix of a signing schedule in Lemma 8.45 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.106 (PDF p.106)): `r` partial signings with congruence replacement, constructed as on the page. The index `i < r` below is step `i + 1` of the page. The level-`i` coefficients are `Bk i`, with `Bk 0 = A`. The active sets are nested, `S 0` is everything, and `S (i+1)` is the part of `S i` left unset by the partial signing `y i ∈ {−1, 0, 1}`. The signed sum is `M_{i+1} := ∑_{j ∈ S i} y_i(j) (Bk i j)`, with `‖M_{i+1}‖ ≤ L_{i+1} √n`, `L_{i+1} > 0`, `C_{i+1} > 0`. Every coefficient is replaced by `C_{i+1} √n H^{−1/2} B H^{−1/2}`, where `H := C_i √n I − |M_{i+1}|`.

**Formalization Note** The equations determine `S` and `Bk` from `A`, `y` and `L`. `Bk i j` is also defined off the active set, where it plays no role. -/
structure PrefixRun {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℝ) (C0 : ℝ)
    (r : ℕ) (L : ℕ → ℝ) (S : ℕ → Finset ι) (y : ℕ → ι → ℝ)
    (Bk : ℕ → ι → Matrix (Fin n) (Fin n) ℝ) : Prop where
  level_zero : Bk 0 = A
  active_zero : S 0 = Finset.univ
  sign : ∀ i < r, ∀ j ∈ S i, y i j = -1 ∨ y i j = 0 ∨ y i j = 1
  active_succ : ∀ i < r, S (i + 1) = (S i).filter fun j => y i j = 0
  L_pos : ∀ i < r, 0 < L (i + 1)
  reserve_pos : ∀ i < r, 0 < reserve C0 L (i + 1)
  norm_bound : ∀ i < r, ‖∑ j ∈ S i, y i j • Bk i j‖ ≤ L (i + 1) * Real.sqrt n
  congruence : ∀ i < r, ∀ j, Bk (i + 1) j =
    (reserve C0 L (i + 1) * Real.sqrt n) •
      (BlockBochner.invSqrt ((reserve C0 L i * Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          absM (∑ l ∈ S i, y i l • Bk i l)) * Bk i j *
        BlockBochner.invSqrt ((reserve C0 L i * Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          absM (∑ l ∈ S i, y i l • Bk i l)))

end SpencerEight


