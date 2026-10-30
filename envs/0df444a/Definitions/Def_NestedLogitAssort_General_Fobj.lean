-- Prove2me | Definitions.Def_NestedLogitAssort_General_Fobj
-- name    : NestedLogitAssort_General_Fobj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:39.208235+00:00
-- url     : https://prove2.me/theorems/63be5e25-bfba-4c34-b2dc-efa474c91519
-- title:
--   Objective of Lemma 6's problem (8), with $v_{i0}$
-- statement:
--   For a nest $i$, a vector $z\in[0,1]^n$ and a number $x$, this is
--
--   $$
--   \Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_j}{v_{i0}+\sum_{j\in N}v_{ij}z_j}-x\right],
--   $$
--
--   the fractional relaxation of the constraint value $V_i(S)^{\gamma_i}(R_i(S)-x)$ (it equals that value when $z$ is the 0–1 vector of $S$). Problem (8) of Lemma 6 maximizes it with $v_{i0}=0$; the proof of Theorem 11 maximizes it with $v_{i0}$ included.
--
--   **Formalization Note** Real powers with $0^0=1$ and division with $a/0=0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (8), p. 21; proof of Theorem 11 (Appendix A.4), Case 1, p. 47

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **The objective of Lemma 6's problem (8), with the no-purchase weight `v_{i0}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (8), p. 21, and the problem in Case 1 of the proof of Theorem 11 (Appendix A.4),
p. 47 (unnumbered):
`(v_{i0} + ∑_{j ∈ N} v_{ij} z_{ij})^{γ_i} [ ∑_{j ∈ N} r_{ij} v_{ij} z_{ij} / (v_{i0} + ∑_{j ∈ N} v_{ij} z_{ij}) − x ]`
for `z_i ∈ [0, 1]^n`. Problem (8) is the case `v_{i0} = 0`.

**Formalization Note.** `Real.rpow` (`0 ^ 0 = 1`, `0 ^ γ = 0` for `γ ≠ 0`) and `a / 0 = 0`. -/
noncomputable def Fobj {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  (I.w0 i + ∑ j, I.v i j * z j) ^ (I.γ i) *
    ((∑ j, I.r i j * I.v i j * z j) / (I.w0 i + ∑ j, I.v i j * z j) - x)

end NestedLogitAssort.General


