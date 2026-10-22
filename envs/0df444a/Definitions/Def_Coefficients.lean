-- Prove2me | Definitions.Def_Coefficients
-- name    : Coefficients
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T04:51:13.771128+00:00
-- url     : https://prove2.me/theorems/edbffaf5-58dc-4418-80dd-8654a91e1e64
-- title:
--   Definitions of Coefficients
-- statement:
--   This module introduces every scalar sequence of the certificate, as exact real-valued functions of the integer indices. The rational-momentum coefficient is
--
--   $$m_k = \frac{k}{k+3},$$
--
--   and the two distinguished sequences are
--
--   $$d_j = \frac{j(j+7)}{8}, \qquad \tau_N = \frac{2}{N^2 + 7N + 4} = \frac{1}{2(2d_N+1)}.$$
--
--   The denominator sequence $D$ follows the source's genuine two-case split, $D_0 = 2d_N + 1$ and $D_j = 2d_N - d_{j-1}$ for $1 \le j \le N$ (formula (4.8) must not be extended mechanically to $j = 0$). The auxiliary sequences are
--
--   $$h_j = \frac{j+2}{2} - \frac{j(j+1)(j+2)}{2(N+1)(N+2)}, \qquad H_j = \frac{(j+1)(j+4)}{4} - \frac{j(j+1)(j+2)(j+3)}{8(N+1)(N+2)},$$
--
--   and the interpolation weights are $a_j = H_j / D_{j+1}$ for $0 \le j < N$ together with the separate endpoint $a_N = 1$ (a real case split, since $H_N/D_{N+1} \ne 1$), and $b_j = a_j - a_{j-1}$ for $0 \le j \le N$ with the source's convention $a_{-1} = 0$ absorbed into $b_0 = a_0$. All divisions are exact divisions in $\mathbb R$: no floating point arithmetic and no finite enumeration is used anywhere.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §3-4, eq. (3.2) and (4.1)-(4.13); Lean: FullFormalization.Coefficients lines 1-129

-- Generated from F:/20261008/FullFormalization\FullFormalization\Coefficients.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.Coefficients

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 4 and 5.

  All scalar coefficient sequences of the rational-momentum Nesterov
  certificate, transcribed verbatim from the source:

    (4.1)  d_j = j (j+7) / 8
    (4.2)  tau = 1/(2 (2 d_N + 1)) = 2 / (N^2 + 7 N + 4)
    (4.3)  h_j = (j+2)/2 - j(j+1)(j+2) / (2 (N+1)(N+2))
    (4.4)  H_j = (j+1)(j+4)/4 - j(j+1)(j+2)(j+3) / (8 (N+1)(N+2))
    (4.7)  D_0 = 2 d_N + 1
    (4.8)  D_j = 2 d_N - d_{j-1}          (1 <= j <= N)
    (4.11) a_j = H_j / D_{j+1}            (0 <= j < N)
    (4.12) a_{-1} = 0,  a_N = 1
    (4.13) b_j = a_j - a_{j-1}            (0 <= j <= N)
    (3.2)  m_k = k / (k+3)

  Representation choices (recorded in DEPENDENCY_MAP.md, section 9, and in
  THEOREM_AUDIT.md):

  * Coefficients are real-valued.  Every division below is a division in the
    exact characteristic-zero field `R`; no floating point arithmetic and no
    finite enumeration is used anywhere.  All identities in
    `CoefficientIdentities.lean` are proved symbolically in `N` and `j`.

  * `D` is defined by the source's two-case definition: index `0` uses the
    separately-declared `D_0`, and the source explicitly warns (line 427) that
    formula (4.8) must not be extended mechanically to `j = 0`.  The Lean
    definition reproduces exactly that two-case split.

  * `a` uses the source's separate endpoint values: `a_N = 1` is *not* equal to
    `H_N / D_{N+1}`, so it is a genuine case split, not a convenience.

  * `a_{-1} = 0` is not an index of `a : Nat -> R`; it is absorbed into the
    definition of `b`, where `b_0 := a_0 - a_{-1} = a_0`.
-/

import Mathlib

namespace FullFormalization

/-- (4.1) `d_j = j (j + 7) / 8`. -/
noncomputable def d (j : ℕ) : ℝ := (j : ℝ) * ((j : ℝ) + 7) / 8

/-- (3.2) `m_k = k / (k + 3)`, the rational momentum coefficient.

Source line 299 defines `m_k = k/(k+3)` for `k = 0, ..., N-1`. -/
noncomputable def mom (k : ℕ) : ℝ := (k : ℝ) / ((k : ℝ) + 3)

/-- (4.7), (4.8) `D_0 = 2 d_N + 1` and `D_j = 2 d_N - d_{j-1}` for `1 <= j <= N`.

The index `0` is a genuine special case (source line 427). -/
noncomputable def D (N j : ℕ) : ℝ :=
  if j = 0 then 2 * d N + 1 else 2 * d N - d (j - 1)

/-- (4.3) `h_j = (j+2)/2 - j(j+1)(j+2) / (2 (N+1)(N+2))`, defined for `0 <= j < N`. -/
noncomputable def h (N j : ℕ) : ℝ :=
  ((j : ℝ) + 2) / 2
    - (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2)
        / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2))

/-- (4.4) `H_j = (j+1)(j+4)/4 - j(j+1)(j+2)(j+3) / (8 (N+1)(N+2))`. -/
noncomputable def H (N j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * ((j : ℝ) + 4) / 4
    - (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) * ((j : ℝ) + 3)
        / (8 * ((N : ℝ) + 1) * ((N : ℝ) + 2))

/-- (4.11), (4.12) `a_j = H_j / D_{j+1}` for `0 <= j < N`, with `a_N = 1`.

`a_{-1} = 0` is handled in `b` (see below), since `-1` is not an index of `ℕ`. -/
noncomputable def a (N j : ℕ) : ℝ :=
  if j = N then 1 else H N j / D N (j + 1)

/-- (4.13) `b_j = a_j - a_{j-1}` for `0 <= j <= N`, with the source's `a_{-1} = 0`. -/
noncomputable def b (N j : ℕ) : ℝ :=
  if j = 0 then a N 0 else a N j - a N (j - 1)

/-- (4.2) `tau_N = 2 / (N^2 + 7 N + 4)`. -/
noncomputable def tau (N : ℕ) : ℝ := 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4)

/-! ## Basic closed forms used throughout

These are the elementary evaluations that every later module relies on.
They are consequences of the definitions, not extra assumptions. -/

























/-! ## `tau` vs `1 / (2 (2 d_N + 1))`  (source (4.2)) -/













end FullFormalization


