-- Prove2me | Definitions.Def_HighMagSampling_SK_GOEEvents
-- name    : HighMagSampling_SK_GOEEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:28:32.059616+00:00
-- url     : https://prove2.me/theorems/efe56681-24af-4d49-903d-d0ab29438f51
-- title:
--   The four high-probability events of Lemma 12 for a matrix $J$, with constant $C$ and failure level $\delta$
-- statement:
--   Fix a constant $C$, a dimension $d\ge1$, a level $\delta\in(0,\tfrac12)$ and $J\in\mathbb R^{d\times d}$. Logarithms are natural, $e=\exp(1)$, and $\|\cdot\|_{\mathrm{op}}$ is the spectral norm.
--
--   1. For every $S\subseteq[d]$ with $|S|=s\in[d]$: $\displaystyle\|J_{S\times S}\|_{\mathrm{op}}\le C\sqrt{\frac{s\log\frac{ed}{s}+\log\frac d\delta}{d}}$.
--   2. $\displaystyle\max_{i,j}|J_{ij}|\le C\sqrt{\frac{\log(d/\delta)}{d}}$ and $\|J\mathbf 1_d\|_\infty\le C\sqrt{\log(d/\delta)}$.
--   3. For every nonzero $u\in\mathbb R^d$, with $q=\|u\|_2^2/\|u\|_1^2$:
--   $$|u^\top Ju|\le C\|u\|_1^2\Big(\sqrt{\frac{q\log(edq)}{d}}+q\sqrt{\frac{\log(d/\delta)}{d}}\Big).$$
--   4. With $H=J\circ J-\tfrac1d(\mathbf 1_d\mathbf 1_d^\top-I_d)$ ($\circ$ the entrywise product): $\displaystyle\|H\|_{\mathrm{op}}\le C\Big(\sqrt{\frac{\log(d/\delta)}{d}}+\frac{\log(d/\delta)}{d}\Big)$.
--
--   Lemma 12 shows that for a GOE matrix all four hold simultaneously with probability at least $1-\delta$; Lemma 13 derives the bounds on $\rho(4\beta J)$ and $m(4\beta J)$ from Items 2–4.
--
--   **Formalization Note.** `event1`–`event4` are predicates on `Matrix (Fin d) (Fin d) ℝ`. A bound on a maximum is written as the bound for every entry (every $i,j$, every row $i$). $J_{S\times S}$ is the principal submatrix indexed by the elements of $S$; Item 1 ranges over nonempty $S$, i.e. $s\in[d]$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, pp. 25–26, Lemma 12, Items 1–4

import Mathlib
import Definitions.Def_HighMagSampling_SK_Spectral

open Matrix

namespace HighMagSampling.SK

/-!
# The four high-probability events of Lemma 12

Kumar, Sarkar, Tian, Zhu, *High-Magnetization Sampling at Low Temperatures*, arXiv:2609.08873v1,
Lemma 12, pp. 25–26 (PDF pp. 27–28). For a constant `C`, a dimension `d`, a failure level `δ` and a
matrix `J ∈ ℝ^{d×d}`:

1. `event1`: for every `S ⊆ [d]` with `|S| = s ∈ [d]`,
   `‖J_{S×S}‖_op ≤ C √((s log(ed/s) + log(d/δ))/d)`;
2. `event2`: `max_{i,j} |J_ij| ≤ C √(log(d/δ)/d)` and `‖J 1_d‖_∞ ≤ C √(log(d/δ))`;
3. `event3`: for every nonzero `u ∈ ℝ^d`, with `q = ‖u‖₂²/‖u‖₁²`,
   `|uᵀJu| ≤ C ‖u‖₁² (√(q log(edq)/d) + q √(log(d/δ)/d))`;
4. `event4`: with `H = J ∘ J − (1/d)(1_d 1_dᵀ − I_d)`, `‖H‖_op ≤ C (√(log(d/δ)/d) + log(d/δ)/d)`.

**Formalization Note.** A maximum bounded by a number is written as the bound for every entry.
`J_{S×S}` is the principal submatrix indexed by the elements of `S`; `e = exp 1`; natural log.
-/

/-- Item 1 of Lemma 12: sparse principal-submatrix operator norms. -/
def event1 (C : ℝ) (d : ℕ) (δ : ℝ) (J : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ S : Finset (Fin d), S.Nonempty →
    opNorm (J.submatrix (fun i : S => i.1) (fun i : S => i.1)) ≤
      C * Real.sqrt (((S.card : ℝ) * Real.log (Real.exp 1 * d / S.card) + Real.log (d / δ)) / d)

/-- Item 2 of Lemma 12: largest entry and `‖J 1_d‖_∞`. -/
def event2 (C : ℝ) (d : ℕ) (δ : ℝ) (J : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, |J i j| ≤ C * Real.sqrt (Real.log (d / δ) / d)) ∧
    ∀ i, |∑ j, J i j| ≤ C * Real.sqrt (Real.log (d / δ))

/-- Item 3 of Lemma 12: the mixed-norm bound on the quadratic form. -/
def event3 (C : ℝ) (d : ℕ) (δ : ℝ) (J : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ u : Fin d → ℝ, u ≠ 0 →
    |u ⬝ᵥ (J *ᵥ u)| ≤ C * (∑ i, |u i|) ^ 2 *
      (Real.sqrt ((∑ i, u i ^ 2) / (∑ i, |u i|) ^ 2 *
          Real.log (Real.exp 1 * d * ((∑ i, u i ^ 2) / (∑ i, |u i|) ^ 2)) / d) +
        (∑ i, u i ^ 2) / (∑ i, |u i|) ^ 2 * Real.sqrt (Real.log (d / δ) / d))

/-- Item 4 of Lemma 12: `‖J ∘ J − (1/d)(1 1ᵀ − I)‖_op ≤ C (√(log(d/δ)/d) + log(d/δ)/d)`. -/
def event4 (C : ℝ) (d : ℕ) (δ : ℝ) (J : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  opNorm (Matrix.of fun i j => J i j ^ 2 - (1 / (d : ℝ)) * (if i = j then 0 else 1)) ≤
    C * (Real.sqrt (Real.log (d / δ) / d) + Real.log (d / δ) / d)

end HighMagSampling.SK


