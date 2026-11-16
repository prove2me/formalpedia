-- Prove2me | Definitions.Def_QMCBeyondHK_Supplement_starDisc
-- name    : QMCBeyondHK_Supplement_starDisc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:15:03.232824+00:00
-- url     : https://prove2.me/theorems/3db2b67f-e7da-4d95-9a58-9a80049eecdd
-- title:
--   Anchored boxes, continuous discrepancy $D_R(A)$ and star discrepancy $D^\star(A)$
-- statement:
--   This module defines the discrepancy notions of Section 2 ("Boxes and Star Discrepancy").
--
--   1. An **anchored box** is a box of the form $[0, x_1) \times \cdots \times [0, x_d)$ with upper corner $x \in [0,1)^d$. The family of all anchored boxes is denoted $\mathcal R$.
--   2. For a finite point set $A \subset [0,1)^d$ and a Lebesgue-measurable set $R \subseteq [0,1)^d$, the **continuous discrepancy** (or Lebesgue-measure discrepancy) of $A$ with respect to $R$ is
--   $$
--   D_R(A) := |A \cap R| - |A|\,|R|,
--   $$
--   where $|R|$ is the Lebesgue measure of $R$.
--   3. The **star discrepancy** of $A$ is
--   $$
--   D^\star(A) := \sup_{R \in \mathcal R} |D_R(A)|.
--   $$
--
--   The discrepancy is not normalized: a set of $n$ well-spread points has $D^\star$ of polylogarithmic size in $n$, while $n$ independent uniform points have $D^\star$ of order $\sqrt n$. Theorem 1.3 bounds $D^\star$ of the output of linear-feedback Haar-thinning.
--
--   **Formalization Note** An $n$-point set is a tuple $A : \mathrm{Fin}\,n \to [0,1)^d$, so repeated points are counted with multiplicity and $|A| = n$; points are vectors $\mathrm{Fin}\,d \to \mathbb R$. $|R|$ is the Lebesgue measure converted to a real number (finite for every $R$ inside the cube). The supremum is a real supremum over corners $x \in [0,1)^d$, a nonempty index set on which $|D_{[0,x)}(A)| \le 2n$, so it is the true supremum.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §2 'Boxes and Star Discrepancy', eqs. (5)–(6), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_QMCBeyondHK_cube

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK.Supplement

/-- The anchored box `[0, x_1) × ⋯ × [0, x_d)` with upper corner `x` (Ezeunala, Jha, Jiang,
*Quasi-Monte Carlo Beyond Hardy–Krause II*, arXiv:2609.10921, sha256 bc273e88…, §2 "Boxes and
Star Discrepancy", printed p.7, PDF p.9).

**Formalization Note** Points are vectors `Fin d → ℝ`; the box is the product set
`∏ i, [0, x_i)`. The paper's family `R` of anchored boxes is `{anchoredBox x | x ∈ [0,1)^d}`. -/
def anchoredBox {d : ℕ} (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun i => Set.Ico (0 : ℝ) (x i))

open Classical in
/-- The continuous (Lebesgue-measure) discrepancy (5) of an `n`-point set `A` with respect to a
Lebesgue-measurable `R ⊆ [0,1)^d`, `D_R(A) := |A ∩ R| − |A| |R|` (arXiv:2609.10921,
sha256 bc273e88…, §2, eq. (5), printed p.7, PDF p.9).

**Formalization Note** An `n`-point set is a tuple `A : Fin n → [0,1)^d` (a multiset), so
`|A ∩ R|` counts the indices `t` with `A t ∈ R`, with multiplicity, and `|A| = n`. `|R|` is the
Lebesgue measure of `R`, taken as a real number; every use has `R ⊆ [0,1)^d`, where it is finite.
The discrepancy is not normalized by `n`. -/
noncomputable def contDisc {d n : ℕ} (A : Fin n → Fin d → ℝ) (R : Set (Fin d → ℝ)) : ℝ :=
  ((Finset.univ.filter (fun t => A t ∈ R)).card : ℝ) - (n : ℝ) * (volume R).toReal

/-- The star discrepancy (6) of an `n`-point set `A`,
`D⋆(A) := sup_{R ∈ R} |D_R(A)|`, the supremum over all anchored boxes `[0, x)` with
`x ∈ [0,1)^d` (arXiv:2609.10921, sha256 bc273e88…, §2, eq. (6), printed p.7, PDF p.9).

**Formalization Note** A real supremum over the nonempty index set `[0,1)^d`; the family
`|D_{[0,x)}(A)|` is bounded by `2n` there (each anchored box with corner in the cube has volume at
most `1`), so the supremum is the true one, not a junk value. -/
noncomputable def starDisc {d n : ℕ} (A : Fin n → Fin d → ℝ) : ℝ :=
  ⨆ x : cube d, |contDisc A (anchoredBox (x : Fin d → ℝ))|

end QMCBeyondHK.Supplement


