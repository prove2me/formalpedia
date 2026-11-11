-- Prove2me | Definitions.Def_AgnHalfMem_IsOrthogonalFamily
-- name    : AgnHalfMem_IsOrthogonalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:43.228778+00:00
-- url     : https://prove2.me/theorems/1c2a84e0-9cc8-453b-ad5d-707239970cf1
-- title:
--   $(\epsilon,\eta)$-orthogonal functions (Definition 4.4)
-- statement:
--   Let $\mu$ be a probability distribution on $X$. Functions $f_1,\dots,f_m:X\to[-1,1]$ are **$(\epsilon,\eta)$-orthogonal** with respect to $\mu$ if for every $i\in[m]$,
--   $$
--   \big|\mathbb E_{x\sim\mu}[f_i(x)f_j(x)]\big|\le\epsilon\quad\text{with probability } 1-\eta \text{ over a uniform } j\in[m],
--   $$
--   that is, at most $\eta m$ indices $j$ violate the bound. Lemma 4.5 turns such a family into an $L_2$-extractor.
--
--   **Formalization Note** The index $j=i$ is counted among the $j$ (Theorem 4.10's proof takes $\eta=1/m$ for this reason). Indices run over `Fin m`.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Definition 4.4, p.11

import Mathlib

open MeasureTheory

namespace AgnHalfMem

/-- **`(ϵ, η)`-orthogonal functions (Definition 4.4).** S. Garg, T. Jadhav, *Memory-Sample
Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Definition 4.4, p.11: "Let μ be a probability distribution over X. The
functions f1, f2, ..., fm : X → [−1, 1] are said to be (ϵ, η)-orthogonal w.r.t. μ if for all
i ∈ [m] |E_{x∼μ}[fi(x) · fj(x)]| ≤ ϵ with probability 1 − η over j ∈ [m]."

`IsOrthogonalFamily μ f ϵ η`: for every `i`, the number of `j` with `|E_μ[f_i f_j]| > ϵ` is at
most `η·m`.

**Formalization Note.** "With probability `1 − η` over `j ∈ [m]`" (uniform `j`) is read as: the
`j` violating the bound number at most `η m`; `j = i` is counted (the proof of Theorem 4.10 takes
`η = 1/m` for this reason, p.18). Indices are `Fin m`. The range `[−1, 1]` and measurability of
the `f_i` are hypotheses of the theorems that use the definition. -/
def IsOrthogonalFamily {X : Type*} [MeasurableSpace X] {m : ℕ} (μ : Measure X)
    (f : Fin m → X → ℝ) (ϵ η : ℝ) : Prop :=
  ∀ i, ((Finset.univ.filter fun j => ϵ < |∫ x, f i x * f j x ∂μ|).card : ℝ) ≤ η * m

end AgnHalfMem


