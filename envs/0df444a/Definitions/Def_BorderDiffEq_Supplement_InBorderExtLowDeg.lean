-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_InBorderExtLowDeg
-- name    : BorderDiffEq_Supplement_InBorderExtLowDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:52:04.736674+00:00
-- url     : https://prove2.me/theorems/d68310fe-54a7-48fd-b134-fdf3d271498f
-- title:
--   The border of $\text{Ext-}\Sigma^{k}\wedge^e\mathcal D_{\text{low-deg}}(\delta,\Delta)$ of total size $s$
-- statement:
--   A polynomial $f\in F[x_1,\dots,x_n]$ is in this border class if there are at most $k$ triples $(q_i,P_i,e_i)$, with $q_i,P_i\in F((\epsilon))[x]$ given as sums of monomials, $\deg P_i\le\delta$, $\deg q_i\le\Delta$, $1\le e_i\le e$, of **total size**
--   $$
--   \sum_{i}\bigl(\mathrm{size}(q_i)+\mathrm{size}(P_i)+e_i\bigr)\le s,
--   $$
--   such that $\sum_iq_iP_i^{e_i}=f+\epsilon S$ with $S\in F[[\epsilon]][x]$.
--
--   This is the class of Theorem 6.2, which extends $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$ by the multipliers $q_i$.
--
--   **Formalization Note** The paper does not define the total size; the proof of Theorem 6.2 uses "total size at most $s$" and "$e\le s$". It is read as the extension of p.8's $\sum_i(\mathrm{size}(P_i)+e_i)$ by the sizes of the $q_i$, with $\mathrm{size}$ = `spSize`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §5.3, p.37, display (29) and D_low-deg(δ, ∆); Theorem 6.2 and its proof, p.48

import Mathlib
import Definitions.Def_BorderDiffEq_IsEpsApprox
import Definitions.Def_BorderDiffEq_Supplement_spSize

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **The border of `Ext-Σ^{[k]} ∧^e D_low-deg(δ, Δ)` with total size at most `s`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §5.3, p.37, display (29) and
"`D_low-deg(δ, Δ)` ... each summand `qᵢPᵢ^{eᵢ}` satisfies `deg Pᵢ ≤ δ` and `deg qᵢ ≤ Δ`"; Theorem 6.2
and its proof, p.48: "total size at most `s`", "`e ≤ s`"): `f ∈ F[x]` is in the border if there are
at most `k` triples `(qᵢ, Pᵢ, eᵢ)` of polynomials over `F((ε))` given as sums of monomials, with
`deg Pᵢ ≤ δ`, `deg qᵢ ≤ Δ`, `1 ≤ eᵢ ≤ e`, total size `∑ᵢ (size(qᵢ) + size(Pᵢ) + eᵢ) ≤ s`, and
`∑ᵢ qᵢ Pᵢ^{eᵢ} = f + ε·S`, `S ∈ F[[ε]][x]`.

**Formalization Note.** The paper does not define the total size; it is read as the extension of
p.8's `∑ᵢ (size(Pᵢ) + eᵢ)` (exponents count) by the sizes of the `qᵢ`, with `size = spSize`.
"`k` summands" is read as "at most `k`", which can only enlarge the class. -/
def InBorderExtLowDeg (F : Type) [Field F] (n k e δ Δ s : ℕ) (f : MvPolynomial (Fin n) F) :
    Prop :=
  ∃ (t : ℕ) (q P : Fin t → MvPolynomial (Fin n) (LaurentSeries F)) (ex : Fin t → ℕ),
    t ≤ k ∧ (∀ i, 1 ≤ ex i ∧ ex i ≤ e) ∧ (∀ i, (P i).totalDegree ≤ δ) ∧
    (∀ i, (q i).totalDegree ≤ Δ) ∧ ∑ i, (spSize (q i) + spSize (P i) + ex i) ≤ s ∧
    IsEpsApprox (∑ i, q i * P i ^ ex i) f

end BorderDiffEq.Supplement


