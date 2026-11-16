-- Prove2me | Definitions.Def_NondualOpt_Supplement_convDistWC
-- name    : NondualOpt_Supplement_convDistWC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:13:48.585328+00:00
-- url     : https://prove2.me/theorems/308b9eb3-f5bd-40bd-be1d-44f6d40ed92c
-- title:
--   The worst-case convex-hull distance $\mathrm{ConvDist}^{\mathrm{wc}}_{X,H,T}$
-- statement:
--   Let $X,H\subseteq\mathbb R^d$ and $T\in\mathbb N$. For a probability distribution $P$ on $\mathbb R^d$ supported in $H$, write $\mu_P=\int g\,dP(g)$ for its mean, and let $G_1,\dots,G_T$ be iid with law $P$. The **worst-case expected $X^\circ$-distance** from the convex hull of $T$ samples to their common mean is
--   $$
--   \mathrm{ConvDist}^{\mathrm{wc}}_{X,H,T}=\sup_{\operatorname{supp}(P)\subseteq H}\ \mathbb E_{G_{1:T}\overset{\text{iid}}{\sim}P}\,\mathrm{dist}_{X^\circ}\big(\mu_P,\operatorname{conv}\{G_1,\dots,G_T\}\big).
--   $$
--   It quantifies the classical question of how well the convex hull of iid samples approximates the mean of a bounded distribution, measured in the polar norm of $X$; Theorem 10 bounds it by the fat-shattering dimension of $L_{X,H}$.
--
--   **Formalization Note** The supremum ranges over all Borel probability measures $P$ on $\mathbb R^d$ with $P(\mathbb R^d\setminus H)=0$, which is $\operatorname{supp}(P)\subseteq H$ for the closed sets $H$ used in Theorem 10. The mean is a Bochner integral (finite, $P$ being carried by a bounded set). The expectation is the Lebesgue integral of the nonnegative distance against the $T$-fold product of $P$, and the value is an extended nonnegative real.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (12), p.13; µ_P: Lemma 9, p.13

import Mathlib
import Definitions.Def_NondualOpt_Supplement_polarDist

open scoped ENNReal

namespace NondualOpt.Supplement

/-- The worst-case expected polar distance from the convex hull of `T` iid samples to their mean,
`ConvDist^wc_{X,H,T} = sup_{supp(P) ⊆ H} E_{G_{1:T} iid∼ P} dist_{X°}(µ_P, conv{G_1, …, G_T})`,
with `µ_P = ∫ g dP(g)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (12), p.13 (and `µ_P`, Lemma 9, p.13).

**Formalization Note.** (i) The supremum ranges over all Borel probability measures `P` on
`ℝ^d = Fin d → ℝ` with `P(Hᶜ) = 0`; for the closed sets `H` of every use (convex bodies) this is
`supp(P) ⊆ H`. (ii) `µ_P` is the Bochner integral `∫ g ∂P`; `P` is carried by the bounded set `H`,
so `µ_P` is the true mean. (iii) The expectation is the lower Lebesgue integral of the
nonnegative distance against the product law `Measure.pi (fun _ : Fin T => P)`; the value is
in `ℝ≥0∞` (finite for bounded `H`). (iv) `conv{G_1, …, G_T}` is `convexHull ℝ (Set.range G)`. -/
noncomputable def convDistWC {d : ℕ} (X H : Set (Fin d → ℝ)) (T : ℕ) : ℝ≥0∞ :=
  ⨆ P : {P : MeasureTheory.ProbabilityMeasure (Fin d → ℝ) //
      (P : MeasureTheory.Measure (Fin d → ℝ)) Hᶜ = 0},
    ∫⁻ G : Fin T → (Fin d → ℝ),
      ENNReal.ofReal (polarDist X (∫ g, g ∂(P.1 : MeasureTheory.Measure (Fin d → ℝ)))
        (convexHull ℝ (Set.range G)))
      ∂(MeasureTheory.Measure.pi fun _ : Fin T => (P.1 : MeasureTheory.Measure (Fin d → ℝ)))

end NondualOpt.Supplement


