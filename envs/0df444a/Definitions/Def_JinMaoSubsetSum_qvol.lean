-- Prove2me | Definitions.Def_JinMaoSubsetSum_qvol
-- name    : JinMaoSubsetSum_qvol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:07.560227+00:00
-- url     : https://prove2.me/theorems/f66915f3-e575-46d4-b468-10e99beecc87
-- title:
--   Point counts $|\pi_\Lambda(S)|$ and Haar volume $\mathrm{vol}_d(\pi_\Lambda(A))$ in $\mathbb R^d/\Lambda$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^d$ be a lattice of any rank and $\pi_\Lambda:\mathbb R^d\to\mathbb R^d/\Lambda$ the quotient map. For a finite set $S$, $|\pi_\Lambda(S)|$ is the number of cosets of $\Lambda$ that $S$ meets. The paper writes $\mathrm{vol}_d$ for the Haar measure on $\mathbb R^d/\Lambda$, normalized so that $\mathrm{vol}_d(\pi_\Lambda(A))=\mathrm{vol}_d(A)$ whenever $\pi_\Lambda$ is injective on $A$. For a bounded set $E$, with $n_E(x)=|(x+\Lambda)\cap E|$,
--   $$
--   \mathrm{vol}_d(\pi_\Lambda(E))=\int_E n_E(x)^{-1}\,dx
--   $$
--   (the identity used in the proof of Lemma 9.2), and for a general set $A$ the value is the increasing limit of $\mathrm{vol}_d(\pi_\Lambda(A\cap B_R))$ over the balls $B_R$ of radius $R=0,1,2,\dots$. The **determinant** of a full-rank lattice $\Gamma$ is $\det\Gamma=\mathrm{vol}_d(\mathbb R^d/\Gamma)$.
--
--   **Formalization Note** `qcount Λ S` is $|\pi_\Lambda(S)|$ (`Set.ncard` of the image in the quotient group). `qvol Λ A` is defined by the integral formula above on the balls $B_R$ and a supremum over $R$, so no fundamental domain has to be chosen; it takes values in $[0,\infty]$. For $\Lambda=\{0\}$ it is the Lebesgue measure (proved in the mission's sanity checks for measurable $A$). `covol Γ = qvol Γ ℝ^d` is $\det\Gamma$.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), §3.3, p.16 (PDF p.18); proof of Lemma 9.2, p.49 (PDF p.51)

import Mathlib

set_option autoImplicit false

namespace JinMaoSubsetSum

open MeasureTheory

/-!
# Point counts and volumes in the quotient `ℝ^d / Λ`

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §3.3, p.16: "For a lattice
Λ ⊆ ℝ^d, write π_Λ for the quotient map π_Λ : ℝ^d → ℝ^d/Λ. Let vol_d also denote the Haar
measure on ℝ^d/Λ, normalized so that vol_d(π_Λ(A)) equals the Euclidean volume vol_d(A) for
every measurable A ⊆ ℝ^d on which π_Λ is injective." Proof of Lemma 9.2, p.49: "For a compact
convex set E, let n_E(x) = |(x + Λ) ∩ E|. By partitioning E into lattice translates of a
fundamental domain, we get vol_d(π_Λ(E)) = ∫_E n_E(x)^{−1} dx."

**Formalization Note.**
* A lattice `Λ` is an additive subgroup of `ℝ^d` (statements assume it discrete); its rank may be
  anything from `0` to `d`.
* `qcount Λ S = |π_Λ(S)|` is the number of cosets of `Λ` that `S` meets (`Set.ncard` of the image
  in `ℝ^d ⧸ Λ`; every set it is applied to is finite).
* `qvol Λ A = vol_d(π_Λ(A))` is defined without choosing a fundamental domain: for bounded `E`,
  `vol_d(π_Λ(E)) = ∫_E n_E(x)^{−1} dx` with `n_E(x) = |(x + Λ) ∩ E|` (the paper's identity; it
  holds for every bounded measurable `E`, since a discrete `Λ` meets each bounded set finitely
  often), and for general `A` the value is the increasing limit over the balls of radius
  `R = 0, 1, 2, …` (continuity of the Haar measure from below, as
  `π_Λ(A) = ⋃_R π_Λ(A ∩ B_R)`). For `Λ = {0}` this is the Lebesgue measure; for a set on which
  `π_Λ` is injective it is the Lebesgue measure, which is the paper's normalization.
* `covol Γ = qvol Γ ℝ^d = vol(ℝ^d/Γ)` is `det Γ` for a full-rank lattice `Γ`.
-/

/-- `n_E(x) = |(x + Λ) ∩ E|`, the number of points of `E` congruent to `x` modulo `Λ`. -/
noncomputable def cosetCount {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) (E : Set (Fin d → ℝ))
    (x : Fin d → ℝ) : ℕ∞ :=
  {y | y ∈ E ∧ y - x ∈ Λ}.encard

/-- `vol_d(π_Λ(A))`, the Haar measure of the image of `A` in `ℝ^d / Λ`. -/
noncomputable def qvol {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) (A : Set (Fin d → ℝ)) : ENNReal :=
  ⨆ R : ℕ, ∫⁻ x in A ∩ Metric.closedBall (0 : Fin d → ℝ) R,
    (ENat.toENNReal (cosetCount Λ (A ∩ Metric.closedBall (0 : Fin d → ℝ) R) x))⁻¹

/-- `det Γ = vol(ℝ^d/Γ)` (finite and positive for a full-rank lattice). -/
noncomputable def covol {d : ℕ} (Γ : AddSubgroup (Fin d → ℝ)) : ENNReal :=
  qvol Γ Set.univ

/-- `|π_Λ(S)|`: the number of cosets of `Λ` met by `S`. -/
noncomputable def qcount {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) (S : Set (Fin d → ℝ)) : ℕ :=
  ((QuotientAddGroup.mk : (Fin d → ℝ) → (Fin d → ℝ) ⧸ Λ) '' S).ncard

end JinMaoSubsetSum


