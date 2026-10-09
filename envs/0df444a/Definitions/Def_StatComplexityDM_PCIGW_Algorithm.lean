-- Prove2me | Definitions.Def_StatComplexityDM_PCIGW_Algorithm
-- name    : StatComplexityDM_PCIGW_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:56.172235+00:00
-- url     : https://prove2.me/theorems/efa385de-f76c-49db-bb5b-cdc68aca8f97
-- title:
--   Algorithm 4, (56)–(57) — policy cover inverse gap weighting
-- statement:
--   Fix a finite-horizon tabular MDP $\bar M$, a value-maximizing policy $\pi_{\bar M}$, and $\eta>0$. For each layer $h$, state $s$, and action $a$, the **policy cover** chooses a randomized nonstationary policy $\pi_{h,s,a}$ maximizing
--   $$
--   \frac{d_h^{\bar M,\pi}(s,a)}{2HSA+\eta\bigl(f^{\bar M}(\pi_{\bar M})-f^{\bar M}(\pi)\bigr)}
--   $$
--   over every randomized nonstationary policy $\pi$. Repeated policies are merged into the finite set $\Psi\cup\{\pi_{\bar M}\}$. Each policy in that set receives weight
--   $$
--   p(\pi)=\frac{1}{\lambda+\eta\bigl(f^{\bar M}(\pi_{\bar M})-f^{\bar M}(\pi)\bigr)},\qquad\sum_{\pi\in\Psi\cup\{\pi_{\bar M}\}}p(\pi)=1.
--   $$
--   This is the explicit exploration distribution of Algorithm 4. The file also records the value-maximizer condition for the selector $\pi_M$.
--
--   **Formalization Note** The cover's ratio comparison is cross-multiplied to avoid division by zero. The finite support is a set of policies, so coinciding cover entries count once. The scalar `lam` is the normalizer $\lambda$, whose existence and range are the separate Proposition 5.7 milestone.
-- source:
--   arXiv:2112.13487v3, Algorithm 4, (56)–(57), p. 35

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_MDP

namespace StatComplexityDM.PCIGW

/-- A choice of StatComplexityDM.TabularPS.value-maximizing randomized policy for every normalized MDP. -/
def IsOptimalSelector {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H) : Prop :=
  ∀ M, StatComplexityDM.TabularPS.IsTabMDP M → RewardsNormalized d1 rv M →
    StatComplexityDM.TabularPS.IsPolicy (piStar M) ∧
      ∀ π, StatComplexityDM.TabularPS.IsPolicy π → StatComplexityDM.TabularPS.value d1 rv M π ≤ StatComplexityDM.TabularPS.value d1 rv M (piStar M)

/-- The StatComplexityDM.TabularPS.value gap under the estimated MDP in Algorithm 4. -/
noncomputable def gapBar {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H) (π : StatComplexityDM.TabularPS.Policy S A H) : ℝ :=
  StatComplexityDM.TabularPS.value d1 rv Mbar (piStar Mbar) - StatComplexityDM.TabularPS.value d1 rv Mbar π

/-- The policies in the cover solve (56) against every randomized Markov policy.
The ratio comparison is cross-multiplied; its denominators are positive under
the assumptions of Algorithm 4. -/
def IsPCIGWCover {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H) (η : ℝ)
    (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H) : Prop :=
  (∀ h s a, StatComplexityDM.TabularPS.IsPolicy (cover h s a)) ∧
  ∀ h s a π, StatComplexityDM.TabularPS.IsPolicy π →
    StatComplexityDM.TabularPS.occ d1 Mbar π h s a *
        (2 * (H : ℝ) * Fintype.card S * Fintype.card A +
          η * gapBar d1 rv Mbar piStar (cover h s a)) ≤
      StatComplexityDM.TabularPS.occ d1 Mbar (cover h s a) h s a *
        (2 * (H : ℝ) * Fintype.card S * Fintype.card A +
          η * gapBar d1 rv Mbar piStar π)

/-- The distinct policies in the cover, together with the estimated-model
maximizer. Repeated cover entries are merged. -/
noncomputable def pcigwPsi {S A W : Type*} [Fintype S] [Fintype A]
    {H : ℕ} (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H) : Finset (StatComplexityDM.TabularPS.Policy S A H) := by
  classical
  exact Finset.univ.image
      (fun x : Fin H × S × A => cover x.1 x.2.1 x.2.2) ∪ {piStar Mbar}

/-- The weight (57) assigned to a policy in the finite support. -/
noncomputable def pcigwWeight {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H) (η lam : ℝ)
    (π : StatComplexityDM.TabularPS.Policy S A H) : ℝ :=
  1 / (lam + η * gapBar d1 rv Mbar piStar π)

/-- Algorithm 4's cover and normalized policy distribution. -/
def IsPCIGW {S A W : Type*} [Fintype S] [Fintype A] [Fintype W]
    {H : ℕ} (d1 : S → ℝ) (rv : W → ℝ) (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H) (η : ℝ)
    (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H) (lam : ℝ) : Prop :=
  IsPCIGWCover d1 rv Mbar piStar η cover ∧ 0 < lam ∧
    ∑ π ∈ pcigwPsi Mbar piStar cover,
      pcigwWeight d1 rv Mbar piStar η lam π = 1

end StatComplexityDM.PCIGW


