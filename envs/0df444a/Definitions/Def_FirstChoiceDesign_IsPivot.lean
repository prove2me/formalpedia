-- Prove2me | Definitions.Def_FirstChoiceDesign_IsPivot
-- name    : FirstChoiceDesign_IsPivot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:37.864922+00:00
-- url     : https://prove2.me/theorems/b2b87249-ca51-4735-9254-2eb0c4c1efe2
-- title:
--   Pivot students $i_0(r),i_1(r)$ and consecutive students
-- statement:
--   The **pivot students** of $r$ at $s$ are the two students with $i_0(r),i_1(r)\in\mathit{First}_s(r)$, $D_{i_0(r)s}(r)=0$, $D_{i_1(r)s}(r)=1$, $r_{i_0(r)s}\le r_{is}$ for all $i\in\mathit{First}_s(r)$ with $D_{is}(r)=0$, and $r_{i_1(r)s}\ge r_{is}$ for all $i\in\mathit{First}_s(r)$ with $D_{is}(r)=1$. If there are no two students satisfying the conditions, the source sets $i_0(r)=i_1(r)=\emptyset$.
--
--   Two students $i',i''$ are **consecutive in $r_s$ within $\mathit{First}_s(r)$** if both lie in $\mathit{First}_s(r)$ and no $i^{\prime\prime\prime}\in\mathit{First}_s(r)$ has $r_{i's}<r_{i^{\prime\prime\prime}s}<r_{i''s}$ or $r_{i's}>r_{i^{\prime\prime\prime}s}>r_{i''s}$.
--
--   **Formalization Note** `IsPivot φ X s r i₀ i₁` is a predicate, and the source's case "$\emptyset$" is the case where no pair satisfies it. `Consecutive` adds $i'\ne i''$, because $\hat\sigma_s(r)$ "switches only two students".
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Main Proof, p.45 and p.46

import Definitions.Def_FirstChoiceDesign_First

namespace FirstChoiceDesign

/-- The pivot students `i₀(r), i₁(r)` of "Main Proof", p.45: both in `First_s(r)`, `D_{i₀ s}(r) = 0`,
`D_{i₁ s}(r) = 1`, `r_{i₀ s} ≤ r_is` for all rejected `i ∈ First_s(r)`, and `r_{i₁ s} ≥ r_is` for all
assigned `i ∈ First_s(r)`. "`i₀(r) = i₁(r) = ∅`" is the case where no such pair exists. -/
def IsPivot {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i₀ i₁ : Fin n) : Prop :=
  i₀ ∈ First φ X s r ∧ i₁ ∈ First φ X s r ∧ ¬ D φ X i₀ s r ∧ D φ X i₁ s r ∧
    (∀ i ∈ First φ X s r, ¬ D φ X i s r → r i₀ s ≤ r i s) ∧
    ∀ i ∈ First φ X s r, D φ X i s r → r i s ≤ r i₁ s

/-- Students `i', i''` are consecutive in `r_s` within `First_s(r)`, p.46: both in `First_s(r)`,
distinct, with no `i''' ∈ First_s(r)` strictly between them in `r_s`. -/
def Consecutive {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i' i'' : Fin n) : Prop :=
  i' ∈ First φ X s r ∧ i'' ∈ First φ X s r ∧ i' ≠ i'' ∧
    ¬ ∃ i''' ∈ First φ X s r,
      (r i' s < r i''' s ∧ r i''' s < r i'' s) ∨ (r i'' s < r i''' s ∧ r i''' s < r i' s)

end FirstChoiceDesign


