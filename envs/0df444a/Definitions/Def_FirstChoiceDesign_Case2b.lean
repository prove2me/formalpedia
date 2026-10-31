-- Prove2me | Definitions.Def_FirstChoiceDesign_Case2b
-- name    : FirstChoiceDesign_Case2b
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:52.920061+00:00
-- url     : https://prove2.me/theorems/97b9cef5-0695-41d7-9e02-61e624b52a56
-- title:
--   The situation of Case 2.b, the preference change, and the column $\hat\sigma^\#_s(r)$
-- statement:
--   **Case 2.b.** Students $i',i''$ are consecutive in $r_s$ within $\mathit{First}_s(r)$, with $D_{i's}(r)=D_{i''s}(r)=0$ and, without loss of generality, $r_{i's}<r_{i''s}$. Some $i\in\mathit{First}_s(r)$ has $D_{is}(\hat\sigma(r))=0\ne1=D_{is}(r)$. The student $i^*\in\mathit{First}_s(r)$ is the assigned student of $\mathit{First}_s(r)$ with the largest number at $s$.
--
--   **Preference change.** Student $i^*$'s preference is changed to $\succ'_{i^*}$ with $s\succ'_{i^*}\emptyset\succ'_{i^*}s'$ for all $s'\ne s$.
--
--   **The column $\hat\sigma^\#_s(r)$** is the further permutation of $\hat\sigma_s(r)$ with $\hat\sigma^\#_{i''s}(r)=\min\{\hat\sigma_{js}(r)\mid j\in\mathit{First}_s(r),D_{js}(r)=0\}$, with $\hat\sigma^\#_{i's}(r)=\min\{\hat\sigma_{js}(r)\ne\hat\sigma^\#_{i''s}(r)\mid j\in\mathit{First}_s(r),D_{js}(r)=0\}$, and with $\hat\sigma^\#_{js}(r)>\hat\sigma^\#_{ks}(r)$ if and only if $\hat\sigma_{js}(r)>\hat\sigma_{ks}(r)$ for all $j,k\in I\setminus\{i',i''\}$.
--
--   **Formalization Note** `Case2b` records the situation in the original problem. `IsTruncation X X' iStar s` relates a problem to any problem with the change: the source leaves the order among the schools $s'\ne s$ free. `IsSigmaSharp` is a predicate on a column. It takes the problem as an argument because the source defines $\hat\sigma^\#_s(r)$ after the change, and $\mathit{First}_s(r)$, $D$ at $r$ are those of the changed problem there. The verification file proves that a changed problem always exists.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Case 2.b, p.55

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_Swap

namespace FirstChoiceDesign

/-- The situation of Case 2.b, p.55, with its two "Without loss of generality" normalizations: `i', i''`
are consecutive in `r_s` within `First_s(r)`, both rejected, with `r_i's < r_i''s`; `i ∈ First_s(r)`
has `D_is(σ̂(r)) = 0 ≠ 1 = D_is(r)`; and `iStar ∈ First_s(r)` is the assigned student of `First_s(r)`
with the largest number, the page's `i*`. -/
def Case2b {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i i' i'' iStar : Fin n) : Prop :=
  Consecutive φ X s r i' i'' ∧ ¬ D φ X i' s r ∧ ¬ D φ X i'' s r ∧ r i' s < r i'' s ∧
    i ∈ First φ X s r ∧ ¬ D φ X i s (swapReg φ.regime s i' i'' r) ∧ D φ X i s r ∧
    iStar ∈ First φ X s r ∧ D φ X iStar s r ∧
    ∀ j ∈ First φ X s r, D φ X j s r → r j s ≤ r iStar s

/-- `X'` is `X` with `iStar`'s preference changed to `≻'` with `s ≻' ∅ ≻' s'` for all `s' ≠ s`, p.55,
and nothing else changed. The page leaves the order among the schools `s' ≠ s` free, so does this
predicate. -/
def IsTruncation {K n m : ℕ} (X X' : Problem K n m) (iStar : Fin n) (s : Fin m) : Prop :=
  X'.c = X.c ∧ X'.ρ = X.ρ ∧ (∀ i, i ≠ iStar → X'.u i = X.u i) ∧
    X'.u iStar (some s) < X'.u iStar none ∧
    ∀ s', s' ≠ s → X'.u iStar none < X'.u iStar (some s')

/-- `c` is the column `σ̂^#_s(r)` of Case 2.b, p.55, the further permutation of `σ̂_s(r)` (which
switches `i', i''` in `r_s`) with `σ̂^#_{i'' s}(r) = min{σ̂_js(r) | j ∈ First_s(r), D_js(r) = 0}`,
`σ̂^#_{i' s}(r) = min{σ̂_js(r) ≠ σ̂^#_{i'' s}(r) | j ∈ First_s(r), D_js(r) = 0}`, and the order of all
`j, k ∈ I ∖ {i', i''}` unchanged. `First_s(r)` and `D` are those of the problem passed as `X`. -/
def IsSigmaSharp {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i' i'' : Fin n) (c : Fin n → ℝ) : Prop :=
  (∃ π : Equiv.Perm (Fin n), ∀ j, c j = r (π j) s) ∧
    IsLeast {x | ∃ j ∈ First φ X s r, ¬ D φ X j s r ∧ r (Equiv.swap i' i'' j) s = x} (c i'') ∧
    IsLeast {x | ∃ j ∈ First φ X s r, ¬ D φ X j s r ∧ r (Equiv.swap i' i'' j) s = x ∧ x ≠ c i''}
      (c i') ∧
    ∀ j k, j ≠ i' → j ≠ i'' → k ≠ i' → k ≠ i'' →
      (c k < c j ↔ r (Equiv.swap i' i'' k) s < r (Equiv.swap i' i'' j) s)

end FirstChoiceDesign


