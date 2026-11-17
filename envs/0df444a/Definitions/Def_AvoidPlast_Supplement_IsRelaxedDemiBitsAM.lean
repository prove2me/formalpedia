-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsRelaxedDemiBitsAM
-- name    : AvoidPlast_Supplement_IsRelaxedDemiBitsAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:08:51.797211+00:00
-- url     : https://prove2.me/theorems/aee06789-6c1c-46a8-b7b4-40cb42e4edf5
-- title:
--   Relaxed $\varepsilon$-demi-bits against AM (Definition 6.3)
-- statement:
--   $g$ is a relaxed $\varepsilon$-demi-bits generator against $\mathsf{AM}$ if no polynomial-time AM verifier $V(y,r,w)$ satisfies, for every sufficiently large $n$:
--
--   1. for at least $\varepsilon(n)\cdot2^n$ strings $y$, $\Pr_r[\exists w: V(y,r,w)=1]\ge2/3$;
--   2. for every $y$ in the range of $g_n$, $\Pr_r[\exists w: V(y,r,w)=1]<1/3$.
--
--   The coins $r$ have a fixed polynomial length and witnesses polynomial length.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 6.3, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `g` is a relaxed `ε`-demi-bits generator against AM (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 6.3, p.33): no
polynomial-time AM verifier `V(y, r, w)` satisfies, for every sufficiently large `n`,
(1) at least `ε(n)·2^n` strings `y` have `Pr_r[∃ w : V(y, r, w) = 1] ≥ 2/3`, and (2) every `y` in
the range of `g_n` has `Pr_r[∃ w : V(y, r, w) = 1] < 1/3`. The coins `r` have the fixed length
`a(n^a + 1)` and witnesses at most that length. -/
def IsRelaxedDemiBitsAM (g : ℕ → List Bool → List Bool) (ℓ : ℕ → ℕ) (ε : ℕ → ℝ) : Prop :=
  ¬ ∃ (V : Machine 3) (a : ℕ),
    (∀ y r w : List Bool, HaltsWithin V ![y, r, w] (a * (y.length ^ a + 1))) ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      ε n ≤ prob n (fun y => (2 : ℝ) / 3 ≤ prob (a * (n ^ a + 1)) fun r =>
        ∃ w : List Bool, w.length ≤ a * (n ^ a + 1) ∧ Accepts V ![y, r, w]) ∧
      ∀ x : List Bool, x.length = ℓ n → prob (a * (n ^ a + 1)) (fun r =>
        ∃ w : List Bool, w.length ≤ a * (n ^ a + 1) ∧ Accepts V ![g n x, r, w]) < 1 / 3

end AvoidPlast.Supplement


