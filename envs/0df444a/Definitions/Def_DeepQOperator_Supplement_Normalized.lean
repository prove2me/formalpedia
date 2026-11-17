-- Prove2me | Definitions.Def_DeepQOperator_Supplement_Normalized
-- name    : DeepQOperator_Supplement_Normalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:40:34.626088+00:00
-- url     : https://prove2.me/theorems/d2c8bf2f-ac9c-4464-86a5-1074240995e5
-- title:
--   The normalized Bellman family (76)–(78)
-- statement:
--   Fix $m\ge2$ and $\theta=(s,z_1,\dots,z_m)\in P_m=[0,m+1]\times[0,1]^m$. For each $j\in[m]$ there are two rows
--   $$
--   A_j(\theta)=\max\{z_j,\,2(s-j),\,-2(s-j)\},\qquad B_j(\theta)=\max\{2(s-j),\,-2(s-j)\}.
--   $$
--   Decision $+$ uses the uniform response $1/m$ on the $A$ rows and reward $r_+=-\gamma/(2m)$. Decision $-$ uses the uniform response on the $B$ rows and reward $r_-=0$. Hence
--   $$
--   t_+(\theta)-t_-(\theta)=\frac{\gamma}{m}\Big(F(\theta)-\frac12\Big),\qquad F(\theta)=\sum_{j=1}^m[z_j-2|s-j|]_+ ,
--   $$
--   and the loss is (3). The listed affine expressions $z_j$, $2(s-j)$, $-2(s-j)$ are the raw sites. Write $c=\gamma/m$ for the contrast scale.
--
--   This family carries the normalized-scale results (Theorems 12–15, 21, 24).
--
--   **Formalization Note** Coordinates are $\{s\}\sqcup\{1,\dots,m\}$. The scores are written out over the $2m$ rows.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix L.1 eqs. (76)–(78), p.43 (PDF p.46)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator.Supplement

/-!
# The normalized Bellman family (76)–(78)

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix L.1 eqs. (76)–(78) p.43 (PDF p.46).

Fix `m ≥ 2` and `θ = (s, z_1, …, z_m) ∈ P_m = [0, m+1] × [0,1]^m`. For each `j ∈ [m]` there are two
rows `A_j = max{z_j, 2(s − j), −2(s − j)}` and `B_j = max{2(s − j), −2(s − j)}`. Decision `+` uses
the uniform response on the `A` rows with reward `r₊ = −γ/(2m)`; decision `−` the uniform response on
the `B` rows with reward `0`. Then `t₊ − t₋ = (γ/m)(F − 1/2)` with `F = Σ_j [z_j − 2|s − j|]₊`. The
listed affine expressions `z_j`, `2(s − j)`, `−2(s − j)` are the raw sites.

**Formalization Note.**
* The coordinates are `Unit ⊕ Fin m`: `Sum.inl ()` is `s` and `Sum.inr j` is `z_{j+1}`; the row index
  `j : Fin m` stands for `j + 1 ∈ [m]`.
* The Bellman scores (1) over the `2m` rows are written out: `t₊ = −γ/(2m) + γ Σ_j (1/m) A_j`,
  `t₋ = 0 + γ Σ_j (1/m) B_j`. `nLoss m γ a θ` is the loss (3); `true` is `+`.
-/

/-- Coordinates of the normalized family. -/
abbrev NCoord (m : ℕ) : Type := Unit ⊕ Fin m

/-- The box `P_m = [0, m+1] × [0,1]^m` of (76). -/
def nBox (m : ℕ) : Set (NCoord m → ℝ) :=
  {θ | θ (Sum.inl ()) ∈ Set.Icc (0 : ℝ) (m + 1) ∧ ∀ j : Fin m, θ (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1}

/-- Row `B_j = max{2(s − j), −2(s − j)}` (row index `j + 1`). -/
noncomputable def nRowB (m : ℕ) (j : Fin m) (θ : NCoord m → ℝ) : ℝ :=
  max (2 * (θ (Sum.inl ()) - ((j : ℝ) + 1))) (-(2 * (θ (Sum.inl ()) - ((j : ℝ) + 1))))

/-- Row `A_j = max{z_j, 2(s − j), −2(s − j)}` (row index `j + 1`). -/
noncomputable def nRowA (m : ℕ) (j : Fin m) (θ : NCoord m → ℝ) : ℝ :=
  max (θ (Sum.inr j)) (nRowB m j θ)

/-- `t₊ = −γ/(2m) + γ Σ_j (1/m) A_j`. -/
noncomputable def nPlus (m : ℕ) (γ : ℝ) (θ : NCoord m → ℝ) : ℝ :=
  -γ / (2 * (m : ℝ)) + γ * ∑ j : Fin m, (1 / (m : ℝ)) * nRowA m j θ

/-- `t₋ = 0 + γ Σ_j (1/m) B_j`. -/
noncomputable def nMinus (m : ℕ) (γ : ℝ) (θ : NCoord m → ℝ) : ℝ :=
  0 + γ * ∑ j : Fin m, (1 / (m : ℝ)) * nRowB m j θ

/-- The score of decision `a` (`true` is `+`). -/
noncomputable def nScore (m : ℕ) (γ : ℝ) (a : Bool) (θ : NCoord m → ℝ) : ℝ :=
  if a then nPlus m γ θ else nMinus m γ θ

/-- The decision loss (3) of the normalized family. -/
noncomputable def nLoss (m : ℕ) (γ : ℝ) (a : Bool) (θ : NCoord m → ℝ) : ℝ :=
  max (nPlus m γ θ) (nMinus m γ θ) - nScore m γ a θ

/-- The raw site `z_j`. -/
noncomputable def nSiteZ (m : ℕ) (j : Fin m) : AffQuery (NCoord m) :=
  (Sum.elim (fun _ => 0) (fun j' => if j' = j then 1 else 0), 0)

/-- The raw site `2(s − j)`. -/
noncomputable def nSitePos (m : ℕ) (j : Fin m) : AffQuery (NCoord m) :=
  (Sum.elim (fun _ => 2) (fun _ => 0), -(2 * ((j : ℝ) + 1)))

/-- The raw site `−2(s − j)`. -/
noncomputable def nSiteNeg (m : ℕ) (j : Fin m) : AffQuery (NCoord m) :=
  (Sum.elim (fun _ => -2) (fun _ => 0), 2 * ((j : ℝ) + 1))

/-- The raw dictionary of (77): the listed affine expressions of the rows. -/
noncomputable def nDictionary (m : ℕ) : Set (AffQuery (NCoord m)) :=
  Set.range (nSiteZ m) ∪ Set.range (nSitePos m) ∪ Set.range (nSiteNeg m)

end DeepQOperator.Supplement


