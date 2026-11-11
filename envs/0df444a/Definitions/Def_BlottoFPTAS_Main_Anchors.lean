-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Anchors
-- name    : BlottoFPTAS_Main_Anchors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:42:31.584607+00:00
-- url     : https://prove2.me/theorems/b4068126-4009-4b0b-af45-402eeac026c5
-- title:
--   Label tables, anchor tables, scores s_jl, h*, the static constraints and the polytopes P(γ)
-- statement:
--   Fix $m$ battlefields with values $w$ (the paper's $\hat v$), $e=2^{-a}$ and $K=128/e$ labels per battlefield. A **label table** $(l_{ij})$ has one row per allocation; every label has probability $1/K$ on every battlefield. An **anchor table** $u=(u_{jl})$ gives each label a bid; row $i$ bids $u_{j,l_{ij}}$ on battlefield $j$, and the strategy specified by $u$ is the uniform distribution on the rows, with opponent supremum $U_w(u;c)$. The **static constraints** are $u_{j0}=0$, $u_{jl}\le u_{j,l+1}\le1$ and $\sum_ju_{j,l_{ij}}\le1$ for every row. The **score** of label $l$ on battlefield $j$ is $s_{jl}=\lfloor Sw_j(l+1)/K\rfloor$ with $S=\mathrm{pow2ceil}(128m/e)$; a tuple $(l_1,\dots,l_m)$ has score $\sum_js_{jl_j}$ and anchor sum $\sum_ju_{jl_j}$, and $h^*$ is the largest score of a tuple whose anchor sum is strictly less than $\beta_0$. $P(\gamma)$ is the set of anchor tables $u'$ satisfying the static constraints and the score constraints: every tuple with score greater than $h^*$ has anchor sum at least $\gamma$.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), pp. 40–42, §5.3; p. 64, App. E.1

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Params

open scoped BigOperators
open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# Label tables, anchor tables, scores and the polytopes `P(γ)` (§5.3, pp. 40–42; App. E.1,
p. 64)

Fix `m` reduced battlefields with values `w` (the paper's `v̂`), `e = 2^{-a}`, and `K = 128/e`
labels `0, …, K − 1` per battlefield (`Fin (Klab a)`).

* A **label table** `lab : Fin R → Fin m → Fin K` has `R` rows (one allocation each); every label
  has probability `1/K` on every battlefield (`EachLabelOneOverK`: label `l` occurs in exactly
  `R/K` rows of column `j`).
* An **anchor table** `u : Fin m → Fin K → ℝ` gives a bid to every label; row `i` bids
  `u_{j, lab i j}` on battlefield `j` (`rowAlloc`). The strategy specified by `u` and `lab` is the
  uniform distribution on the rows (`tableLaw`), so `U_w(u; c) = U w (tableLaw u lab) c`.
* **Static constraints** (`IsStatic`): `u_{j0} = 0`, `u_{jl} ≤ u_{j,l+1} ≤ 1`, and every row
  spends at most one.
* **Scores** `s_{jl} = ⌊S w_j (l + 1)/K⌋` with `S = pow2ceil(128m/e)`; a tuple `l` (one label per
  battlefield) has score `∑_j s_{j,l_j}` and anchor sum `∑_j u_{j,l_j}`. `hStar u β₀` is the
  largest score of a tuple whose anchor sum is strictly less than `β₀` (the set is nonempty when
  `u_{j0} = 0` and `β₀ > 0`: the all-zero tuple qualifies).
* `InP γ`: the anchor tables satisfying the static constraints for `lab` and the score constraints
  "every tuple with score greater than `h*` has anchor sum at least `γ`" (the set `P(γ)` of
  App. E.1, with `h*` computed from the old table `u` and the old budget `β₀`).
-/

section

variable {m R : ℕ} (a : ℕ)

/-- Every label has probability `1/K` on every battlefield. -/
def EachLabelOneOverK (lab : Fin R → Fin m → Fin (Klab a)) : Prop :=
  ∀ j l, Klab a * (Finset.univ.filter fun i => lab i j = l).card = R

/-- The allocation of row `i`: `j ↦ u_{j, lab i j}`. -/
def rowAlloc (u : Fin m → Fin (Klab a) → ℝ) (lab : Fin R → Fin m → Fin (Klab a)) (i : Fin R) :
    Fin m → ℝ :=
  fun j => u j (lab i j)

/-- The uniform distribution on the rows of the label table under the anchors `u`. -/
noncomputable def tableLaw (u : Fin m → Fin (Klab a) → ℝ) (lab : Fin R → Fin m → Fin (Klab a)) :
    Measure (Fin m → ℝ) :=
  uniformList (List.ofFn fun i => rowAlloc a u lab i)

/-- The static constraints: `u_{j0} = 0`, `u_{jl} ≤ u_{j,l+1} ≤ 1`, every row spends at most
one. -/
def IsStatic (u : Fin m → Fin (Klab a) → ℝ) (lab : Fin R → Fin m → Fin (Klab a)) : Prop :=
  (∀ j, u j 0 = 0) ∧ (∀ j (l l' : Fin (Klab a)), l ≤ l' → u j l ≤ u j l') ∧
    (∀ j l, u j l ≤ 1) ∧ (∀ i, ∑ j, u j (lab i j) ≤ 1)

/-- The score `s_{jl} = ⌊S w_j (l + 1)/K⌋`. -/
noncomputable def score (w : Fin m → ℝ) (j : Fin m) (l : Fin (Klab a)) : ℤ :=
  ⌊(Sscore m a : ℝ) * w j * ((l : ℝ) + 1) / Klab a⌋

/-- The score `∑_j s_{j,l_j}` of a tuple. -/
noncomputable def tupleScore (w : Fin m → ℝ) (l : Fin m → Fin (Klab a)) : ℤ :=
  ∑ j, score a w j (l j)

/-- The anchor sum `∑_j u_{j,l_j}` of a tuple. -/
def anchorSum (u : Fin m → Fin (Klab a) → ℝ) (l : Fin m → Fin (Klab a)) : ℝ :=
  ∑ j, u j (l j)

/-- `h*`: the largest score of a tuple with anchor sum strictly less than `β₀`. -/
noncomputable def hStar (w : Fin m → ℝ) (u : Fin m → Fin (Klab a) → ℝ) (β₀ : ℝ) : ℤ :=
  sSup {h : ℤ | ∃ l : Fin m → Fin (Klab a), anchorSum a u l < β₀ ∧ h = tupleScore a w l}

/-- `u′ ∈ P(γ)` (App. E.1), with `h*` computed from the old table `u` and old budget `β₀`. -/
def InP (w : Fin m → ℝ) (u : Fin m → Fin (Klab a) → ℝ) (β₀ : ℝ)
    (lab : Fin R → Fin m → Fin (Klab a)) (γ : ℝ) (u' : Fin m → Fin (Klab a) → ℝ) : Prop :=
  IsStatic a u' lab ∧
    ∀ l : Fin m → Fin (Klab a), hStar a w u β₀ < tupleScore a w l → γ ≤ anchorSum a u' l

end

end BlottoFPTAS.Main


