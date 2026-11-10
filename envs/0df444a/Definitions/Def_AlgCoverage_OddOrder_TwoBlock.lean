-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_TwoBlock
-- name    : AlgCoverage_OddOrder_TwoBlock
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:30.827389+00:00
-- url     : https://prove2.me/theorems/01c3f433-7716-43ef-8438-e82534e4851d
-- title:
--   The two local suffix blocks of §7: block-local FULL tests, the good event $E_S$, the good mass $\gamma(U_S)$ and the deficit bound $\beta$
-- statement:
--   Let $k$ inputs be split so that the last $\ell_1+\ell_2$ positions form a **suffix** $S$, divided into two successive nonempty blocks $S_1$ (the first $\ell_1$ positions of $S$) and $S_2$ (the last $\ell_2$). For a selector array $U$ and a block, the **local FULL test** is FULL of the rows restricted to that block, i.e. of the block words restarted at the identity; it depends only on the inputs in the block. The **good event** $E_S$ says that both local tests pass. With $\mu_a(w)=\Pr(\text{block-}a\text{ words}=w,\ \text{local FULL}_a)$, a subprobability of mass $1-\delta_a$, the **good mass** is
--   $$\gamma(U_S)=(1-\delta_1-\delta_2)_+ ,$$
--   which depends on the masks only. For a series with $J$ layers and an envelope value $A_*$, the **deficit bound** of (7.5) is $\beta=\min\{1,\ JA_*(2^{-\ell_1}+2^{-\ell_2})\}$.
--
--   **Formalization Note.** Positions are 0-based: $S_1=\{k-\ell_1-\ell_2,\dots,k-\ell_2-1\}$ and $S_2=\{k-\ell_2,\dots,k-1\}$ (natural-number subtraction; statements assume $\ell_1+\ell_2\le k$). A restricted row keeps its bits inside the block and is $0$ outside; for a position inside a contiguous block its selected prefix is exactly the block-local prefix. $\delta_a$ is the iid probability that the local test of block $a$ fails.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), pp. 22–23 (PDF 23–24), §7, Eqs. (7.2)–(7.5)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Series

namespace AlgCoverage.OddOrder

/-! The two local suffix blocks of §7 (Lin, printed pp. 22–23 / PDF 23–24). The suffix
`S = {k − ℓ₁ − ℓ₂, …, k − 1}` of the input positions (0-based) is split into the successive blocks
`S₁ = {k − ℓ₁ − ℓ₂, …, k − ℓ₂ − 1}` (length `ℓ₁`) and `S₂ = {k − ℓ₂, …, k − 1}` (length `ℓ₂`). -/

/-- Membership in the first block `S₁`. -/
def inBlock1 (k ℓ₁ ℓ₂ : ℕ) (i : Fin k) : Bool :=
  decide (k - ℓ₁ - ℓ₂ ≤ i.val ∧ i.val < k - ℓ₂)

/-- Membership in the second block `S₂`. -/
def inBlock2 (k ℓ₂ : ℕ) (i : Fin k) : Bool :=
  decide (k - ℓ₂ ≤ i.val)

/-- Membership in the suffix `S = S₁ ∪ S₂`. -/
def inSuffix (k ℓ₁ ℓ₂ : ℕ) (i : Fin k) : Bool :=
  decide (k - ℓ₁ - ℓ₂ ≤ i.val)

/-- The selector array restricted to a block: row `u` keeps its bits inside the block and is `0`
outside. Its words are the block words `V^{(a)}` (the block restarted at the identity), and its
coefficient prefixes are the block-local prefixes. -/
def restrictRows {ι : Type*} {k : ℕ} (rows : ι → Fin k → Bool) (S : Fin k → Bool) :
    ι → Fin k → Bool :=
  fun u i => rows u i && S i

/-- The local FULL test of block `S₁`: FULL of the rows restricted to `S₁` (it depends only on the
inputs in `S₁`). -/
def localFULL1 {G : Type*} [Group G] (s : NormalEASeries G) {ι : Type*} {k : ℕ} (ℓ₁ ℓ₂ : ℕ)
    (x : Fin k → G) (rows : ι → Fin k → Bool) : Prop :=
  FULL s x (restrictRows rows (inBlock1 k ℓ₁ ℓ₂))

/-- The local FULL test of block `S₂`. -/
def localFULL2 {G : Type*} [Group G] (s : NormalEASeries G) {ι : Type*} {k : ℕ} (ℓ₂ : ℕ)
    (x : Fin k → G) (rows : ι → Fin k → Bool) : Prop :=
  FULL s x (restrictRows rows (inBlock2 k ℓ₂))

/-- The good event `E_S`: both local tests pass. -/
def GoodS {G : Type*} [Group G] (s : NormalEASeries G) {ι : Type*} {k : ℕ} (ℓ₁ ℓ₂ : ℕ)
    (x : Fin k → G) (rows : ι → Fin k → Bool) : Prop :=
  localFULL1 s ℓ₁ ℓ₂ x rows ∧ localFULL2 s ℓ₂ x rows

/-- `γ(U_S) = (1 − δ₁ − δ₂)₊`, where `1 − δ_a` is the mass of the block subprobability
`μ_a(w) = Pr(block words = w, local FULL of block a)`, i.e. `δ_a = Pr(local FULL of block a fails)`
over the uniform inputs (iid model). It depends on the masks only. -/
noncomputable def gammaS {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) {ι : Type*}
    (k ℓ₁ ℓ₂ : ℕ) (rows : ι → Fin k → Bool) : ℝ :=
  max 0 (1 - probIid G k (fun x => ¬ localFULL1 s ℓ₁ ℓ₂ x rows)
           - probIid G k (fun x => ¬ localFULL2 s ℓ₂ x rows))

/-- The deficit bound `β = min{1, J A_*(2^{−ℓ₁} + 2^{−ℓ₂})}` of (7.5), for a series with `J` layers and
an envelope value `A_*`. -/
noncomputable def betaDef (J : ℕ) (Astar : ℝ) (ℓ₁ ℓ₂ : ℕ) : ℝ :=
  min 1 ((J : ℝ) * Astar * ((2 : ℝ) ^ (-(ℓ₁ : ℤ)) + (2 : ℝ) ^ (-(ℓ₂ : ℤ))))

end AlgCoverage.OddOrder


