-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_Counting
-- name    : MultiCorrectPAC_Demo_Counting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:41.16786+00:00
-- url     : https://prove2.me/theorems/d02f5dba-a0f9-431f-8e37-82592a2a4bc0
-- title:
--   Finite label spaces: $q=|\mathcal A|$, the number $\Gamma$ of minimal empty-intersection families, $\Pi_d(n)$, $M_d(n)$ and finite covers
-- statement:
--   Let $\mathcal Y$ be finite with $k=|\mathcal Y|$. Put $q=|\mathcal A|=\sum_{j=1}^{\ell}\binom kj$ (2), let $\Gamma$ be the number of minimal empty-intersection families contained in $\mathcal A$ (12), and for integers $d,n\ge0$
--   $$\Pi_d(n)=\sum_{j=0}^{\min\{d,n\}}\binom nj\Gamma^j\ (\Gamma^0=1),\qquad M_d(n)=\Big\lceil\frac{\log\Pi_d(n)}{\log(1+1/\ell)}\Big\rceil \tag{14, 18}$$
--   (natural logarithms). A **finite cover** of $\mathcal H$ on a pool $S=(x_1,\dots,x_n)$ (repetitions allowed) is a finite $F\subseteq\mathcal Y^n$ such that every $h\in\mathcal H$ has some $f\in F$ with $f(i)\in h(x_i)$ at every position $i$ with $x_i\in\operatorname{supp}(h)$.
--
--   **Formalization Note** `setsA Y ℓ`, `qCount`, `gammaCount`, `piCount`, `mBound` are computed over `[Fintype Y]`; families are `Finset (Finset Y)`; $M_d(n)$ is `Nat.ceil` of the real quotient (`Real.log`), the ceiling printed in (18). Pools are `S : Fin n → X`, covers `Finset (Fin n → Y)`.
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 25 (PDF 27), (2); pp. 37–40 (PDF 39–42), (12), (14), (18), §7.2

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
(2) (printed p. 25, PDF 27), (12), (14), (18) (pp. 37–39, PDF 39–41) and finite covers (§7.2,
p. 40, PDF 42), for a finite label space `Y` with `k = |Y|`. -/

/-- The collection `𝒜 = {A ⊆ Y : 1 ≤ |A| ≤ ℓ}` of (1), as a finset. -/
def setsA (Y : Type*) [Fintype Y] [DecidableEq Y] (ℓ : ℕ) : Finset (Finset Y) :=
  Finset.univ.filter fun A => A.Nonempty ∧ A.card ≤ ℓ

/-- `q = |𝒜| = Σ_{j=1}^ℓ C(k, j)` (2). -/
def qCount (Y : Type*) [Fintype Y] [DecidableEq Y] (ℓ : ℕ) : ℕ := (setsA Y ℓ).card

open Classical in
/-- `Γ = |𝒞|`, the number of minimal empty-intersection families contained in `𝒜` (12). -/
noncomputable def gammaCount (Y : Type*) [Fintype Y] [DecidableEq Y] (ℓ : ℕ) : ℕ :=
  ((setsA Y ℓ).powerset.filter fun 𝒜 => IsMinimalEmptyInter 𝒜).card

/-- `Π_d(n) = Σ_{j=0}^{min{d,n}} C(n, j) Γ^j` (14), with `Γ⁰ = 1`. -/
noncomputable def piCount (Y : Type*) [Fintype Y] [DecidableEq Y] (ℓ d n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min d n + 1), n.choose j * gammaCount Y ℓ ^ j

/-- `M_d(n) = ⌈log Π_d(n) / log(1 + 1/ℓ)⌉` (18). -/
noncomputable def mBound (Y : Type*) [Fintype Y] [DecidableEq Y] (ℓ d n : ℕ) : ℕ :=
  ⌈Real.log (piCount Y ℓ d n) / Real.log (1 + 1 / (ℓ : ℝ))⌉₊

/-- A finite cover of `H` on the pool `S = (x₁, …, xₙ)` (repetitions allowed; §7.2): a finite
`F ⊆ Yⁿ` such that every `h ∈ H` has some `f ∈ F` with `f(i) ∈ h(xᵢ)` at every position `i` with
`xᵢ ∈ supp(h)`. -/
def IsFiniteCover {X Y : Type*} (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X)
    (F : Finset (Fin n → Y)) : Prop :=
  ∀ h ∈ H, ∃ f ∈ F, ∀ i (A : Finset Y), h (S i) = some A → f i ∈ A

end MultiCorrectPAC.Demo


