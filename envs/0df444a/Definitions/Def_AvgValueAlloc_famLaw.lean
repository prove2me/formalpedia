-- Prove2me | Definitions.Def_AvgValueAlloc_famLaw
-- name    : AvgValueAlloc_famLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:54.796063+00:00
-- url     : https://prove2.me/theorems/926c6b1a-9f7a-4f52-aec9-63b6827a0114
-- title:
--   Threshold-centered hard law $D_J$ of (11)
-- statement:
--   Fix $d$ original buyers $I$ with $a=\min_{j\in I}\rho_j$ and $\rho_j<2a$ on $I$, integers $k\ge2$, $T\ge8k$, and put
--   $$
--   p_0=q_0=1/T,\quad h=k/T,\quad \beta_j=\rho_j+a/T,\quad \nu_j=\rho_j-a/T^2.\tag{11}
--   $$
--   Under $D_J$ ($J\in I$), with probability $p_0$ the item is the sponsor with values $\beta_j$ on $I$; otherwise its values are $\nu_jX_j$ on $I$ with independent bits $X_J\sim\mathrm{Ber}(h)$ and $X_j\sim\mathrm{Ber}(q_0)$ for $j\neq J$. All other buyers have value zero.
--
--   **Formalization Note** The values are cast to $\mathbb Q_{\ge0}$, exactly since $\beta_j,\nu_j>0$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §5, p.10, eq. (11); §5.1, p.11

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw

namespace AvgValueAlloc

/-- `a = min_{j ∈ I} ρ_j` (`0` for an empty `I`, never used). -/
def famMin {n : ℕ} (ρ : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  if h : I.Nonempty then I.inf' h ρ else 0

/-- `β_j = ρ_j + a/T`. -/
def famBeta {n : ℕ} (ρ : Fin n → ℚ) (I : Finset (Fin n)) (T : ℕ) (j : Fin n) : ℚ :=
  ρ j + famMin ρ I / T

/-- `ν_j = ρ_j − a/T²`. -/
def famNu {n : ℕ} (ρ : Fin n → ℚ) (I : Finset (Fin n)) (T : ℕ) (j : Fin n) : ℚ :=
  ρ j - famMin ρ I / (T : ℚ) ^ 2

/-- The eligibility rate of buyer `j` under hypothesis `J`: `h = k/T` at `J`, `q₀ = 1/T` elsewhere. -/
noncomputable def famRate {n : ℕ} (k T : ℕ) (J j : Fin n) : ℝ :=
  if j = J then (k : ℝ) / T else 1 / (T : ℝ)

/-- **The threshold-centered hard law `D_J` of (11).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §5, p.10, (11): "Choose d original buyers I with
a = min_{j∈I} ρ_j ≤ ρ_j < 2a. Give every other buyer value zero … For T ≥ 8k, k ≥ 2, put p_0 = q_0 =
1/T, h = k/T, β_j = ρ_j + a/T, ν_j = ρ_j − a/T². A sponsor of probability p_0 has active values β_j.
Otherwise values are ν_jX_j, with independent eligibility bits."; §5.1, p.11: "Under D_J, let X_J ∼
Ber(h) and all other coordinates be Ber(q_0)."

`famLaw ρ I k T J`: with probability `1/T` the sponsor vector (`β_j` on `I`, `0` elsewhere);
otherwise the mask vector `ν_j X_j` on `I` (`0` elsewhere) with independent bits `X_J ∼ Ber(k/T)`
and `X_j ∼ Ber(1/T)` for `j ∈ I \ {J}`.

**Formalization Note.** Atoms are `none` (sponsor) and `some x` (mask `x : I → Bool`). Values are
cast to `ℚ≥0` by `Rat.toNNRat`, which is exact because `β_j, ν_j > 0` whenever `T ≥ 1`. With
`T ≥ 8k`, `k ≥ 2` every weight is positive and rational and the weights sum to one. -/
noncomputable def famLaw {n : ℕ} (ρ : Fin n → ℚ) (I : Finset (Fin n)) (k T : ℕ) (J : Fin n) :
    FinLaw n where
  ι := Option (I → Bool)
  p := fun o => match o with
    | none => 1 / (T : ℝ)
    | some x => (1 - 1 / (T : ℝ)) *
        ∏ j : I, if x j then famRate k T J j.1 else 1 - famRate k T J j.1
  val := fun o => match o with
    | none => fun j => if j ∈ I then (famBeta ρ I T j).toNNRat else 0
    | some x => fun j => if h : j ∈ I then (if x ⟨j, h⟩ then (famNu ρ I T j).toNNRat else 0) else 0

end AvgValueAlloc


