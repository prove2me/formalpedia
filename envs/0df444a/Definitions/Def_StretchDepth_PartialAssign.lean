-- Prove2me | Definitions.Def_StretchDepth_PartialAssign
-- name    : StretchDepth_PartialAssign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:07.73408+00:00
-- url     : https://prove2.me/theorems/7140f3b1-bce2-491a-bb2b-ce27de02ddce
-- title:
--   Partial assignments, $\mathcal R^{n,N}_p$ and the planted experiment
-- statement:
--   A **partial assignment** $\rho:\{0,1\}^n\to\{0,1\}^N\cup\{*\}$ assigns each input a value or the symbol $*$ (free). A total $G$ **extends** $\rho$, written $G\supseteq\rho$, if $G(w)=\rho(w)$ wherever $\rho(w)\ne *$; similarly $\tau\supseteq\sigma$ for two partial assignments.
--
--   The distribution $\mathcal R^{n,N}_p$ sets, independently for each $w$, $\rho(w)=*$ with probability $p$ and $\rho(w)=z$ with probability $(1-p)2^{-N}$ for each $z$. For a function $G$ and a set $S$, $G|_{\overline S}$ maps inputs in $S$ to $*$ and every other input $w$ to $G(w)$.
--
--   The definition also fixes the finite expectations and probabilities used in the proofs: $\mathbb E_\rho$, $\Pr_\rho$; the expectation over uniform $G$ and independent $S$ with inclusion probability $p$; and the expectation over the correlated experiment of the proof of Theorem 1, which adds independent uniform $w\in\{0,1\}^n$ and $z\in\{0,1\}^N$.
--
--   **Formalization Note** On p.13 $G|_X$ takes the values of $G$ inside $X$, and the sampling sets $\rho=G|_{\overline S}$: $S$ is the free set. The proof of Theorem 1 writes $G|_{\overline S}$ and $G|_{\overline{S^+}}$ likewise (p.20).
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), §2, p.13; proof of Theorem 1, p.20

import Definitions.Def_StretchDepth_RoundTree

namespace StretchDepth

variable {n N : ℕ}

/-- **Partial assignment.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), §2, p.13: "A partial assignment ρ : {0, 1}n → {0, 1}N ∪ {∗} assigns each input
in {0, 1}n either a value in {0, 1}N or the symbol ∗, indicating that the input is free
(unassigned)." `none` is `∗`. -/
abbrev PartialAssign (n N : ℕ) := Bits n → Option (Bits N)

/-- `G ⊇ ρ`: the total assignment `G` is a completion of `ρ` (§2, p.13). -/
def Extends (G : Bits n → Bits N) (ρ : PartialAssign n N) : Prop :=
  ∀ w z, ρ w = some z → G w = z

/-- `τ ⊇ σ` for partial assignments (§2, p.13). -/
def ExtendsPartial (τ σ : PartialAssign n N) : Prop :=
  ∀ w z, σ w = some z → τ w = some z

/-- The probability of `ρ` under `R^{n,N}_p` (§2, p.13): independently for each `w`, `ρ(w) = ∗`
with probability `p` and `ρ(w) = z` with probability `(1−p)2^{−N}` for each `z`. -/
noncomputable def restrWeight (p : ℝ) (ρ : PartialAssign n N) : ℝ :=
  ∏ w : Bits n, if ρ w = none then p else (1 - p) / 2 ^ N

/-- The probability of `S` when each input is included independently with probability `p`. -/
noncomputable def setWeight (p : ℝ) (S : Finset (Bits n)) : ℝ :=
  ∏ w : Bits n, if w ∈ S then p else 1 - p

/-- The partial assignment `G|_{S̄}` of §2 and §4 (p.13, p.20): inputs in `S` map to `∗` and the
others to their `G`-value.

**Formalization Note.** p.13 defines `G|_X` as taking the values of `G` inside `X` and samples
`ρ = G|_{S̄}`, the restriction to the complement of `S`, so `S` is the free set; p.20 writes
`G|_{S̄}` and `ρ⁺ = G|_{S⁺̄} = G′|_{S⁺̄}` likewise. `freeOn G S` names `G|_{S̄}` by its free set. -/
def freeOn (G : Bits n → Bits N) (S : Finset (Bits n)) : PartialAssign n N :=
  fun w => if w ∈ S then none else some (G w)

/-- `E_{ρ ∼ R^{n,N}_p} f(ρ)`, a finite weighted sum. -/
noncomputable def expRho (p : ℝ) (f : PartialAssign n N → ℝ) : ℝ :=
  ∑ ρ : PartialAssign n N, restrWeight p ρ * f ρ

open Classical in
/-- `Pr_{ρ ∼ R^{n,N}_p}[E(ρ)]`. -/
noncomputable def probRho (p : ℝ) (E : PartialAssign n N → Prop) : ℝ :=
  expRho p fun ρ => if E ρ then 1 else 0

/-- The expectation over uniform `G : {0,1}^n → {0,1}^N` and independent `S` with inclusion
probability `p`, the distribution `D` of the proof of Theorem 1 (p.20). -/
noncomputable def avgGS (p : ℝ) (f : (Bits n → Bits N) → Finset (Bits n) → ℝ) : ℝ :=
  ∑ G : Bits n → Bits N, ∑ S : Finset (Bits n), setWeight p S * f G S / 2 ^ (N * 2 ^ n)

open Classical in
/-- The probability of an event under the distribution of `avgGS`. -/
noncomputable def probGS (p : ℝ) (E : (Bits n → Bits N) → Finset (Bits n) → Prop) : ℝ :=
  avgGS p fun G S => if E G S then 1 else 0

/-- The expectation over the correlated experiment of p.20: `G` uniform, `S` with inclusion
probability `p`, `w` and `z` uniform, all independent. -/
noncomputable def avgPlanted (p : ℝ)
    (F : (Bits n → Bits N) → Finset (Bits n) → Bits n → Bits N → ℝ) : ℝ :=
  avgGS p fun G S => (∑ w : Bits n, ∑ z : Bits N, F G S w z) / (2 ^ n * 2 ^ N)

open Classical in
/-- The probability of an event under the correlated experiment of p.20. -/
noncomputable def probPlanted (p : ℝ)
    (E : (Bits n → Bits N) → Finset (Bits n) → Bits n → Bits N → Prop) : ℝ :=
  avgPlanted p fun G S w z => if E G S w z then 1 else 0

end StretchDepth


