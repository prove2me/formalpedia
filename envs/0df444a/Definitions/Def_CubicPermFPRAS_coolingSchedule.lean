-- Prove2me | Definitions.Def_CubicPermFPRAS_coolingSchedule
-- name    : CubicPermFPRAS_coolingSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:01.82792+00:00
-- url     : https://prove2.me/theorems/19314591-2818-4913-9ef6-3a13592e3b64
-- title:
--   The annealing schedule of Lemma 50 and the cooling schedule $\lambda_i=e^{-\beta_i}$
-- statement:
--   Given $H_{\max}$, $\Delta$ and $\beta_{\max}$, the **annealing schedule** of Lemma 50 is $\beta_0=0$, $\beta_{i+1}=\beta_i+d_i$ with
--   $$d_i=\min\Big\{\beta_{\max}-\beta_i,\ \tfrac14\max\Big\{\tfrac1{H_{\max}},\tfrac{\beta_i}{\Delta}\Big\}\Big\},$$
--   and its length $L$ is the first index with $\beta_L=\beta_{\max}$. For $H:\Omega\to\mathbb R$ and a family $S$, $Z_S(\beta)=\sum_{M\in S}e^{-\beta H(M)}$, $z_S=\log Z_S$, and the relative second moment of $Y=\prod_{i<L}e^{-d_iH(M_i)}$ with independent $M_i\sim\mu_{S,\beta_i}\propto e^{-\beta_iH}$ is $\prod_i\mathbb E[Y_i^2]/(\prod_i\mathbb E[Y_i])^2$.
--
--   The **cooling schedule** of the input is this schedule with $H_{\max}=n$, $\beta_{\max}=\lceil\log_2 n!\rceil$, $\Delta=2\beta_{\max}$, and temperatures $\lambda_i=e^{-\beta_i}$, $0\le i\le L$.
--
--   **Formalization Note** $L$ is the infimum of the indices reaching $\beta_{\max}$; the statements that use it assert that the schedule reaches $\beta_{\max}$. $\lceil\log_2 n!\rceil$ is `Nat.clog 2 n!`.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 50, p.55 (PDF 57); §9.1, p.54 (PDF 56); proof of Lemma 7, p.55 (PDF 57)

import Mathlib
import Definitions.Def_CubicPermFPRAS_matchWeight

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

/-- One step of the non-adaptive annealing schedule of Lemma 50, p.55 (PDF 57)
(arXiv:2609.20717, held version sha256 9e14f335…):
`d_i = min{β_max − β_i, ¼ · max{1/H_max, β_i/Δ}}`. -/
def annealStep (Hmax Δ βmax β : ℝ) : ℝ :=
  min (βmax - β) ((1 / 4) * max (1 / Hmax) (β / Δ))

/-- The inverse temperatures of Lemma 50: `β₀ = 0`, `β_{i+1} = β_i + d_i`. Once `β_i = β_max`
the step is `0`, so the sequence stays at `β_max`. -/
def annealBeta (Hmax Δ βmax : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => annealBeta Hmax Δ βmax i + annealStep Hmax Δ βmax (annealBeta Hmax Δ βmax i)

/-- The schedule length `L`: the first index with `β_L = β_max` ("until `β_L = β_max`",
Lemma 50). **Formalization Note.** This is `sInf` of the set of such indices; statements that
use it assert (or are given) that the schedule reaches `β_max`, so the empty-set value `0` is
never relied upon. -/
def annealLen (Hmax Δ βmax : ℝ) : ℕ :=
  sInf {i : ℕ | annealBeta Hmax Δ βmax i = βmax}

/-- `Z_S(β) = ∑_{M ∈ S} e^{−βH(M)}`, §9.1, p.54 (PDF 56). -/
def ZS {Ω : Type*} (H : Ω → ℝ) (S : Finset Ω) (β : ℝ) : ℝ :=
  ∑ M ∈ S, Real.exp (-β * H M)

/-- `z_S(β) = log Z_S(β)`, §9.1, p.54. -/
def zS {Ω : Type*} (H : Ω → ℝ) (S : Finset Ω) (β : ℝ) : ℝ :=
  Real.log (ZS H S β)

/-- `E[Y_i]` for `Y_i = e^{−d_i H(M_i)}`, `M_i ∼ µ_{S,β_i}` (`µ_{S,β} ∝ e^{−βH}` on `S`),
§9.1, p.54. -/
def annealMeanY {Ω : Type*} (H : Ω → ℝ) (S : Finset Ω) (Hmax Δ βmax : ℝ) (i : ℕ) : ℝ :=
  let β := annealBeta Hmax Δ βmax i
  let d := annealBeta Hmax Δ βmax (i + 1) - β
  ∑ M ∈ S, (Real.exp (-β * H M) / ZS H S β) * Real.exp (-d * H M)

/-- `E[Y_i²]` for `Y_i = e^{−d_i H(M_i)}`, `M_i ∼ µ_{S,β_i}`, §9.1, p.54. -/
def annealMeanY2 {Ω : Type*} (H : Ω → ℝ) (S : Finset Ω) (Hmax Δ βmax : ℝ) (i : ℕ) : ℝ :=
  let β := annealBeta Hmax Δ βmax i
  let d := annealBeta Hmax Δ βmax (i + 1) - β
  ∑ M ∈ S, (Real.exp (-β * H M) / ZS H S β) * Real.exp (-d * H M) ^ 2

/-- The relative second moment `E[Y²]/E[Y]²` of the product `Y = ∏_{i<L} Y_i` with independent
`M_i ∼ µ_{S,β_i}` (§9.1, p.54).

**Formalization Note.** By independence, `E[Y] = ∏_i E[Y_i]` and `E[Y²] = ∏_i E[Y_i²]`; the
definition is the ratio of these two finite products. -/
def annealRelSecondMoment {Ω : Type*} (H : Ω → ℝ) (S : Finset Ω) (Hmax Δ βmax : ℝ) : ℝ :=
  (∏ i ∈ Finset.range (annealLen Hmax Δ βmax), annealMeanY2 H S Hmax Δ βmax i) /
    (∏ i ∈ Finset.range (annealLen Hmax Δ βmax), annealMeanY H S Hmax Δ βmax i) ^ 2

/-- `β_max = ⌈log₂(n!)⌉` for the input (proof of Lemma 7, p.55). `Nat.clog 2 (n!)` is the least
`k` with `n! ≤ 2^k`, i.e. `⌈log₂ n!⌉`. -/
def coolBetaMax (n : ℕ) : ℝ := (Nat.clog 2 n.factorial : ℝ)

/-- The input cooling schedule's inverse temperatures (proof of Lemma 7, p.55): Lemma 50 with
`H_max = n`, `β_max = ⌈log₂ n!⌉`, `Δ = 2β_max`. -/
def coolBeta (n : ℕ) (i : ℕ) : ℝ := annealBeta n (2 * coolBetaMax n) (coolBetaMax n) i

/-- The length `L` of the input cooling schedule. -/
def coolLen (n : ℕ) : ℕ := annealLen n (2 * coolBetaMax n) (coolBetaMax n)

/-- The temperatures `λ_i = e^{−β_i}` of the cooling schedule Eq. (7), p.9 (PDF 11). -/
def coolLam (n : ℕ) (i : ℕ) : ℝ := Real.exp (-coolBeta n i)

end

end CubicPermFPRAS


