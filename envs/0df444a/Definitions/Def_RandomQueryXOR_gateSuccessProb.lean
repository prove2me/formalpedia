-- Prove2me | Definitions.Def_RandomQueryXOR_gateSuccessProb
-- name    : RandomQueryXOR_gateSuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:52.782612+00:00
-- url     : https://prove2.me/theorems/099e44f7-a8d2-465c-8ad5-6c64da61e354
-- title:
--   Success probability in the gate-keeper input model $(i, b, w(i))$
-- statement:
--   In the **gate-keeper model** each sample is a triple $(i,b,w(i))$: the index $i$ is uniform on the index set, the bit $b$ is uniform on $\{0,1\}$ and independent of $i$, and
--   $$
--   w(i)=\begin{cases}x(i)&\text{if } b=1,\\ \bot&\text{if } b=0.\end{cases}
--   $$
--   For a randomized branching program $\mu$ over this sample alphabet, a program $P\sim\mu$ runs on $T$ independent such samples, independent of $P$; its **probability of success** on input $x$ for $F$ is $\Pr[P(x)=F(x)]$.
--
--   Claim 4.1 shows that this model costs only constant factors in length and width, and it lets the analysis measure what the memory reveals about the gate bits $b_j$.
--
--   **Formalization Note** $\bot$ is `none`. `gateOutProb μ x b` is $\Pr[P(x)=b]$; junk value $0$ if the index set is empty and $T\ge1$.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §4.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_DetBP

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- The sample alphabet of the gate-keeper model: triples `(i, b, w(i))` with `w(i) ∈ {0, 1, ⊥}`
(`none` = ⊥). -/
abbrev GateSample (ι : Type) := ι × Bool × Option Bool

/-- The gate-keeper sample `(i, b, w(i))` of input `x`: `w(i) = x(i)` if `b = 1` and `⊥`
otherwise (arXiv:2611.04353, §4.1, p.15 = PDF p.17). -/
def gateSample {ι : Type} (x : ι → Bool) (i : ι) (b : Bool) : GateSample ι :=
  (i, b, if b then some (x i) else none)

/-- `Pr[P(x) = b]` for a randomized branching program `μ` in the gate-keeper model on input
`x`: `P ∼ μ`, the indices `i_1, …, i_T` uniform on `ι` and the gate bits `b_1, …, b_T` uniform
on `{0, 1}`, all independent, and `P` runs on the samples `(i_t, b_t, w(i_t))`.

**Formalization Note** Junk value `0` if `ι` is empty and `T ≥ 1` (no index sequence). -/
noncomputable def gateOutProb {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinDist (DetBP W (GateSample ι) T)) (x : ι → Bool) (b : Bool) : ℝ :=
  ∑ P, ∑ i : Fin T → ι, ∑ c : Fin T → Bool,
    μ.prob P * (Fintype.card (Fin T → ι) : ℝ)⁻¹ * (Fintype.card (Fin T → Bool) : ℝ)⁻¹ *
      (if P.output (fun t => gateSample x (i t) (c t)) = b then 1 else 0)

/-- The success probability on input `x` of a randomized branching program `μ` computing
`F` in the gate-keeper input model (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the
Random Query Model*, arXiv:2611.04353, §4.1, p.15 = PDF p.17): "the branching program is given
as input (i, b, w(i)) where: The index i ∈ [n] is chosen uniformly at random from [n]. The bit
b ∈ {0, 1} is chosen uniformly at random independent of i. The value w(i) is equal to x(i) if
b = 1 and ⊥ otherwise."

**Formalization Note** As in the random query model, a randomized program is a distribution on
deterministic layered programs, here `DetBP W (GateSample ι) T`; all samples are independent of
the program. -/
noncomputable def gateSuccessProb {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinDist (DetBP W (GateSample ι) T)) (F : (ι → Bool) → Bool) (x : ι → Bool) : ℝ :=
  gateOutProb μ x (F x)

end RandomQueryXOR


