-- Prove2me | Definitions.Def_RandomQueryXOR_infoCost
-- name    : RandomQueryXOR_infoCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:04:30.639294+00:00
-- url     : https://prove2.me/theorems/76c99f6a-99d2-4724-9081-7eb55ed4b6d0
-- title:
--   Information cost $\mathrm{IC}_\mu(P)=\sum_{i}\sum_{j\le i} I(P_i;b_j\mid P_{j-1},y,L,R_{\rm pub})$
-- statement:
--   Let $P$ be a randomized branching program of width $W$ and length $T$ in the gate-keeper model and $\mu$ a distribution on inputs $y$. Draw the deterministic program $R_{\rm pub}$ from $P$, the input $y\sim\mu$, the index sequence $L=(\ell_1,\dots,\ell_T)$ uniformly and the gate bits $b_1,\dots,b_T$ uniformly, all independently, and let $P_t$ be the node reached after the first $t$ samples $(\ell_s,b_s,w_{\ell}(s))$. The **information cost** is
--   $$
--   \mathrm{IC}_\mu(P)=\sum_{i\in[T]}\ \sum_{j\le i} I\bigl(P_i\,;\,b_j\ \big|\ P_{j-1},\,y,\,L,\,R_{\rm pub}\bigr).
--   $$
--   It measures how much the memory states reveal about whether earlier samples carried their value. Claim 4.4 bounds it by $TS$ for width $2^S$; Lemma 4.16 bounds the information of the two-bit game by it.
--
--   **Formalization Note** 0-based times: for $0\le j\le i<T$ the term is $I(P_{i+1};b_j\mid P_j,y,L,R_{\rm pub})$, which is the paper's term for the pair $(i+1,j+1)$. Lean returns $0$ when the index set is empty.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §4.1, p.17 (PDF p.19), boxed definition; notation p.16 (PDF p.18)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_RandomQueryXOR_cmi

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

/-- The probability space of the information cost: the deterministic program `R_pub = P`, the
input `y`, the index sequence `L = (ℓ_1, …, ℓ_T)` and the gate bits `(b_1, …, b_T)`. -/
abbrev ICSpace (W T : ℕ) (ι : Type) :=
  DetBP W (GateSample ι) T × (ι → Bool) × (Fin T → ι) × (Fin T → Bool)

/-- The joint law of `(R_pub, y, L, b)`: the program `P ∼ μP`, the input `y ∼ μ`, the indices
uniform on `ι` and the gate bits uniform on `{0, 1}`, all independent. -/
noncomputable def icLaw {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μP : FinDist (DetBP W (GateSample ι) T)) (μ : FinDist (ι → Bool)) :
    FinDist (ICSpace W T ι) :=
  μP.prod (μ.prod ((uniformDist (Fin T → ι)).prod (uniformDist (Fin T → Bool))))

/-- `P_t`: the label of the node reached after processing the first `t` gate-keeper samples
`(ℓ_s, b_s, w_{ℓ}(s))` (arXiv:2611.04353, p.16 = PDF p.18). -/
def icState {W T : ℕ} {ι : Type} (t : ℕ) (ω : ICSpace W T ι) : Fin W :=
  ω.1.stateAt (fun s => gateSample ω.2.1 (ω.2.2.1 s) (ω.2.2.2 s)) t

/-- The information cost of a randomized gate-keeper branching program `P` (law `μP`) under an
input distribution `µ` (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random
Query Model*, arXiv:2611.04353, p.17 = PDF p.19, boxed):
`IC_µ(P) = ∑_{i ∈ [T]} ∑_{j ≤ i} I(P_i ; b_j | P_{j−1}, y, L, R_pub)`, where `y ∼ µ`, `P_t` is
the label reached after the first `t` samples, `b_j` the gate bit of the `j`-th sample, `L` the
whole index sequence and `R_pub` the deterministic program drawn from `P`.

**Formalization Note** 0-based: for `i j : Fin T` with `j ≤ i` the term is
`I(P_{i+1} ; b_j | P_j, y, L, R_pub)` with `b_j` the gate bit of the sample at time `j`
(the paper's `b_{j+1}`) and `P_j` the label before it (the paper's `P_{(j+1)−1}`), so the sum
covers exactly the paper's pairs `1 ≤ j ≤ i ≤ T`. `R_pub` is the drawn deterministic program.
The indices and gate bits are independent of `P` and `y`. Junk value `0` when `ι` is empty
(the paper has `n ≥ 1`). -/
noncomputable def infoCost {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (μP : FinDist (DetBP W (GateSample ι) T)) (μ : FinDist (ι → Bool)) : ℝ :=
  if h : Fintype.card ι = 0 then 0 else
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
    ∑ i : Fin T, ∑ j ∈ Finset.univ.filter (fun j : Fin T => j ≤ i),
      cmi (icLaw μP μ) (icState (i.val + 1)) (fun ω : ICSpace W T ι => ω.2.2.2 j)
        (fun ω : ICSpace W T ι => (icState j.val ω, ω.2.1, ω.2.2.1, ω.1))

end RandomQueryXOR


