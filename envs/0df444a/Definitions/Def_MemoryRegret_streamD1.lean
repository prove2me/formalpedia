-- Prove2me | Definitions.Def_MemoryRegret_streamD1
-- name    : MemoryRegret_streamD1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:05.683103+00:00
-- url     : https://prove2.me/theorems/b5c186f2-bbb5-425b-88b5-c9cfff7b1225
-- title:
--   The stream laws $\mathcal D_0$, $\mathcal D_1$, the hybrids $\mathcal D^t$ and the joint law
-- statement:
--   Fix a distribution $\mu$ on a finite set $X$, a finite nonempty class $(\mathrm{hyp}_i)_{i\in\iota}$ and $\varepsilon$. One stream element is a pair $(x,b)\in X\times\{0,1\}^m$.
--
--   1. **No case.** $D_0(x,b)=\mu(x)\,\mathrm{blockLabelLaw}_\varepsilon(b)$: draw $x\sim\mu$ and a fair bit, then the labels i.i.d. $\mathrm{Ber}(\text{bit},\frac12+\varepsilon)$. $\mathcal D_0=D_0^{T_{\mathrm{block}}}$.
--   2. **Fixed hypothesis.** $D_h(x,b)=\mu(x)\,\mathrm{berBlock}_\varepsilon(h(x),b)$.
--   3. **Yes case.** $\mathcal D_1=\mathbb E_{i\in_R\iota}D_{\mathrm{hyp}_i}^{T_{\mathrm{block}}}$: one hidden hypothesis is drawn once, for the whole stream.
--   4. **Hybrids.** $\mathcal D^t$ draws $i$ uniformly, then the first $t$ elements from $D_{\mathrm{hyp}_i}$ and the rest from $D_0$; thus $\mathcal D^0=\mathcal D_0$ and $\mathcal D^{T_{\mathrm{block}}}=\mathcal D_1$.
--   5. **Joint law.** The law of $(i,\text{stream})$ in the learning problem of Proposition 5: $i$ uniform, then $\tau$ i.i.d. samples from $D_{\mathrm{hyp}_i}$.
--
--   **Formalization Note** The class is an indexed family and "$h\in_R H$" is uniform on the index type $\iota$; for $\iota=H$ this is the paper's law. Streams are functions on $\mathrm{Fin}\,T_{\mathrm{block}}$ (0-based time) and all laws are explicit finite real weights.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Definition 3, p.9; §3.2, p.12; Proposition 5, pp.9–10

import Mathlib
import Definitions.Def_MemoryRegret_berBlock

namespace MemoryRegret

variable {X ι : Type} [Fintype X] [Fintype ι] {m : ℕ}

/-- The NO-case law of one stream element `(x, b)`: `x ∼ µ`, a fair bit `b ∈_R {0,1}`, and
`b^{(i)} ∼ Ber(b, ½ + ε)` i.i.d. (Definition 3, p.9). -/
noncomputable def elemD0 (μ : X → ℝ) (ε : ℝ) (a : X × (Fin m → Bool)) : ℝ :=
  μ a.1 * blockLabelLaw ε a.2

/-- `D_h`: the law of one stream element for a fixed hypothesis `h`: `x ∼ µ` and
`b^{(i)} ∼ Ber(h(x), ½ + ε)` i.i.d. (Definition 3, p.9). -/
noncomputable def elemDh (μ : X → ℝ) (ε : ℝ) (h : X → Bool) (a : X × (Fin m → Bool)) : ℝ :=
  μ a.1 * berBlock ε (h a.1) a.2

/-- `𝒟_0 = D_0^{T_block}`: `T_block` i.i.d. NO-case elements (Definition 3, p.9; §3.2, p.12). -/
noncomputable def streamD0 {Tb : ℕ} (μ : X → ℝ) (ε : ℝ) (s : Fin Tb → X × (Fin m → Bool)) : ℝ :=
  ∏ t, elemD0 μ ε (s t)

/-- **The YES-case law `𝒟_1` of Definition 3, together with `𝒟_0` and the hybrids `𝒟^t`.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Definition 3, p.9: "(Yes case: D_1) Sample a hypothesis h ∈_R H. At every time-step t, the
element (x_t, b_t = (b_t^{(1)}, …, b_t^{(m)})) is sampled as follows: x_t ∼ µ and for all
i ∈ [m], b_t^{(i)} ∼ Ber(h(x_t), 1/2 + ε)"; §3.2, p.12: "𝒟_1 … is E_{h∈_R H} D_h^{T_block}".

`streamD1 μ hyp ε s = |ι|⁻¹ ∑_i ∏_t D_{hyp i}(s_t)` is the probability of the stream
`s = ((x_1, b_1), …, (x_{T_block}, b_{T_block}))` when the hidden hypothesis index `i` is
uniform on `ι` and the elements are then i.i.d. `D_{hyp i}`.

**Formalization Note.** The class is an indexed family `hyp : ι → X → Bool` and "h ∈_R H" is
the uniform distribution on the index type `ι`; for an injective family (`ι = H`) this is the
paper's law. Streams are `Fin T_block → X × (Fin m → Bool)` (0-based time). All laws are
explicit real weights on a finite type; they are probability vectors when `µ` is one and
`ε ∈ [−½, ½]`. -/
noncomputable def streamD1 {Tb : ℕ} (μ : X → ℝ) (hyp : ι → X → Bool) (ε : ℝ)
    (s : Fin Tb → X × (Fin m → Bool)) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∏ t, elemDh μ ε (hyp i) (s t)

/-- The hybrid `𝒟^k` (§3.2, p.12): `h ∈_R H`, the first `k` elements from `D_h` and the rest
from `D_0`. Elements are 0-based, so element `t` comes from `D_h` iff `t < k`; `𝒟^0 = 𝒟_0` and
`𝒟^{T_block} = 𝒟_1`. -/
noncomputable def hybridD {Tb : ℕ} (μ : X → ℝ) (hyp : ι → X → Bool) (ε : ℝ) (k : ℕ)
    (s : Fin Tb → X × (Fin m → Bool)) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∏ t : Fin Tb, if (t : ℕ) < k then elemDh μ ε (hyp i) (s t) else elemD0 μ ε (s t)

/-- The joint law of the hidden hypothesis index and the samples in the learning problem of
Proposition 5 (p.9) and §3.3 (p.17): `i` uniform on `ι`, then `τ` i.i.d. samples from
`D_{hyp i}`. -/
noncomputable def jointLaw {τ : ℕ} (μ : X → ℝ) (hyp : ι → X → Bool) (ε : ℝ)
    (p : ι × (Fin τ → X × (Fin m → Bool))) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∏ t, elemDh μ ε (hyp p.1) (p.2 t)

end MemoryRegret


