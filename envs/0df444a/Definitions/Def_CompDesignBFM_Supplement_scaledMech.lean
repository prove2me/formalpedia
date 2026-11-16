-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_scaledMech
-- name    : CompDesignBFM_Supplement_scaledMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:04:48.01057+00:00
-- url     : https://prove2.me/theorems/ecd36606-10cb-42aa-8f30-53794dd258ad
-- title:
--   The scaled marginal contribution mechanism (Mechanism C.1)
-- statement:
--   Let $v$ be a value function, $B,\beta>0$, and fix a total order on $2^N$ in which $\emptyset$ comes first. At bids $b$, **Mechanism C.1** selects
--
--   $$S^{(\beta)}(b)\in\arg\max_{S\subseteq N}\ \Phi^{(\beta)}_b(S),\qquad \Phi^{(\beta)}_b(S)=v(S)\prod_{i\in S}\Bigl(1-\frac{\beta b_i}{B}\Bigr)^+,$$
--
--   ties broken by the order, and pays each selected agent $i$
--
--   $$p_i=\frac B\beta\left(1-\frac{\Phi^{(\beta)}_{i,\mathrm{out}}(b_{-i})}{\Phi^{(\beta)}_{i,\mathrm{in}}(b_{-i})}\right),$$
--
--   where $\Phi^{(\beta)}_{i,\mathrm{in}}(b_{-i})=\max_{T\ni i}v(T)\prod_{i'\in T\setminus\{i\}}(1-\beta b_{i'}/B)^+$ and $\Phi^{(\beta)}_{i,\mathrm{out}}(b_{-i})=\max_{T\not\ni i}v(T)\prod_{i'\in T}(1-\beta b_{i'}/B)^+$. Unselected agents are paid zero.
--
--   **Formalization Note** The selected set is the base mission's `Amc v (B / β) r b` for a rank $r$ encoding the order: its potential at budget $B/\beta$ is $\Phi^{(\beta)}_b$ since $b_i/(B/\beta)=\beta b_i/B$. Both maxima are over finite nonempty families of sets.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Mechanism C.1, p.46 (PDF 48)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_Amc

namespace CompDesignBFM

namespace Supplement

/-- The scaled marginal contribution mechanism (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Mechanism C.1, p.46, PDF 48). At bids `b` it
selects `S^(β)(b)`, the global maximizer of `Φ^(β)_b(S) = v(S) ∏_(i ∈ S) (1 − β bᵢ/B)₊` with ties
broken by the fixed order `r` (`∅` first), and pays each selected `i`
`(B/β) (1 − Φ^(β)_(i,out)(b₋ᵢ) / Φ^(β)_(i,in)(b₋ᵢ))`, where
`Φ^(β)_(i,in)(b₋ᵢ) = max_(T ∋ i) v(T) ∏_(i' ∈ T ∖ {i}) (1 − β b_(i')/B)₊` and
`Φ^(β)_(i,out)(b₋ᵢ) = max_(T ∌ i) v(T) ∏_(i' ∈ T) (1 − β b_(i')/B)₊`; unselected agents are paid zero.
**Formalization Note.** `S^(β)(b)` is the base mission's `Amc v (B / β) r b`: its potential
`pot v (B / β) b S = v S ∏ max (1 − bᵢ/(B/β)) 0` is `Φ^(β)_b(S)` because `bᵢ/(B/β) = β bᵢ/B` for
`B, β > 0`. Both maxima range over finite nonempty families (`{i}` contains `i`; `∅` does not), written
`Finset.sup'`. The payment is Mechanism C.1's formula, not a supremum of thresholds. -/
noncomputable def scaledMech {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (r : Finset (Fin n) → ℕ) :
    Mechanism n where
  alloc := fun b => Amc v (B / β) r b
  pay := fun b i =>
    if i ∈ Amc v (B / β) r b then
      B / β * (1 -
        (Finset.univ.filter fun T : Finset (Fin n) => i ∉ T).sup' ⟨∅, by simp⟩
            (fun T => v T * ∏ i' ∈ T, max (1 - β * b i' / B) 0) /
        (Finset.univ.filter fun T : Finset (Fin n) => i ∈ T).sup' ⟨{i}, by simp⟩
            (fun T => v T * ∏ i' ∈ T.erase i, max (1 - β * b i' / B) 0))
    else 0

end Supplement

end CompDesignBFM


