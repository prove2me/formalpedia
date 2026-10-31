-- Prove2me | Definitions.Def_KashUpgrade_OLStep
-- name    : KashUpgrade_OLStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:56.834757+00:00
-- url     : https://prove2.me/theorems/7bb571b5-5b85-46cf-91db-5978be872945
-- title:
--   One iteration of OptimalLumping
-- statement:
--   One iteration of the loop of OptimalLumping, from a state $(\mathcal L,\gamma)$ with $S\ne\emptyset$:
--
--   1. choose $k^*$ among the maximizers of $\gamma^j_{j+k}$ over $S$;
--   2. add the constraint $\theta^j_{j+k^*}=\theta^j_{j+k^*+1}$ to $\mathcal L$;
--   3. for every $\iota$ in the new block $\mathcal L(j+k^*)$, set
--   $$
--   \gamma^j_\iota\leftarrow\frac{c\sum_{\ell\in\mathcal L(j+k^*)}A^j_\ell}{\sum_{\ell\in\mathcal L(j+k^*)}A^j_\ell(s_\ell-s_{\ell-1})} .
--   $$
--
--   **Formalization Note** The printed $\arg\max$ does not say which maximizer to take, and with some choices the printed loop repeats a state forever. One iteration is therefore a relation that allows any maximizer.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19

import Mathlib
import Definitions.Def_KashUpgrade_lumpBlock
import Definitions.Def_KashUpgrade_blockValue
import Definitions.Def_KashUpgrade_violators

namespace KashUpgrade

/-- **One iteration of the `while` loop of OptimalLumping.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19. From the state
`(L, γ)`: choose `k*` among the maximizers of `γ_{j+k}` over `S`, add the constraint
`θ_{j+k*} = θ_{j+k*+1}` to the lumping, and set `γ_ι ← c ∑A / ∑A Δ` over the new block `L(j + k*)`
for every `ι` in that block.

**Formalization Note** The printed `argmax` does not say which maximizer to take, and with some
choices the printed loop never stops. One step is therefore a relation that allows any maximizer.
-/
def OLStep (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ)
    (st st' : Finset ℕ × (ℕ → ℝ)) : Prop :=
  open Classical in
  ∃ k ∈ violators j n st.2,
    (∀ k₂ ∈ violators j n st.2, st.2 (j + k₂) ≤ st.2 (j + k)) ∧
    st'.1 = insert (j + k) st.1 ∧
    st'.2 = fun ι =>
      if ι ∈ lumpBlock j n st'.1 (j + k) then blockValue c s A (lumpBlock j n st'.1 (j + k))
      else st.2 ι

end KashUpgrade


