-- Prove2me | Definitions.Def_OWFLocalDesc_HasBiasAtMost
-- name    : OWFLocalDesc_HasBiasAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:24.946024+00:00
-- url     : https://prove2.me/theorems/d81698de-1900-4bd1-8db7-7524880bd4fe
-- title:
--   Bias of a map into $\mathbb F_2^L$
-- statement:
--   A map $S:\{0,1\}^h\to\mathbb F_2^L$ has **bias at most** $\varepsilon$ on uniform inputs if
--   $$\Big|\,\mathbb E_{z\sim U_h}(-1)^{\langle v,S(z)\rangle}\Big|\le\varepsilon\qquad\text{for every nonzero } v\in\mathbb F_2^L,$$
--   where $\langle v,u\rangle=\sum_i v_iu_i$ in $\mathbb F_2$.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2`. The helper `vecBits` writes a vector of $\mathbb F_2^L$ as a bit string.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.3, p.17; Lemma 4.4, p.18

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Bias of a map into `𝔽₂^L`.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem 4.3, p.17 and
Lemma 4.4, p.18: `S : {0,1}^h → 𝔽₂^L` has bias at most `ε` on uniform inputs if
`|E_{z∼U_h} (−1)^{⟨v,S(z)⟩}| ≤ ε` for every nonzero `v ∈ 𝔽₂^L`.

**Formalization Note.** `𝔽₂ = ZMod 2`; `⟨v,u⟩` is `dotProduct v u` in `ZMod 2`; `(−1)^a` is
`1` for `a = 0` and `−1` for `a = 1`. -/
def HasBiasAtMost {h L : ℕ} (S : (Fin h → Bool) → (Fin L → ZMod 2)) (ε : ℝ) : Prop :=
  ∀ v : Fin L → ZMod 2, v ≠ 0 →
    |(∑ z : Fin h → Bool, (if dotProduct v (S z) = 0 then (1 : ℝ) else -1)) / (2 : ℝ) ^ h| ≤ ε

/-- The bit list of a vector of `𝔽₂^L`. -/
def vecBits {L : ℕ} (u : Fin L → ZMod 2) : List Bool := List.ofFn fun i => decide (u i = 1)

end OWFLocalDesc


