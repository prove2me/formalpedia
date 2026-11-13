-- Prove2me | Definitions.Def_MultiThinkCoT_cotLossClass
-- name    : MultiThinkCoT_cotLossClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:00.844426+00:00
-- url     : https://prove2.me/theorems/2e6881a7-5475-4ffd-ab8b-c5b7c9d47f88
-- title:
--   The CoT loss class $\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F)$ over $\mathcal X\times\{0,1\}^T$
-- statement:
--   The **CoT loss class** of a base class $\mathcal F$ is the binary class over the domain $\mathcal X\times\{0,1\}^T$
--
--   $$
--   \mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F)=\big\{\ell_f:(x,z)\mapsto\mathbf 1\{z\neq f^{\mathrm{CoT}\text{-}T}(x)\}\ \big|\ f\in\mathcal F\big\}.
--   $$
--
--   Its VC dimension controls learning from CoTs of a single generator (Proposition 6.2) and the per-source budget of Algorithm 1 in the relaxed protocol (Theorem 7).
--
--   **Formalization Note** $\{0,1\}^T$ is the set of Boolean lists of length $T$; the indicator is the Boolean value of $z\neq f^{\mathrm{CoT}\text{-}T}(x)$.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §6.2, eq. (10), p.18 (PDF p.18)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# The CoT loss class `L^{CoT-T}(F)` (10)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), §6.2, eq. (10), p.18 (PDF p.18).

`L^{CoT-T}(F) = {ℓ_f : (x, z) ↦ 1{z ≠ f^{CoT-T}(x)} | f ∈ F}`, "a binary class over the domain
`X × {0,1}^T`".

**Formalization Note.** `{0,1}^T` is the subtype of `List Bool` of length `T`; the indicator
`1{z ≠ f^{CoT-T}(x)}` is the Boolean `decide (z ≠ cot f T x)`.
-/

/-- (10) The CoT loss class over `X × {0,1}^T`. -/
def cotLossClass (F : Set Gen) (T : ℕ) (X : Set (List Bool)) :
    Set (X × {z : List Bool // z.length = T} → Bool) :=
  {l | ∃ f ∈ F, ∀ q : X × {z : List Bool // z.length = T}, l q = decide (q.2.1 ≠ cot f T q.1.1)}

end MultiThinkCoT


