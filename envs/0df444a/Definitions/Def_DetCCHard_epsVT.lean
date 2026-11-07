-- Prove2me | Definitions.Def_DetCCHard_epsVT
-- name    : DetCCHard_epsVT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:00.689959+00:00
-- url     : https://prove2.me/theorems/d9be387a-ff69-4217-8b9b-c94bbe9d98f3
-- title:
--   Error $\varepsilon(v,\tau)$, exceptional count $e(v,\tau)$ and marginals
-- statement:
--   For $0 < v, \tau \le 1$ set
--   $$
--   \varepsilon(v, \tau) := \min\{\tau,\ 2^{-30} v^{1/256}\}, \qquad e(v, \tau) := 8 \left\lceil 2^{20}\, \varepsilon(v, \tau)^{-2}\, v^{-1/512} \right\rceil .
--   $$
--   For weights $\nu$ on labels with decoder $z$, an event $Y$ of labels and a coordinate set $J$, the **conditional marginal** $(\nu \mid Y)_J$ gives $a \in Z^J$ the weight $(\nu \mid Y)(\{\ell : z(\ell)_J = a\})$, and the **product weights** $\mu_J$ give $a$ the weight $\prod_{j \in J} \mu(a_j)$.
--
--   $\varepsilon$ bounds the total variation distance after conditioning and $e$ bounds the number of exceptional coordinates in Lemma 6.10; both reappear in Theorem 6.12, Lemma C.3 and Theorem 7.2.
--
--   **Formalization Note** $v^{1/256}$ and $v^{-1/512}$ are real powers, $\varepsilon^{-2}$ is division by $\varepsilon^2$, and the ceiling is the natural-number ceiling, so $e(v,\tau) \in \mathbb N$. The verification file checks $e(1,1) = 2^{83}$.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), §6.4, p.26 (display before Lemma 6.10)

import Mathlib
import Definitions.Def_DetCCHard_IsWeight

namespace DetCCHard

/-- The **conditioning error** `ε(v, τ) := min{τ, 2^{-30} v^{1/256}}` (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, §6.4, p.26, display before Lemma 6.10). -/
noncomputable def epsVT (v τ : ℝ) : ℝ :=
  min τ ((2 : ℝ) ^ (-30 : ℤ) * v ^ ((1 : ℝ) / 256))

/-- The **number of exceptional coordinates** `e(v, τ) := 8 ⌈2^{20} ε(v, τ)^{-2} v^{-1/512}⌉`
(§6.4, p.26, display before Lemma 6.10); `e(v) := e(v, 1)`.

**Formalization Note** `ε^{-2}` is written as division by `ε²`, and `v^{-1/512}` is the real power
`Real.rpow`; the ceiling is `Nat.ceil`, so `e(v, τ)` is a natural number. -/
noncomputable def eVT (v τ : ℝ) : ℕ :=
  8 * ⌈(2 : ℝ) ^ (20 : ℕ) / (epsVT v τ) ^ 2 * v ^ (-(1 : ℝ) / 512)⌉₊

/-- The **conditional marginal** `(ν | Y)_J` (§4.2, p.14 and Lemma 6.10, p.26): for weights `ν` on
labels, a decoder `z`, an event `Y` of labels and a coordinate set `J`, the weight that `ν`
conditioned on `Y` gives to the labels whose decoded tuple restricts to `a` on `J`. -/
noncomputable def condMarginal {L Z ι : Type} [Fintype L] (ν : L → ℚ) (z : L → ι → Z)
    (Y : Set L) (J : Finset ι) : (J → Z) → ℝ :=
  fun a => (condWt ν Y {ℓ | ∀ j : J, z ℓ j = a j} : ℝ)

/-- The **product weights** `μ_J` on `Z^J` (§4.2, p.14): `μ_J(a) = ∏_{j ∈ J} μ(a_j)`. -/
noncomputable def prodMarginal {Z ι : Type} (μ : Z → ℚ) (J : Finset ι) : (J → Z) → ℝ :=
  fun a => ∏ j : J, (μ (a j) : ℝ)

end DetCCHard


