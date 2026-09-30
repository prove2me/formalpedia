-- Prove2me | Definitions.Def_CachingML_PredMarker_predError
-- name    : CachingML_PredMarker_predError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:45:05.080802+00:00
-- url     : https://prove2.me/theorems/c77796d2-5fcc-4ae6-8de4-c488bcc8ad47
-- title:
--   §2.2–2.3 — next-arrival labels and the error $\eta_\ell(h,\sigma)$ of a predictor
-- statement:
--   Let $\sigma = (z_1, \dots, z_n)$ be a sequence of requests for elements of a set $Z$, and let $h = (h_1, \dots, h_n)$ be real predictions, one per request. The **label** of the $i$-th request is the position of the next request of the same element,
--
--   $$y_i = \min\{t > i : z_t = z_i\}, \qquad y_i = n + 1 \text{ if } z_i \text{ is never requested again}.$$
--
--   Positions are $1$-based. For a loss function $\ell : \mathbb R \times \mathbb R \to \mathbb R_{\ge 0}$, the **error** of the predictions on $\sigma$ is
--
--   $$\eta_\ell(h, \sigma) = \sum_{i=1}^{n} \ell(y_i, h_i).$$
--
--   A predictor is $\epsilon$-accurate when this error is at most $\epsilon \cdot \mathrm{Opt}(\sigma)$ (Definition 2). The labels are completely determined by $\sigma$; the predictions are arbitrary reals.
--
--   **Formalization Note** The Lean sequence is a `List α`, indexed from $0$; the request with Lean index $j$ sits at position $j + 1$, so `nextArrival σ j` is the least $t + 1$ with $t > j$ and $z_{t+1} = z_{j+1}$, or `σ.length + 1`. The paper prints $x(\sigma_t) = x(\sigma_i)$ (equal *features*) in the definition of the label; the same paragraph states that features may change between requests of the same element, and the label is the next arrival of the element, which is what is formalized. The auxiliary `lossAt ℓ σ h j` is the loss $\ell(y_{j+1}, h_{j+1})$ of the request with Lean index $j$ (and $0$ for an invalid index).
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 7, §2.2 (definition of η_ℓ) and p. 9, §2.3 (labels y(σ_i))

import Mathlib

namespace CachingML.PredMarker

/-- The label of the request at 0-based index `i` of the request sequence `σ` (Lykouris–Vassilvitskii,
arXiv:1802.05399v4, §2.3, p. 9): the 1-based position of the next request of the *same element*,
i.e. the least 1-based position `t > i + 1` with `σ_t = σ_{i+1}`, or `σ.length + 1` if the element is
never requested again. The request at 0-based index `j` sits at 1-based position `j + 1`. -/
def nextArrival {α : Type*} [DecidableEq α] (σ : List α) (i : Fin σ.length) : ℕ :=
  (((List.finRange σ.length).filter (fun j => decide (i < j ∧ σ.get j = σ.get i))).head?.map
    (fun j => j.val + 1)).getD (σ.length + 1)

/-- The loss `ℓ(y_j, h_j)` of the prediction made at the request with 0-based index `j`
(`0` if `j` is not a valid index). -/
noncomputable def lossAt {α : Type*} [DecidableEq α] (ℓ : ℝ → ℝ → ℝ) (σ : List α)
    (h : Fin σ.length → ℝ) (j : ℕ) : ℝ :=
  if hj : j < σ.length then ℓ (nextArrival σ ⟨j, hj⟩) (h ⟨j, hj⟩) else 0

/-- The total error `η_ℓ(h, σ) = ∑_i ℓ(y(σ_i), h(σ_i))` of the predictions `h` (one real per request)
on the request sequence `σ` (§2.2, p. 7), with the labels `y` of `nextArrival`. -/
noncomputable def predError {α : Type*} [DecidableEq α] (ℓ : ℝ → ℝ → ℝ) (σ : List α)
    (h : Fin σ.length → ℝ) : ℝ :=
  ∑ i : Fin σ.length, ℓ (nextArrival σ i) (h i)

end CachingML.PredMarker


