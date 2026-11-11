-- Prove2me | Definitions.Def_PreservePast_IsSuccess
-- name    : PreservePast_IsSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:40:34.638121+00:00
-- url     : https://prove2.me/theorems/6cc6f69a-e1a2-4dbb-bf4e-5002d0040b96
-- title:
--   Successful response (14)
-- statement:
--   For a history $h=(h_1,\dots,h_K)$ and a query $(x,p)$, an update $H\in\mathbb R^{m\times n}$ is **successful** (for rank $r$, radius $R$, fit tolerance $\xi$ and accuracy $\epsilon$) when
--   $$
--   \operatorname{rank}H\le r,\qquad \|H\|_F\le R,\qquad \tfrac12\|Hx-p\|^2\le\xi,\qquad \max_{i\le K}f_i(H)\le\epsilon .
--   $$
--   With $\xi=0$ the fit is exact, $Hx=p$.
--
--   **Formalization Note** $\max_{i\le K}f_i(H)\le\epsilon$ is written as $f_i(H)\le\epsilon$ for every $i$. $\|\cdot\|_F$ is the published `LowRankMEG.frobNorm`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (14)

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_PreservePast_Task

open Matrix

namespace PreservePast

/-- **Successful response** (14). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8): the decoder must "return an update of
rank at most r and Frobenius norm at most R satisfying ½‖Hx − p‖² ≤ ξ, max_{i≤K} f_i(H) ≤ ϵ (14)."

`IsSuccess r R ξ ε h x p H` says that the update `H` has rank at most `r`, Frobenius norm at most
`R`, fit error `½‖Hx − p‖² ≤ ξ`, and loss increment at most `ε` on every old task of `h`.

**Formalization Note.** `max_{i≤K} f_i(H) ≤ ϵ` is written `∀ i, f_i(H) ≤ ε`; squared Euclidean
norms are sums of squares. -/
def IsSuccess {m n K : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (r : ℕ) (R ξ ε : ℝ)
    (h : Fin K → Task W₀) (x : Fin n → ℝ) (p : Fin m → ℝ) (H : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  H.rank ≤ r ∧ LowRankMEG.frobNorm H ≤ R ∧ (1 / 2) * ∑ j, (H *ᵥ x - p) j ^ 2 ≤ ξ ∧
    ∀ i, (h i).lossInc H ≤ ε

end PreservePast


