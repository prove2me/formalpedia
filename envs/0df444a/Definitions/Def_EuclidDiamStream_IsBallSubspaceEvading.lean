-- Prove2me | Definitions.Def_EuclidDiamStream_IsBallSubspaceEvading
-- name    : EuclidDiamStream_IsBallSubspaceEvading
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:00.571988+00:00
-- url     : https://prove2.me/theorems/612e87b1-99f5-444b-bf59-3ec4e6d8c41d
-- title:
--   $(\delta,\tau)$-ball-subspace-evading functions (Definition 3.2)
-- statement:
--   A function $f:\{0,1\}^d\to\mathbb R^s$ is **$(\delta,\tau)$-ball-subspace-evading** if
--   $$\Pr_{x,y\sim\{0,1\}^d}\big[f(y)\notin\mathrm{Span}_f(\mathcal B(x,\tau))\big]\ge1-\delta,$$
--   where $\mathrm{Span}_f(\mathcal B(x,\tau))\subseteq\mathbb R^s$ is the subspace spanned by the vectors $f(z)$, $z\in\mathcal B(x,\tau)$.
--
--   The property is the linear-algebraic core of the lower bound: good sketches produce such functions, and such functions need high dimension.
--
--   **Formalization Note** The uniform probability over pairs is written as a count of pairs.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8, Def. 3.2

import Mathlib
import Definitions.Def_EuclidDiamStream_hamBall

namespace EuclidDiamStream

open Classical in
/-- Definition 3.2 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8: `f : {0,1}^d → ℝ^s` is `(δ,τ)`-ball-subspace-evading if
`Pr_{x,y∼{0,1}^d}[f(y) ∉ Span_f(B(x,τ))] ≥ 1 − δ`, where `Span_f(B(x,τ))` is the span of
`{f(z) : z ∈ B(x,τ)}`.

**Formalization Note.** The uniform probability over pairs is written as a count: at least `(1 − δ) · 4^d`
of the `4^d` pairs `(x,y)` satisfy the condition. -/
def IsBallSubspaceEvading {d s : ℕ} (δ : ℝ) (τ : ℕ) (f : Cube d → (Fin s → ℝ)) : Prop :=
  (1 - δ) * 4 ^ d ≤
    (((Finset.univ : Finset (Cube d × Cube d)).filter
      (fun p => f p.2 ∉ Submodule.span ℝ (f '' (↑(hamBall p.1 τ) : Set (Cube d))))).card : ℝ)

end EuclidDiamStream


