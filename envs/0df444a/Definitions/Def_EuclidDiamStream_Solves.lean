-- Prove2me | Definitions.Def_EuclidDiamStream_Solves
-- name    : EuclidDiamStream_Solves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:25.024644+00:00
-- url     : https://prove2.me/theorems/6910f061-3c03-4c2f-8eee-32087cff9226
-- title:
--   The $(r,c,n)$-diameter problem (Definition 2.1)
-- statement:
--   A randomized streaming algorithm $\mathcal A$ **solves the $(r,c,n)$-diameter problem** with error $\delta$ if, for every stream $\sigma$ with $v=\mathrm{freq}(\sigma)$ and $|\mathrm{supp}(v)|\le n$:
--   1. if $\mathrm{diam}(v)\le r$, then $\mathcal A(\sigma)$ outputs $0$ with probability at least $1-\delta$;
--   2. if $\mathrm{diam}(v)\ge cr$, then $\mathcal A(\sigma)$ outputs $1$ with probability at least $1-\delta$.
--
--   This is the hypothesis of the mission's main theorem.
--
--   **Formalization Note** "Every stream" means every strict-turnstile stream, with no bound on its length or on the magnitude of its frequencies. The source's $\delta$ is "a sufficiently small constant", so it is a parameter here.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), pp.6–7, Def. 2.1; footnote 6, p.6

import Mathlib
import Definitions.Def_EuclidDiamStream_diamGap
import Definitions.Def_EuclidDiamStream_StreamAlg

namespace EuclidDiamStream

/-- Definition 2.1 ((r,c,n)-diameter problem) of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), pp.6–7, with error
probability `δ`: on every stream `σ` with `v = freq(σ)` and `|supp(v)| ≤ n`, the algorithm outputs 0 with
probability at least `1 − δ` if `diam(v) ≤ r`, and 1 with probability at least `1 − δ` if `diam(v) ≥ cr`.

**Formalization Note.** "Any stream" is every strict-turnstile stream (footnote 6, p.6), with no bound on
its length or on the magnitude of its frequencies (pp.3–4). The source's `δ` is "a sufficiently small
constant", so it is a parameter here. -/
def StreamAlg.Solves {d Δ : ℕ} {R W : Type} [Fintype R] (A : StreamAlg (Point d Δ) R W)
    (r c : ℝ) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ σ : List (Point d Δ × Bool), BoolCSPDel.IsLegal σ → (supp (BoolCSPDel.freq σ)).card ≤ n →
    (diam (BoolCSPDel.freq σ) ≤ r →
      ENNReal.ofReal (1 - δ) ≤ A.μ.toOuterMeasure {ρ | A.out ρ (A.toTurnstileAlg.run ρ σ) = false}) ∧
    (c * r ≤ diam (BoolCSPDel.freq σ) →
      ENNReal.ofReal (1 - δ) ≤ A.μ.toOuterMeasure {ρ | A.out ρ (A.toTurnstileAlg.run ρ σ) = true})

end EuclidDiamStream


