-- Prove2me | Definitions.Def_QNoiseStab_noiseKernel
-- name    : QNoiseStab_noiseKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:51.264999+00:00
-- url     : https://prove2.me/theorems/48c1ae7f-28a2-4a4a-ba5e-441bd34b240f
-- title:
--   Law of the restricted noise $N_p^A(x)$ on $X^n$
-- statement:
--   Let $X$ be a finite set, $A\subseteq[n]$, $p\in\mathbb R$ and $x,y\in X^n$. The restricted noise $N_p^A(x)$ applies the single-coordinate noise $N_p$ independently to each coordinate $x_i$ with $i\in A$ and leaves the other coordinates unchanged. Its law is
--
--   $$
--   \Pr[N_p^A(x)=y]=\prod_{i\in A}\Bigl(\frac{p}{|X|}+(1-p)\,\delta_{x_i,y_i}\Bigr)\ \prod_{i\notin A}\delta_{x_i,y_i}.
--   $$
--
--   With $A=[n]$ this is the law of $N_p(x)=\bigotimes_i N_p(x_i)$.
--
--   **Formalization Note** The random variable is represented by its law, the product of the independent coordinate laws; the closed form of Proposition 3.2 is a theorem, not the definition. Coordinates are $0$-based.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, pp.11–12 (N_p(x) by independent coordinates, p.11; N_p^A(x), p.12)

import Mathlib
import Definitions.Def_QNoiseStab_coordNoise

namespace QNoiseStab

/-- The law of the restricted noise `N_p^A(x)` on `Xⁿ` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, pp.11–12: "Np(x) is defined by
applying Np(xi) at every index independently", and "for any A ⊆ [n] … we can define random
variable N^A_p(x) by applying the noise operator to x on the coordinates in A and leaving other
coordinates unchanged"): `noiseKernel p A x y = Pr[N_p^A(x) = y]`, the product over coordinates of
`Pr[N_p(x_i) = y_i]` for `i ∈ A` and of the Kronecker delta `[x_i = y_i]` for `i ∉ A`.

**Formalization Note** The random variable is represented by its law, the product of the
independent coordinate laws. Coordinates are `Fin n` (0-based). -/
noncomputable def noiseKernel {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (p : ℝ)
    (A : Finset (Fin n)) (x y : Fin n → X) : ℝ :=
  ∏ i, if i ∈ A then coordNoise p (x i) (y i) else (if x i = y i then 1 else 0)

end QNoiseStab


