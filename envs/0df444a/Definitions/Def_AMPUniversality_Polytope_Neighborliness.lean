-- Prove2me | Definitions.Def_AMPUniversality_Polytope_Neighborliness
-- name    : AMPUniversality_Polytope_Neighborliness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:57.485217+00:00
-- url     : https://prove2.me/theorems/ac06ce90-2f40-405e-b044-351183701361
-- title:
--   Definition 1, pp. 3–4 — projected cross-polytopes and weak neighborliness in probability
-- statement:
--   Let $C_n=\{x\in\mathbb R^n:\sum_i|x_i|\leq1\}$ be the cross-polytope, and let $AC_n$ be its image under an $m\times n$ real matrix $A$. For a polytope $Q$, write $F(Q;\ell)$ for its number of nonempty faces of dimension $\lfloor\ell\rfloor$.
--
--   A random sequence $Q_n\subseteq\mathbb R^{m(n)}$ has weak neighborliness $\rho\in(0,1)$ in probability when the lower face-count ratio converges to one for $0<\xi\leq1$, and the upper ratio converges to zero for every $\xi>0$:
--
--   $$\frac{F(Q_n;m(n)\rho(1-\xi))}{F(C_n;m(n)\rho(1-\xi))}\to1,\qquad\frac{F(Q_n;m(n)\rho(1+\xi))}{F(C_n;m(n)\rho(1+\xi))}\to0.$$
--
--   This is the geometric property asserted by Theorem 2. Face counts reuse the published nonempty exposed-face definition. The lower ratio is restricted to nonnegative requested dimensions because the printed quotient is undefined for $\xi>1$; a negative requested dimension has zero nonempty faces. The condition that the intended polytope class is centrosymmetric with $2n$ vertices is treated as a description of that class rather than an additional limit condition.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 3–4, Definition 1 and notation preceding it

import Mathlib
import Definitions.Def_Grunbaum2003_faceCount

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators

namespace AMPUniversality.Polytope

/-- The unit ball of the one-norm in real coordinate space. -/
def crossPolytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i, |x i| ≤ 1}

/-- The image of a cross-polytope under a rectangular matrix. -/
def projPolytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  (fun x => Matrix.mulVec A x) '' crossPolytope n

/-- The number of nonempty exposed faces of dimension `⌊ell⌋`. -/
noncomputable def faceNumber {d : ℕ} (Q : Set (Fin d → ℝ)) (ell : ℝ) : ℝ :=
  if ell < 0 then 0 else (Grunbaum2003.faceCount Q ⌊ell⌋₊ : ℝ)

/-- The two face-ratio limits in Definition 1, interpreted in probability.
The lower-face quotient is evaluated only where its requested dimension is
nonnegative; for `ξ > 1` both counts in the printed quotient are zero. -/
def HasWeakNeighborlinessInProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ → ℕ)
    (Q : ∀ n, Ω → Set (Fin (m n) → ℝ)) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 ∧
    ∀ ξ : ℝ, 0 < ξ →
      (ξ ≤ 1 → TendstoInMeasure P
        (fun n ω => faceNumber (Q n ω) ((m n : ℝ) * ρ * (1 - ξ)) /
          faceNumber (crossPolytope n) ((m n : ℝ) * ρ * (1 - ξ)))
        atTop (fun _ => (1 : ℝ))) ∧
      TendstoInMeasure P
        (fun n ω => faceNumber (Q n ω) ((m n : ℝ) * ρ * (1 + ξ)) /
          faceNumber (crossPolytope n) ((m n : ℝ) * ρ * (1 + ξ)))
        atTop (fun _ => (0 : ℝ))

end AMPUniversality.Polytope


