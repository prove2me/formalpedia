-- Prove2me | Definitions.Def_AMPUniversality_Polytope_Certificate
-- name    : AMPUniversality_Polytope_Certificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:40.907171+00:00
-- url     : https://prove2.me/theorems/ec4c6746-8179-4481-ac3f-ba4de2ae9304
-- title:
--   Lemma 5, p. 41 — ℓ¹ subgradients and restricted singular values
-- statement:
--   An $\ell^1$ subgradient at $x_0$ has coordinate $\operatorname{sign}(x_{0,i})$ on the support of $x_0$ and absolute value at most one everywhere. The near-saturation set is $S(c)=\{i:|v_i|\geq1-c\}$.
--
--   The restricted least singular value of $A_R$ is the infimum of $\|A_Rr\|_2$ over unit vectors $r$ on its column set $R$. The largest squared singular value is the supremum of $\|Ar\|_2^2$ over unit vectors $r$. These notions state the two spectral conditions of Lemma 5.
--
--   **Formalization Note** The empty-column infimum is $+\infty$; if $A_R$ is wide and has a unit kernel vector, its value is zero. The paper's printed indexing convention for $\sigma_{\min}$ would not give the lower bound on $\|A_Rr\|_2$ that Lemma 5 uses.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 40–41, Lemma 5 and preceding notation

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Recovery

set_option autoImplicit false
open Set
open scoped BigOperators

namespace AMPUniversality.Polytope

/-- The coordinate description of the subdifferential of the one-norm. -/
def IsL1Subgradient {n : ℕ} (x0 v : Fin n → ℝ) : Prop :=
  ∀ i, (x0 i ≠ 0 → v i = Real.sign (x0 i)) ∧ |v i| ≤ 1

/-- Coordinates at which a dual certificate is close to saturation. -/
noncomputable def nearSaturation {n : ℕ} (v : Fin n → ℝ) (c : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 1 - c ≤ |v i|)

/-- Squared Euclidean norm in a finite coordinate space. -/
noncomputable def euclideanNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- The least output norm on unit inputs supported on `R`. An empty
column set has value `⊤`; a wide matrix with a kernel has value zero. -/
noncomputable def sigmaMin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (R : Finset (Fin n)) : WithTop ℝ :=
  sInf {v : WithTop ℝ |
    ∃ r : R → ℝ,
      (∑ i, (r i) ^ 2) = 1 ∧
      v = (↑(Real.sqrt (∑ j : Fin m,
        (∑ i : R, A j i * r i) ^ 2)) : WithTop ℝ)}

/-- The square of the largest singular value, expressed as the maximal
squared output norm on unit inputs. -/
noncomputable def sigmaMaxSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {v : ℝ |
    ∃ r : Fin n → ℝ,
      euclideanNormSq r = 1 ∧
      v = euclideanNormSq (Matrix.mulVec A r)}

end AMPUniversality.Polytope


