-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_thetaBody
-- name    : ConeLifts_Factorization_Supplement_thetaBody
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:47:19.177477+00:00
-- url     : https://prove2.me/theorems/2a5e6442-5104-4684-9cd7-7c7f349a9a2f
-- title:
--   Sums of squares modulo an ideal and theta bodies $\mathrm{TH}_k(I)$
-- statement:
--   Let $I \subseteq \mathbb R[x_1, \dots, x_n]$ be an ideal. A polynomial $q$ is a **sum of squares modulo $I$** if there are polynomials $h_1, \dots, h_s$ with
--
--   $$
--   q - \sum_{i=1}^s h_i^2 \in I,
--   $$
--
--   and **$k$-sos modulo $I$** if moreover every $h_i$ has degree at most $k$. The **$k$-th theta body** of $I$ is
--
--   $$
--   \mathrm{TH}_k(I) = \bigcap \{\, \{x : \ell(x) \ge 0\} : \ell \text{ linear and } k\text{-sos modulo } I \,\}.
--   $$
--
--   Theta bodies are nested semidefinite relaxations of $\operatorname{conv}(\mathcal V_{\mathbb R}(I))$.
--
--   **Formalization Note** `IsSosModulo I V q` asks for finitely many $h_i$ in a prescribed set $V$ of polynomials; $k$-sos is $V = \{h : \deg h \le k\}$ (total degree). A linear polynomial has total degree at most one, constants included.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 21, §5.2 (sums of squares modulo I; theta bodies)

import Mathlib
import Definitions.Def_ConeLifts_Factorization_Supplement_IsConvexRadical

namespace ConeLifts.Factorization.Supplement

/-- `q` is a **sum of squares modulo `I` with summands in `V`** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §5.2, p. 21): there are finitely many polynomials `h₁, …, hₛ ∈ V` with
`q − ∑ hᵢ² ∈ I`. With `V` all polynomials this is "sos modulo `I`"; with `V` the polynomials of
total degree at most `k` it is "`k`-sos modulo `I`". -/
def IsSosModulo {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ))
    (V : Set (MvPolynomial (Fin n) ℝ)) (q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ (s : ℕ) (h : Fin s → MvPolynomial (Fin n) ℝ), (∀ i, h i ∈ V) ∧ q - ∑ i, h i ^ 2 ∈ I

/-- The **`k`-th theta body** `TH_k(I)` of an ideal `I ⊆ ℝ[x₁, …, xₙ]` (Gouveia, Parrilo &
Thomas, arXiv:1111.3164v2, §5.2, p. 21): the intersection of the half-spaces `{x : ℓ(x) ≥ 0}` over
all linear polynomials `ℓ` (total degree at most one, constants included) that are `k`-sos
modulo `I`. -/
def thetaBody {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ)) (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 →
    IsSosModulo I {h | h.totalDegree ≤ k} ℓ → 0 ≤ polyEval x ℓ}

end ConeLifts.Factorization.Supplement


