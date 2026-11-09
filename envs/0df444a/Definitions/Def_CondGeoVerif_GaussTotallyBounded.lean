-- Prove2me | Definitions.Def_CondGeoVerif_GaussTotallyBounded
-- name    : CondGeoVerif_GaussTotallyBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:18:49.124173+00:00
-- url     : https://prove2.me/theorems/b2e557bf-3e7f-47d8-91fe-ed61ee4447be
-- title:
--   Gaussian disagreement $d_\gamma(f,g)$ and total boundedness of a rule family
-- statement:
--   For rules $f,g:\mathbb R^k\to\{-1,1\}$ the **Gaussian disagreement** is
--   $$d_\gamma(f,g)=\mathbb P(f(G)\ne g(G)),\qquad G\sim N(0,I_k).$$
--   A family $F$ of rules is **totally bounded in Gaussian disagreement** if for every $b>0$ a finite subset $F[b]\subseteq F$ approximates every rule to disagreement at most $b$: every $f\in F$ has some $f_0\in F[b]$ with $d_\gamma(f,f_0)\le b$.
--
--   Total boundedness is the standing assumption on the unknown intrinsic rule; it supplies the finite rule alphabets used by proper protocols.
--
--   **Formalization Note** The finite net is a `Finset` contained in $F$. Borel measurability of the rules is a separate hypothesis wherever the notion is used.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2, p.4 (PDF p.7); §A.9, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory

/-- The Gaussian disagreement `d_γ(f, g) = P(f(G) ≠ g(G))`, `G ∼ N(0, I_k)` (Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
§A.9, p.21 = PDF p.24). -/
noncomputable def gaussDisagree {k : ℕ} (f g : Vec k → Bool) : ℝ :=
  (gauss k {u | f u ≠ g u}).toReal

/-- **Total boundedness in Gaussian disagreement** (Chen, Oct. 2026, §2, p.4 = PDF p.7): "for
every `b > 0`, a finite subset `F[b] ⊂ F` approximates every rule to disagreement at most `b`."

**Formalization Note** The finite net is a `Finset` contained in `F`. Borel measurability of the
rules is a separate hypothesis wherever the notion is used. -/
def GaussTotallyBounded {k : ℕ} (F : Set (Vec k → Bool)) : Prop :=
  ∀ b : ℝ, 0 < b → ∃ F₀ : Finset (Vec k → Bool), (↑F₀ : Set (Vec k → Bool)) ⊆ F ∧
    ∀ f ∈ F, ∃ f₀ ∈ F₀, gaussDisagree f f₀ ≤ b

end CondGeoVerif


