-- Prove2me | Definitions.Def_JencovaRenyi_IsNormingDual
-- name    : JencovaRenyi_IsNormingDual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:18.273774+00:00
-- url     : https://prove2.me/theorems/cee0c636-734f-426b-a25e-9d3c8f9b16be
-- title:
--   The norming dual element $h = T_{q,\varphi}(k)$
-- statement:
--   Let $1/p+1/q=1$ and $k\in L_p(\mathcal M,\varphi)$. An element $h$ is a **norming dual** of $k$, written $h = T_{q,\varphi}(k)$, if $h$ lies in the unit ball of $L_q(\mathcal M,\varphi)$ and
--   $$
--   \langle h, k\rangle = \|k\|_{p,\varphi}.
--   $$
--   For $1<p<\infty$ and $k\ne0$ there is exactly one such $h$ (a milestone of this mission); Theorem 3.14 uses $T_{\beta,\varphi}(h_\psi)$ and $T_{\beta,\Phi(\varphi)}(\Phi(h_\psi))$.
--
--   **Formalization Note** A predicate on $(k, h)$ with the exponents $p, q$ as explicit arguments, rather than a function, so that no default value can enter a statement.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_pairing

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `h = T_{q,φ}(k)` (Jenčová, arXiv:1609.08462v4, §2.2, p.6): `h` lies in the unit ball of
`L_q(M, φ)` and `⟨h, k⟩ = ‖k‖_{p,φ}`, where `k ∈ L_p(M, φ)` and `1/p + 1/q = 1`.

**Formalization Note.** The paper's `T_{q,φ}(k)` is the unique such element for
`1 < p < ∞`, `k ≠ 0` (milestone `normingDual_existsUnique`); this predicate states the defining
property, and the exponents `p`, `q` are explicit arguments. -/
def IsNormingDual {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ : Predual A) (p q : ℝ≥0∞) (k h : Predual A) : Prop :=
  lpNorm S φ q h ≤ 1 ∧ pairing S φ q h k = (((lpNorm S φ p k).toReal : ℝ) : ℂ)

end JencovaRenyi


