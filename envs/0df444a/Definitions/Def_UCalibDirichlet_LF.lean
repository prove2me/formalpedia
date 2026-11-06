-- Prove2me | Definitions.Def_UCalibDirichlet_LF
-- name    : UCalibDirichlet_LF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:56.63808+00:00
-- url     : https://prove2.me/theorems/61a60f75-0251-4936-a1d5-ef86460d5864
-- title:
--   Bernstein approximation gap $L_F(T)$
-- statement:
--   For $F:\Delta_K\to\mathbb R$ and $T\ge1$,
--   $$L_F(T)=T\sup_{q\in\Delta_K}\Big\{\mathbb E_{M\sim\mathrm{Mult}(T,q)}\big[F(M/T)\big]-F(q)\Big\}.$$
--   This is $T$ times the largest multivariate Bernstein approximation gap of $F$. When the outcomes are i.i.d. from $q$, the best forecaster's expected regret is $T(\mathbb E[F(M/T)]-F(q))$, so $L_F(T)$ is a lower bound on the minimax regret for the loss $\ell_F$; the main theorem shows it is also an upper bound up to a factor $K\log T$.
--
--   **Formalization Note** The supremum is the real supremum over the simplex; for a convex finite $F$ the family is bounded.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.8, display (14), p.6

import Mathlib
import Definitions.Def_UCalibDirichlet_multBern

namespace UCalibDirichlet

/-- **The Bernstein approximation gap `L_F(T)`, display (14).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Theorem 1.8, p.6:
"`L_F(T) = T sup_{q∈Δ_K} { E_{M∼Mult(T,q)}[F(M/T)] − F(q) }`. (14)"

`LF F T = T · sup_{q ∈ Δ_K} (B_T F(q) − F(q))`, with `B_T F = multBern F T`.

**Formalization Note.** The supremum is the real `⨆` over the subtype `stdSimplex ℝ (Fin K)`. For a
finite convex `F` on `Δ_K` the family is bounded (F is bounded on the simplex), so the supremum is
not a junk value. The paper uses `T ≥ 1`. -/
noncomputable def LF {K : ℕ} (F : (Fin K → ℝ) → ℝ) (T : ℕ) : ℝ :=
  T * ⨆ q : stdSimplex ℝ (Fin K), (multBern F T q - F q)

end UCalibDirichlet


