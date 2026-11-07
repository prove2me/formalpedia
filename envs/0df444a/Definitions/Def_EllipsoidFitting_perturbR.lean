-- Prove2me | Definitions.Def_EllipsoidFitting_perturbR
-- name    : EllipsoidFitting_perturbR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:10.61885+00:00
-- url     : https://prove2.me/theorems/ac707fc9-c964-4c56-a754-fac42e5e52cb
-- title:
--   The deviation $\eta$, the identity perturbation $R$ and the projections $\Pi_S$, $\Pi_S^\perp$
-- statement:
--   With $L$, $L^*$, $M$ as in the notation:
--
--   1. $\eta=L(I_d)-\mathbf 1_m$, i.e. $\eta[t]=\|v_t\|_2^2-1$, the constraint violation of the identity;
--   2. $R=L^*M^{-1}\eta$, the identity perturbation, so that $L(I_d-R)=\mathbf 1_m$ when $M$ is invertible;
--   3. $\Pi_S=L^*M^{-1}L$, the orthogonal projection onto $S$, and $\Pi_S^\perp=I-\Pi_S$.
--
--   **Formalization Note** $M^{-1}$ is Lean's total matrix inverse (zero when $M$ is singular); every statement using $R$ or $\Pi_S$ assumes $M$ invertible. Page 8 prints "$R:=LM^{-1}\eta$"; the operator is $L^*$, as on pp.5 and 24.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Notation 4–6, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_EllipsoidFitting_constraintMap

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The deviation `η` and the identity perturbation `R`, and the projections `Π_S`, `Π⊥_S`.**
de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*,
arXiv:2608.12415 (version of Nov 3, 2026), Notation 4–6, p.5: "Π := Π_S = L∗M−1L denote the
orthogonal projection to S, and Π⊥_S the projection to its orthogonal complement"; "η = η∅ :=
L(Id) − 1m"; "R := L∗M−1η = L∗M−1(L(Id) − 1m)".

`eta v` is `η = L(I_d) − 1_m`, i.e. `η[t] = ‖v_t‖² − 1`. -/
def eta {m d : ℕ} (v : Fin m → Fin d → ℝ) : Fin m → ℝ :=
  fun t => constraintMap v 1 t - 1

/-- `perturbR v` is `R = L*(M⁻¹ η)`.

**Formalization Note** `M⁻¹` is Mathlib's `Matrix.inv`, which is `0` when `M` is singular; every
statement using `R` assumes `M` invertible. p.8 prints "R := LM−1η"; the operator is `L*` (as on
p.5 and p.24). -/
noncomputable def perturbR {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  liftMap v ((gram v)⁻¹ *ᵥ eta v)

/-- `projS v X` is `Π_S X = L*(M⁻¹ L(X))`. -/
noncomputable def projS {m d : ℕ} (v : Fin m → Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  liftMap v ((gram v)⁻¹ *ᵥ constraintMap v X)

/-- `projSperp v X` is `Π⊥_S X = X − Π_S X`. -/
noncomputable def projSperp {m d : ℕ} (v : Fin m → Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  X - projS v X

end EllipsoidFitting


