-- Prove2me | Definitions.Def_PolySphereLP_Fa
-- name    : PolySphereLP_Fa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:32.552826+00:00
-- url     : https://prove2.me/theorems/6b588eb1-31a3-4ef9-8515-931ef9c9b32a
-- title:
--   The top harmonic component $F_{\mathbf a}=\Pi_q(P_{\mathbf a}^r)$
-- statement:
--   For a coefficient vector $\mathbf a$,
--   $$F_{\mathbf a}=\Pi_q\big(P_{\mathbf a}^r\big),$$
--   the $L^2(\sigma)$ projection of the powered objective onto $\mathcal H_{n,q}$. It has mean zero and serves as the calibration direction of the witness (39).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (39), p.16

import Mathlib
import Definitions.Def_PolySphereLP_piProj
import Definitions.Def_PolySphereLP_Pa

namespace PolySphereLP

/-- **The top harmonic component `F_a = Π_q(P_a^r)` of the powered objective.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (39), p.16.

`Fa n q r Y a = Π_q((P_a)^r)` with `Π_q = piProj n q`. The items take `r = q/d`. -/
noncomputable def Fa (n q r : ℕ) {h : ℕ} (Y : Fin h → MvPolynomial (Fin n) ℝ) (a : Fin h → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  piProj n q (Pa Y a ^ r)

end PolySphereLP


