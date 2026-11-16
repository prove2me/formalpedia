-- Prove2me | Definitions.Def_DRSub4633_Supplement_CubeQueries
-- name    : DRSub4633_Supplement_CubeQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:30:26.911207+00:00
-- url     : https://prove2.me/theorems/033daa17-acae-441e-820e-29af4a7e6109
-- title:
--   Objective queries stay in the cube
-- statement:
--   A transcript satisfies this condition when every value query and every gradient query in it is made at a point of $Q=[0,1]^n$. LMO and projection queries are unconstrained. It encodes the model's restriction that "exact values and full gradients are available on $Q$" (p.8).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, p.8, and Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query
import Definitions.Def_GeomDRSub_cube

namespace DRSub4633.Supplement

/-- **Objective queries stay in the cube.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, p.8: "Exact values and full
gradients are available on `Q`"; Theorem 6.3, p.37: "exact cube value and gradient queries".

`CubeQueries h` says that every value or gradient query in the transcript `h` is at a point of
`Q = [0,1]ⁿ`. LMO and projection queries are unconstrained. -/
def CubeQueries {n : ℕ} (h : List (Query n × (ℝ × EuclideanSpace ℝ (Fin n)))) : Prop :=
  ∀ p ∈ h, match p.1 with
    | .value y => y ∈ GeomDRSub.cube n
    | .grad y => y ∈ GeomDRSub.cube n
    | _ => True

end DRSub4633.Supplement


