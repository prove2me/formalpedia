-- Prove2me | Definitions.Def_MatchVec3_fiber
-- name    : MatchVec3_fiber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:52.675623+00:00
-- url     : https://prove2.me/theorems/6542a0dd-c5e3-436c-a11b-c94a9a7a98cb
-- title:
--   An $L$-sum fiber
-- statement:
--   For a list $U$ in $\mathbb Z_m^n$ of length $K$, an integer $L$ and $x\in\mathbb Z_m^n$, the **$L$-sum fiber** of $x$ is
--
--   $$\Big\{A\in\binom{[K]}{L}:\ \Sigma_L(A)=x\Big\},\qquad \Sigma_L(A)=\sum_{i\in A}u_i.$$
--
--   The paper bounds the size of these fibers by induction on $L$.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §3, p.10

import Mathlib

namespace MatchVec3

/-- **An `L`-sum fiber** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…), §3,
p.10): `{A ∈ ([K] choose L) : Σ_L(A) = x}`, where `Σ_L(A) = ∑_{i ∈ A} u_i`. -/
def fiber {m n K : ℕ} (U : Fin K → Fin n → ZMod m) (L : ℕ) (x : Fin n → ZMod m) :
    Finset (Finset (Fin K)) :=
  (Finset.powersetCard L Finset.univ).filter fun A => ∑ i ∈ A, U i = x

end MatchVec3


