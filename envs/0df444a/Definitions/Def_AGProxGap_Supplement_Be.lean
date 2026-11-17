-- Prove2me | Definitions.Def_AGProxGap_Supplement_Be
-- name    : AGProxGap_Supplement_Be
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:15:36.125341+00:00
-- url     : https://prove2.me/theorems/ef4c7366-3bea-4b29-98ab-52fc08c6eb6d
-- title:
--   The bound $B_e$ of Theorem 4.1 and the parameters $s,N,D_Y,D_Z$
-- statement:
--   Let $m,n\ge1$, $\rho=m/n$, let $\mathfrak g$ be the genus, $\ell\ge1$, $e\ge0$ and $0<\eta<1-\sqrt\rho$. Section 4 sets
--   $$s:=\Bigl\lceil\frac{2\sqrt\rho}{\eta}\Bigr\rceil+2,\qquad N:=\bigl\lceil(s+1)\sqrt{mn}\bigr\rceil+\mathfrak g-1,\qquad D_Y:=\Bigl\lfloor\frac{N-\mathfrak g}{m}\Bigr\rfloor,\qquad D_Z:=\ell sD_Y,$$
--   and Theorem 4.1 bounds the number of MCA-bad parameters by
--   $$B_e:=(2D_Y+1)D_Z+\frac{n-m}{n-m-e}\bigl(4mD_YD_Z+\ell D_Y\bigr)+\ell D_Y(e+1).$$
--
--   These are the interpolation parameters of the Guruswami–Sudan step of §4: $s$ is the multiplicity, $N$ the pole bound, $D_Y$ and $D_Z$ the degree bounds of the interpolation polynomial.
--
--   **Formalization Note** $s,N,D_Y,D_Z$ are natural numbers (ceilings of positive reals, floor division); $B_e$ is real, with the fraction a real quotient.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §4, p.23 (parameters and Theorem 4.1)

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AGProxGap.Supplement

/-- The multiplicity `s := ⌈2√ρ/η⌉ + 2` of §4 (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4, p.23), with `ρ = m/n`.

**Formalization Note** `Nat.ceil` of a nonnegative real is the ceiling. -/
noncomputable def sPar (m n : ℕ) (η : ℝ) : ℕ :=
  ⌈2 * Real.sqrt ((m : ℝ) / n) / η⌉₊ + 2

/-- The pole bound `N := ⌈(s + 1)√(mn)⌉ + 𝔤 − 1` of §4 (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4, p.23), `g` the genus.

**Formalization Note** For `m, n ≥ 1` the ceiling is at least `1`, so the natural subtraction
does not truncate. -/
noncomputable def NPar (m n g : ℕ) (η : ℝ) : ℕ :=
  ⌈((sPar m n η : ℝ) + 1) * Real.sqrt ((m : ℝ) * n)⌉₊ + g - 1

/-- The `Y`-degree bound `D_Y := ⌊(N − 𝔤)/m⌋` of §4 (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4, p.23).

**Formalization Note** Natural division is the floor; `N − 𝔤 ≥ 0` is a true difference. -/
noncomputable def DYPar (m n g : ℕ) (η : ℝ) : ℕ :=
  (NPar m n g η - g) / m

/-- The `Z`-degree bound `D_Z := ℓ s D_Y` of §4 (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4, p.23). -/
noncomputable def DZPar (ℓ m n g : ℕ) (η : ℝ) : ℕ :=
  ℓ * sPar m n η * DYPar m n g η

/-- **The bound `B_e` of Theorem 4.1** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Theorem 4.1, p.23):
`B_e := (2D_Y + 1)D_Z + (n − m)/(n − m − e)·(4mD_Y D_Z + ℓD_Y) + ℓD_Y(e + 1)`, with
`s = ⌈2√ρ/η⌉ + 2`, `N = ⌈(s + 1)√(mn)⌉ + 𝔤 − 1`, `D_Y = ⌊(N − 𝔤)/m⌋`, `D_Z = ℓsD_Y` and
`ρ = m/n`.

**Formalization Note** `B_e` is a real number; the fraction `(n − m)/(n − m − e)` is real
division (Theorem 4.1's hypothesis `e ≤ (1 − √ρ − η)n` makes its denominator positive). `g` is
the genus `𝔤`. -/
noncomputable def Be (ℓ m n g e : ℕ) (η : ℝ) : ℝ :=
  (2 * (DYPar m n g η : ℝ) + 1) * DZPar ℓ m n g η
    + ((n : ℝ) - m) / ((n : ℝ) - m - e)
        * (4 * (m : ℝ) * DYPar m n g η * DZPar ℓ m n g η + ℓ * DYPar m n g η)
    + ℓ * (DYPar m n g η : ℝ) * (e + 1)

end AGProxGap.Supplement


