-- Prove2me | Definitions.Def_AdaDiscRL_IsZoomingDim
-- name    : AdaDiscRL_IsZoomingDim
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:36.369997+00:00
-- url     : https://prove2.me/theorems/2a8075a9-d5dc-448c-97b4-27a0bc4a9f39
-- title:
--   Step-$h$ zooming dimension $z_h$ with constant $c_h$
-- statement:
--   The **step-$h$ zooming dimension with constant $c_h$** is
--   $$
--   z_h=\inf\{d>0:\ N_r(Z^r_h)\le c_h r^{-d}\ \text{for all } r\in(0,1]\}.
--   $$
--   `IsZoomingDim M D C_L h c z` states that $z$ is this infimum (the greatest lower bound of the set) for the near-optimal sets with constant $C_L$, packings taken in $\mathcal D$. It replaces the ambient dimension in the regret bounds.
--
--   **Formalization Note** The paper writes $\forall r>0$; for $r>1$ the packing number of a nonempty set is at least $1$ while $c_hr^{-d}\to0$, so the printed set is empty for every $c_h$. The scales are restricted to $r\in(0,1]$ (every use has $r=\mathrm{diam}(B)\le1$). `IsGLB` is used, so an empty set gives no zooming dimension instead of a junk value.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.7, p.11 (scales r ∈ (0,1]; see p.10, covering dimension)

import Mathlib
import Definitions.Def_AdaDiscRL_nearOptSet
import Definitions.Def_AdaDiscRL_packingNum

namespace AdaDiscRL

/-- **Step-`h` zooming dimension with constant `c_h`** (arXiv:2110.15843v3, Definition 2.7, p.11):
`z_h = inf{d > 0 : N_r(Z_h^r) ≤ c_h r^{−d} ∀ r}`, packings taken in the metric `D` of `S × A`.

`IsZoomingDim M D C_L h c z` says `z` is the greatest lower bound of
`{d > 0 | ∀ r ∈ (0, 1], N_r(Z_h^r) ≤ c r^{−d}}`.

**Formalization Note.** (i) `r` ranges over `(0, 1]`, not `r > 0`: for `r > 1` the packing number
of a nonempty set is at least `1` while `c r^{−d} → 0`, so the printed set is empty for every `c`
(every use has `r = diam(B) ≤ 1`, and `S × A` has diameter `1`). (ii) `IsGLB` is used instead of
`sInf`, so the empty set yields no instance (no junk value `sInf ∅ = 0`). -/
def IsZoomingDim {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (D : S × A → S × A → ℝ) (CL : ℝ) (h : Fin H) (c z : ℝ) : Prop :=
  IsGLB {d : ℝ | 0 < d ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
    ((packingNum D r (nearOptSet M CL h r) : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (c * r ^ (-d))} z

end AdaDiscRL


