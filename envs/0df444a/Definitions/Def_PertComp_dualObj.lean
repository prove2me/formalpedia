-- Prove2me | Definitions.Def_PertComp_dualObj
-- name    : PertComp_dualObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:00.11626+00:00
-- url     : https://prove2.me/theorems/450c72be-9cfa-4e54-959c-ef4a56cf4b0f
-- title:
--   Closed form (3.11) of the dual objective
-- statement:
--   In the setting of Problem 1.1, for $(\xi^*,y^*)\in\mathbb R\times Y^*$,
--   $$(\xi^*,y^*)\mapsto\varphi^*(\xi^*)+\big(h^*\,\Box\,\widetilde{f^*}(\cdot,\xi^*)\big)(-L^*y^*)+g^*(y^*)+\ell^*(y^*),$$
--   where $\widetilde{f^*}$ is the perspective (2.7) of the conjugate $f^*\colon X^*\to\,]-\infty,+\infty]$ and $L^*y^*=y^*\circ L$. Theorem 3.3(ii) states that the dual problem (2.25) of the perturbation $F$ is the minimization of this function; its set of minimizers is $\mathscr D$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Theorem 3.3(ii), (3.11), p.12

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_PWDB_conj
import Definitions.Def_PertComp_infConv
import Definitions.Def_PertComp_persp

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Theorem 3.3(ii), (3.11), p.12: the closed-form
dual objective of Problem 1.1,
`(ξ*, y*) ↦ φ*(ξ*) + (h* □ \widetilde{f*}(·, ξ*))(−L*y*) + g*(y*) + ℓ*(y*)`,
where `\widetilde{f*}` is the perspective (2.7) of the conjugate `f* : X* → ]−∞, +∞]`.

**Formalization Note.** `φ*` is the published `PWDB.conj φ` on `ℝ`
(`ℝ* = ℝ` through `⟨t, s⟩ = t s`), `h*, f*, g*, ℓ*` are
`RockafellarMaxMono.Shared.conj`, `L*y*` is `y'.comp L`. This is the right-hand side of (3.11),
not the dual problem (2.25) itself (`dualFun`). -/
noncomputable def dualObj {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (φ : ℝ → EReal) (f : X → EReal)
    (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal) (ξ' : ℝ) (y' : StrongDual ℝ Y) : EReal :=
  PWDB.conj φ ξ' +
    infConv (RockafellarMaxMono.Shared.conj h)
      (fun x' => persp (RockafellarMaxMono.Shared.conj f) x' ξ') (-(y'.comp L)) +
    RockafellarMaxMono.Shared.conj g y' + RockafellarMaxMono.Shared.conj ℓ y'

end PertComp


