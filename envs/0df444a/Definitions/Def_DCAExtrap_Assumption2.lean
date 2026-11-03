-- Prove2me | Definitions.Def_DCAExtrap_Assumption2
-- name    : DCAExtrap_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:27.669125+00:00
-- url     : https://prove2.me/theorems/e7831e6a-8bb6-4717-886d-b14f4a73c72a
-- title:
--   Assumption 2 (KL property of $\Phi$, local Lipschitz gradients)
-- statement:
--   Let $\Phi$ be the auxiliary function (24). Assumption 2 requires:
--
--   1. (a) $\Phi$ satisfies the Kurdyka–Łojasiewicz property at every point of $\operatorname{dom}\partial_L\Phi=\{z:\partial_L\Phi(z)\neq\emptyset\}$;
--   2. (b) $\nabla f$ and $\nabla\varphi$ are Lipschitz continuous on every bounded subset of $E$;
--   3. (c) $h$ is differentiable and $\nabla h$ is Lipschitz continuous on every bounded subset of $E$.
--
--   Here $\partial_L$ is the limiting subdifferential and the KL property at $z^*$ asks for $\eta>0$, a neighbourhood $V$ of $z^*$ and a concave desingularizing function $\psi\in M_\eta$ ($\psi(0)=0$, $C^1$ with $\psi'>0$ on $(0,\eta)$) with $\psi'(\Phi(z)-\Phi(z^*))\operatorname{dist}(0,\partial_L\Phi(z))\ge1$ for $z\in V$ with $\Phi(z^*)<\Phi(z)<\Phi(z^*)+\eta$.
--
--   **Formalization Note** The limiting subdifferential and the KL property reuse the published `NonconvexSplitting.Shared.LimitingSubdiff` and `NonconvexSplitting.ADMMKL.HasKLProperty` (whose inequality, quantified over every $v\in\partial_L\Phi(z)$, is the distance form with $\operatorname{dist}(0,\emptyset)=+\infty$; a finite $\eta$ loses nothing since $\psi$ restricts). "Lipschitz on any bounded subset" is: for every bounded $S$ there is a Lipschitz constant on $S$.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, Assumption 2, p.8; KL property, pp.4–5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_DCAExtrap_lyapunov

namespace DCAExtrap

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- **Assumption 2** (Phan–Le Thi, arXiv:2106.04743v1, p.8):
(a) `Φ` satisfies the KL property at any point of `dom ∂_LΦ`;
(b) `∇f` and `∇φ` are Lipschitz continuous on any bounded subset of `E`;
(c) `h` is differentiable with `∇h` Lipschitz continuous on any bounded subset of `E`.

**Formalization Note.** `Φ = lyapunov f g h φ L δ` on `WithLp 2 (E × E)`; `∂_L` is the limiting
subdifferential `NonconvexSplitting.Shared.LimitingSubdiff` and the KL property (with
desingularising functions in the class `M_η` of p.4) is `NonconvexSplitting.ADMMKL.HasKLProperty`.
`dom ∂_LΦ` is the set of points where `∂_LΦ` is nonempty. "Lipschitz on any bounded subset" is,
for every bounded `S`, some Lipschitz constant on `S`. -/
structure Assumption2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (φ : E → ℝ) (L δ : ℝ) : Prop where
  kl : ∀ z : WithLp 2 (E × E), (LimitingSubdiff (lyapunov f g h φ L δ) z).Nonempty →
    HasKLProperty (lyapunov f g h φ L δ) z
  gradF_lip : ∀ S : Set E, Bornology.IsBounded S → ∃ K, LipschitzOnWith K (gradient f) S
  gradφ_lip : ∀ S : Set E, Bornology.IsBounded S → ∃ K, LipschitzOnWith K (gradient φ) S
  h_diff : Differentiable ℝ h
  gradH_lip : ∀ S : Set E, Bornology.IsBounded S → ∃ K, LipschitzOnWith K (gradient h) S

end DCAExtrap


