-- Prove2me | Definitions.Def_AutomorphicForm_PeterssonIntegral
-- name    : AutomorphicForm_PeterssonIntegral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/67ee46de-89bc-5e52-95c1-0ab9aff5e0a2
-- title:
--   Weighted Petersson integral on adelic GL(2)
-- statement:
--   For a number field $F$ this module defines a single object, [`AutomorphicForm.peterssonIntegral`](../def/AutomorphicForm_PeterssonIntegral.html#L13). Its data are a real exponent $s$, a set $S \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ (where $\mathrm{GL}_2(\mathbb{A}_F)$ is the project's `AdelicGL2` $= \mathrm{GL}_2$ of the adele ring of $F$) and two functions $x, y \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$; its value is the complex number
--   $$\int_S x(g)\,\overline{y(g)}\;\bigl(\,\|\det g\|^{-s}\bigr)\,dg,$$
--   the integral being a Bochner integral over $S$ against the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` for the Borel $\sigma$-algebra `glBorel (Fin 2) (𝓞 F) F` (this measurable-space instance is installed inside the definition by `letI`). Here $\overline{\phantom{y}}$ is complex conjugation (`starRingEnd ℂ`), $\det g$ is taken as a unit of $\mathbb{A}_F$, and $\|\cdot\|$ is the project's [`NumberField.TateGlobal.ideleNorm`](../def/NumberField_TateGlobalZeta.html#L19), defined as the value of Mathlib's module-Haar character `distribHaarChar` of the adele ring on the given idele, viewed as a positive real; the real power $\|\det g\|^{-s}$ is then coerced into $\mathbb{C}$.
--
--   This is a plain definition: no integrability hypothesis is imposed, so for non-integrable integrands the value is $0$ by the convention governing the Bochner integral, and no invariance, positivity or independence of $S$ is asserted. The pairing is linear in $x$ and conjugate-linear in $y$; with $s$ the integral is twisted by $\|\det g\|^{-s}$, which for $s = 0$ gives the unweighted Petersson integral over $S$.
--
--   **Relation to Mathlib.** Mathlib has no Petersson pairing for automorphic functions on adelic $\mathrm{GL}_2$; this is the project's own definition. It is built from Mathlib's Bochner integral and from the project's Haar measure `adelicGLHaar` (Mathlib's `Measure.haar` for the Borel structure on $\mathrm{GL}_2$ of the adeles) and idele norm `ideleNorm` (Mathlib's `distribHaarChar` of the adele ring).
--
--   **Where it is used.** The weighted Petersson integral provides the inner product used on the analytic side of the modularity argument, where automorphic forms on $\mathrm{GL}_2(\mathbb{A}_F)$ are treated as square-integrable functions on a region $S$ of the adelic group, the factor $\|\det g\|^{-s}$ absorbing a central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_PeterssonIntegral.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHaar

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def peterssonIntegral (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  letI := glBorel (Fin 2) (𝓞 F) F
  ∫ g in S,
    x g * (starRingEnd ℂ) (y g) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

end AutomorphicForm

end


