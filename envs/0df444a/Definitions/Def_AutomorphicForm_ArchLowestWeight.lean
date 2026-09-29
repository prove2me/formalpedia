-- Prove2me | Definitions.Def_AutomorphicForm_ArchLowestWeight
-- name    : AutomorphicForm_ArchLowestWeight
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/9aa11981-5b85-5023-9793-1a1f7fac023d
-- title:
--   Archimedean lowest-weight predicate at a real place
-- statement:
--   Throughout, $F$ is a number field, $w$ an infinite place of $F$ together with a witness $hw$ that $w$ is real, and $\varphi$ a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$ (the group `AdelicGL2 (𝓞 F) F`). For $z$ in the upper half-plane, `iwasawaSectionGL z` is the element of $\mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix}\operatorname{Im} z&\operatorname{Re} z\\0&1\end{pmatrix}$; it is transported entrywise into $\mathrm{GL}_2$ of the completion $F_w$ along the inverse of the isomorphism $F_w\cong\mathbb{R}$ attached to a real place, and then placed into the adelic group by `adelicArchGLInclAt F w`, which puts the given matrix in the component at $w$ and the identity at all other places (archimedean and finite). Write $D_g(z)$ for the resulting value $\varphi\bigl(g\cdot\iota_w(\ldots)\bigr)$, the descent of $\varphi$ at $w$ through $g$.
--
--   The predicate [`AutomorphicForm.IsArchLowestWeightAt w hw φ`](../def/AutomorphicForm_ArchLowestWeight.html#L13) asserts that there exists a complex number $\sigma$ such that for every adelic $g$ the function $z\mapsto (\operatorname{Im} z)^{\sigma}\,D_g(z)$ is differentiable on the upper half-plane in the sense of `MDifferentiable` for the trivial complex model $\mathcal{I}(\mathbb{C})$ on source and target, the power being the complex power of the positive real number $\operatorname{Im} z$. Note the quantifier order: a single exponent $\sigma$ must work uniformly in $g$. The accompanying lemmas record an unfolding statement; that the zero function satisfies the predicate (with $\sigma=0$); stability under multiplication of $\varphi$ by a fixed complex constant; a variant in which a real exponent $\sigma$ is given and the normalising factor is the real power $(\operatorname{Im} z)^{\sigma}$ coerced to $\mathbb{C}$; and that the predicate `IsArchHolomorphicAt w hw φ`, which demands holomorphy of the $(\operatorname{Im} z)^{-1}$-normalised descents, implies it, being the case $\sigma=-1$.
--
--   **Relation to Mathlib.** Mathlib supplies the complex-manifold structure on the upper half-plane and the notion `MDifferentiable`, and the adele ring, completions at infinite places and the isomorphism $F_w\cong\mathbb{R}$ at a real place; the predicate on adelic functions itself is the project's own.
--
--   **Where it is used.** The stronger predicate `IsArchHolomorphicAt` is one of the archimedean conditions imposed in the project's cuspidality notion `viaCompactCuspNotion`, alongside the weight-one character condition at each real place; `IsArchLowestWeightAt` is the corresponding weakened condition, allowing an arbitrary uniform exponent in place of the normalisation by $(\operatorname{Im} z)^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchLowestWeight.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

noncomputable section

namespace AutomorphicForm

def IsArchLowestWeightAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ σ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

variable {F : Type} [Field F] [NumberField F]

theorem isArchLowestWeightAt_iff (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsArchLowestWeightAt w hw φ ↔
      ∃ σ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
        (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
            (iwasawaSectionGL z))) :=
  Iff.rfl

theorem isArchLowestWeightAt_zero (w : InfinitePlace F) (hw : w.IsReal) :
    IsArchLowestWeightAt w hw (fun _ => 0) :=
  ⟨0, fun _ => by simpa using mdifferentiable_const⟩

theorem IsArchLowestWeightAt.const_mul {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchLowestWeightAt w hw φ) (a : ℂ) :
    IsArchLowestWeightAt w hw (fun g => a * φ g) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun g => ?_⟩
  have := (hσ g).const_smul a
  simpa [Pi.smul_def, smul_eq_mul, mul_left_comm] using this

theorem isArchLowestWeightAt_of_rpow {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (σ : ℝ)
    (h : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) ^ σ : ℝ) : ℂ) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) :
    IsArchLowestWeightAt w hw φ := by
  refine ⟨(σ : ℂ), fun g => ?_⟩
  have hfun : (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ (σ : ℂ)) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) =
      (fun z : UpperHalfPlane =>
      (((z.im : ℝ) ^ σ : ℝ) : ℂ) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) := by
    funext z
    rw [Complex.ofReal_cpow (le_of_lt z.im_pos)]
  rw [hfun]
  exact h g

theorem IsArchHolomorphicAt.isArchLowestWeightAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchHolomorphicAt w hw φ) :
    IsArchLowestWeightAt w hw φ := by
  refine ⟨-1, fun g => ?_⟩
  have hfun : (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ (-1 : ℂ)) * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) =
      (fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL z)))) := by
    funext z
    rw [Complex.cpow_neg_one]
  rw [hfun]
  exact h g

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @IsArchLowestWeightAt
#print axioms AutomorphicForm.isArchLowestWeightAt_zero
#print axioms AutomorphicForm.IsArchLowestWeightAt.const_mul
#print axioms AutomorphicForm.isArchLowestWeightAt_of_rpow
#print axioms AutomorphicForm.IsArchHolomorphicAt.isArchLowestWeightAt
end Battery


