-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
-- name    : LanglandsTunnell_CubicInduction_GodementSection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/52c692ab-8f0c-57f0-83e7-1a8f91418362
-- title:
--   Column Fourier transforms and Godement sections for GL3​
-- statement:
--   Throughout, $v$ is a finite place of $\mathbb Q$ and $F=\mathbb Q_v$ is the completion `v.adicCompletion ℚ`, equipped with its Borel structure and with the project's self-dual local Haar measure `selfDualHaarAt`. The elementary constructors `setCol23` and `setCol22` replace the $j$-th column of a $2\times 3$ (resp. $2\times 2$) matrix over $F$ by a pair $u=(u_1,u_2)$, the first coordinate going into row $0$. For an additive character $\eta$ of $F$, `colFourier23 v η j Φ` is the partial Fourier transform in the $j$-th column, $(X)\mapsto\int_{F\times F}\Phi(X\text{ with column }j\text{ set to }u)\,\eta(u_1X_{0j}+u_2X_{1j})\,du$, the measure being the product of two copies of `selfDualHaarAt`; `colFourier22` is the same for $2\times 2$ matrices. `rowFourier23 v η` is the transform in the last column, `colFourier23 v η 2`, and `matFourier23 v η` (resp. `matFourier22 v η`) is the composite of the column transforms over all columns, with the same character throughout. These are plain total functions, the integrals being Bochner integrals, so no integrability or smoothness condition is built in.
--
--   `godementArg v h`, for $h\in GL_2(F)$, is the $2\times 3$ matrix whose columns indexed by `Fin.castSucc` are those of $h$ and whose last column is the index-$1$ column of `transposeInvN (Fin 2) h`. Given $\eta$, a measure $\mu_2$ on $GL_2(F)$, a character $\lambda_0$ of $F^\times$, and a datum $\Phi$ assigning to each $2\times 3$ matrix a function on $GL_2(F)$, `godementWhittaker3` is the function on `LocalGL3 v` given by
--   $$\lambda_0(\det g)\,\mathrm{mod}(\det g)\int_{GL_2(F)}\bigl(\mathrm{rowFourier23}\ v\ \eta^{-1}(X\mapsto \Phi(Xg)(h^{-1}))\bigr)(\mathrm{godementArg}\ v\ h)\,\lambda_0(\det h)\,\mathrm{mod}(\det h)^{1/2}\,d\mu_2(h),$$
--   where $\mathrm{mod}$ denotes the local modulus `modulus`. Finally `godementZeta2 v μ₂ c φ χ s` is the zeta integral $\int_{GL_2(F)} c(g)\,\varphi(g)\,\chi(\det g)\,\mathrm{mod}(\det g)^{s}\,d\mu_2(g)$ attached to a coefficient function $c$, a function $\varphi$ on $2\times 2$ matrices, a character $\chi$ and $s\in\mathbb C$. The accompanying lemmas restate each definition and evaluate `godementArg` column by column.
--
--   **Relation to Mathlib.** Mathlib provides the Haar measures, Bochner integral and general linear groups used here, but has no Fourier transforms on spaces of matrices over a local field, no Godement–Jacquet zeta integrals and no mixed-model Whittaker integrals; all of these are the project's own definitions.
--
--   **Where it is used.** These local constructions belong to the cubic-induction package supporting the Langlands–Tunnell theorem, which supplies the modularity of the mod-$3$ representation attached to a Frey curve and thereby the starting point of the Wiles argument. The $GL_3$ Whittaker integral and the $GL_2$ zeta integral are the local ingredients for the functional equation of $GL_3\times GL_2$ Rankin–Selberg integrals used in the converse-theorem step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_GodementSection.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section GodementSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

def setCol23 (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k

theorem setCol23_apply (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (j : Fin 3)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i : Fin 2) (k : Fin 3) :
    setCol23 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl

def setCol22 (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.of fun i k => if k = j then (if i = 0 then u.1 else u.2) else X i k

theorem setCol22_apply (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (j : Fin 2)
    (u : v.adicCompletion ℚ × v.adicCompletion ℚ) (i k : Fin 2) :
    setCol22 v X j u i k = if k = j then (if i = 0 then u.1 else u.2) else X i k :=
  rfl

def colFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))

theorem colFourier23_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    colFourier23 v η j Φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        Φ (setCol23 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl

def colFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  letI := localBorel ℚ v
  ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
    φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))

theorem colFourier22_apply (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 2)
    (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    colFourier22 v η j φ X =
      letI := localBorel ℚ v
      ∫ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
        φ (setCol22 v X j u) * η (u.1 * X 0 j + u.2 * X 1 j) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
  rfl

def rowFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 2 Φ

theorem rowFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    rowFourier23 v η Φ = colFourier23 v η 2 Φ :=
  rfl

def matFourier23 (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ :=
  colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ))

theorem matFourier23_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) :
    matFourier23 v η Φ = colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 Φ)) :=
  rfl

def matFourier22 (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ :=
  colFourier22 v η 0 (colFourier22 v η 1 φ)

theorem matFourier22_eq (η : AddChar (v.adicCompletion ℚ) ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    matFourier22 v η φ = colFourier22 v η 0 (colFourier22 v η 1 φ) :=
  rfl

def godementArg (h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
  Matrix.of fun i k =>
    Fin.lastCases ((transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1)
      (fun k' : Fin 2 => (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k') k

theorem godementArg_apply_castSucc (h : GL (Fin 2) (v.adicCompletion ℚ)) (i k : Fin 2) :
    godementArg v h i (Fin.castSucc k) = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i k := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_castSucc]

theorem godementArg_apply_last (h : GL (Fin 2) (v.adicCompletion ℚ)) (i : Fin 2) :
    godementArg v h i (Fin.last 2) = (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i 1 := by
  simp only [godementArg, Matrix.of_apply, Fin.lastCases_last]

def godementWhittaker3 (η : AddChar (v.adicCompletion ℚ) ℂ)
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (lam0 : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (g : LocalGL3 v) : ℂ :=
  letI := localGLBorel ℚ v
  ((lam0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
    * ∫ h : GL (Fin 2) (v.adicCompletion ℚ),
        rowFourier23 v η⁻¹
            (fun X => Φ (X * ((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹)
            (godementArg v h)
          * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) ∂μ₂

theorem godementWhittaker3_apply (η : AddChar (v.adicCompletion ℚ) ℂ)
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (lam0 : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (g : LocalGL3 v) :
    godementWhittaker3 v η μ₂ lam0 Φ g =
      letI := localGLBorel ℚ v
      ((lam0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
        * ∫ h : GL (Fin 2) (v.adicCompletion ℚ),
            rowFourier23 v η⁻¹
                (fun X => Φ (X * ((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹)
                (godementArg v h)
              * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
              * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
                  ^ (1 / 2 : ℂ) ∂μ₂ :=
  rfl

def godementZeta2 (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (c : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  letI := localGLBorel ℚ v
  ∫ g : GL (Fin 2) (v.adicCompletion ℚ),
    c g * φ ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
      * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂

theorem godementZeta2_apply (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (c : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    godementZeta2 v μ₂ c φ χ s =
      letI := localGLBorel ℚ v
      ∫ g : GL (Fin 2) (v.adicCompletion ℚ),
        c g * φ ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
          * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂ :=
  rfl

end GodementSection

end LanglandsTunnell.CubicInduction

end


