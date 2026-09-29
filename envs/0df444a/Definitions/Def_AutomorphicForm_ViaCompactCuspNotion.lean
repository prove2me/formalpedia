-- Prove2me | Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
-- name    : AutomorphicForm_ViaCompactCuspNotion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/f45e1fb6-153f-53a3-a0a9-ae94f094bb0b
-- title:
--   Compact-pins cuspidality notion for ℤ√(−2) eigensystems
-- statement:
--   Four things are set up here. First, `iotaZsqrtdNegTwo` is the fixed ring homomorphism $\mathbb{Z}[\sqrt{-2}]\to\mathbb{C}$ obtained from `Zsqrtd.lift` by sending the generator to $\sqrt2\,i$; `iotaZsqrtdNegTwo_apply` records that $z\mapsto z_{\mathrm{re}}+z_{\mathrm{im}}\sqrt2\,i$. Second, `iwasawaSectionGL` sends $z$ in the upper half-plane to the matrix $\begin{pmatrix}\operatorname{Im}z&\operatorname{Re}z\\0&1\end{pmatrix}\in GL_2(\mathbb{R})$ (invertible since $\operatorname{Im}z\neq0$), the usual section of $GL_2(\mathbb{R})\to\mathfrak{H}$ at $i$. Third, `IsArchHolomorphicAt w hw φ`, for a real infinite place $w$ of a number field $F$ and $φ\colon GL_2(\mathbb{A}_F)\to\mathbb{C}$, asserts that for *every* $g$ the function $z\mapsto(\operatorname{Im}z)^{-1}\,φ\bigl(g\cdot\iota_w(s_z)\bigr)$ is `MDifferentiable` for the model $\mathcal{I}(\mathbb{C})$ on the upper half-plane, where $s_z$ is the above section transported to $GL_2(F_w)$ along the inverse of the isometric isomorphism $F_w\cong\mathbb{R}$ and $\iota_w$ is the inclusion of the $w$-component into the adelic group; so the normalised Iwasawa descent of $φ$ at $w$ is holomorphic.
--
--   Fourth, `viaCompactCuspNotion` is an element of the project's `CuspidalityNotion` over $\mathbb{Z}[\sqrt{-2}]$: for $Φ$ a Hecke eigensystem over $F$ with coefficients in $\mathbb{Z}[\sqrt{-2}]$, `IsCusp F Φ` is the conjunction of (i) the existence of a *single* witness $R$ in the project's structure `SmoothCuspRealizationAt` at the pins `productionPinsCompact F` for the rescaled eigensystem $(Φ\circ\iota_0)^{\mathrm{raw}}$ (in which $b_v$ is divided by $\lvert N v\rvert$) whose underlying function satisfies, at every real place $w$, both the weight-one archimedean character condition `HasArchCharacterAt₀ F w (archWeightOneAt hw)` — equivariance $φ(g\,\iota_w(k))=\chi(k)φ(g)$ for $k$ in the determinant-one row-isometry subgroup, with $\chi$ the transported character $k\mapsto k_{00}+ik_{01}$ — and `IsArchHolomorphicAt w hw`; and (ii) the existence of a finite set $S$ of finite places with $Φ.b\,v=\chi_{-3}(N v)$ for $v\notin S$, where $\chi_{-3}(n)$ is $1,-1,0$ according as $n\equiv1,2,0\pmod 3$. Note that (i) demands one joint witness, not a property of all realisations, and that complex places are unconstrained. `viaCompactCuspNotion_isCusp_iff` is this unfolding by `Iff.rfl`, and `isArithCuspRealizableVia_of_viaCompactCuspNotion` extracts from `IsCusp` the weaker statement `IsArithCuspRealizableVia F (productionPinsCompact F) iotaZsqrtdNegTwo Φ`, i.e. mere nonemptiness of the realisation type, by forgetting the archimedean clauses.
--
--   **Relation to Mathlib.** The adelic automorphic machinery (carrier pins, smooth cuspidal realisations, Hecke eigensystems, row-isometry subgroups and archimedean weight characters) is the project's own; Mathlib supplies only the ambient ingredients used here, such as `Zsqrtd.lift`, `UpperHalfPlane`, `MDifferentiable`, adele and infinite-place completions, and `InfinitePlace.Completion.ringEquivRealOfIsReal`. The character $\chi_{-3}$ is defined elementarily by residues modulo $3$ rather than via Mathlib's quadratic characters.
--
--   **Where it is used.** This is the cuspidality notion against which the weight-one dihedral form attached to a Hecke character of $\mathbb{Q}(\sqrt{-3})$, with coefficients in $\mathbb{Z}[\sqrt{-2}]$, is recognised: clause (ii) pins the finite-place data through $\chi_{-3}$, while clause (i) pins a weight-one holomorphic archimedean realisation, excluding weight-one Maass realisations that the $SO(2)$-type alone would permit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ViaCompactCuspNotion.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup
open scoped Manifold

noncomputable section

namespace AutomorphicForm

def iotaZsqrtdNegTwo : ℤ√(-2) →+* ℂ :=
  Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * Complex.I, by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
      norm_num [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    calc ((Real.sqrt 2 : ℂ) * Complex.I) * ((Real.sqrt 2 : ℂ) * Complex.I)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * (Complex.I * Complex.I) := by
          ring
      _ = ((-2 : ℤ) : ℂ) := by rw [h2, Complex.I_mul_I]; norm_num⟩

@[simp] theorem iotaZsqrtdNegTwo_apply (z : ℤ√(-2)) :
    iotaZsqrtdNegTwo z = (z.re : ℂ) + (z.im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) := by
  simp [iotaZsqrtdNegTwo, Zsqrtd.lift]

noncomputable def iwasawaSectionGL (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by
    simp [Matrix.det_fin_two_of]
    exact z.im_ne_zero)

def IsArchHolomorphicAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

def viaCompactCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

theorem viaCompactCuspNotion_isCusp_iff {F : Type} [Field F] [NumberField F]
    (Φ : HeckeEigensystem F (ℤ√(-2))) :
    viaCompactCuspNotion.IsCusp F Φ ↔
      (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          IsArchHolomorphicAt w hw R.toFun)) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) :=
  Iff.rfl

theorem isArithCuspRealizableVia_of_viaCompactCuspNotion {F : Type} [Field F]
    [NumberField F] (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaCompactCuspNotion.IsCusp F Φ) :
    IsArithCuspRealizableVia F (productionPinsCompact F) iotaZsqrtdNegTwo Φ :=
  ⟨h.1.choose⟩

end AutomorphicForm

end


