-- Prove2me | Definitions.Def_BundleGerbeStable_Coefficients
-- name    : BundleGerbeStable_Coefficients
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:20.431906+00:00
-- url     : https://prove2.me/theorems/c703051f-294d-495c-b4a8-f0421cb48add
-- title:
--   The coefficient presheaves; $H^3(M,\mathbb Z)$ and $H^2(M,\mathbb C^\times)$
-- statement:
--   Three presheaves on $M$: the **locally constant $\mathbb Z$-valued** functions, the **smooth $\mathbb C$-valued** functions, and the **smooth $\mathbb C^\times$-valued** functions, written additively. With them,
--   $$H^3(M,\mathbb Z):=\text{Čech } H^3 \text{ of locally constant } \mathbb Z,\qquad H^2(M,\mathbb C^\times):=\text{Čech } H^2\text{ of smooth } \mathbb C^\times.$$
--
--   These are the groups of the paper's isomorphism $H^2(M,\mathbb C^\times)\simeq H^3(M,\mathbb Z)$.
--
--   **Formalization Note.** With arbitrary $\mathbb Z$-valued functions, or arbitrary $\mathbb C^\times$-valued functions, the Čech groups would vanish. So locally constant and smooth are required. In the additive notation the zero of $H^2(M,\mathbb C^\times)$ is the class of $g=1$. Smoothness is `DSmooth` on the open subset with its subspace diffeology, which on a manifold is the usual smoothness.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_Cech

open Diffeology TopologicalSpace ContDiff

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M]

/-- The inclusion of a smaller open set into a larger one. -/
def inclOpens {U V : Opens M} (h : U ≤ V) (x : U) : V := ⟨x.1, h x.2⟩

/-- The presheaf of **locally constant ℤ-valued functions**. With arbitrary `ℤ`-valued functions the
Čech groups would vanish. -/
def locConstZ (M : Type u) [TopologicalSpace M] : AbPresheaf M where
  F U := LocallyConstant U ℤ
  res h := LocallyConstant.comapAddMonoidHom
    ⟨inclOpens h, Continuous.subtype_mk continuous_subtype_val _⟩
  res_id _ := by ext; rfl
  res_comp _ _ _ := by ext; rfl

variable [DiffeologicalSpace M]

theorem dSmooth_inclOpens {U V : Opens M} (h : U ≤ V) : DSmooth (inclOpens h) :=
  fun _ _ hp ↦ hp

/-- The smooth `ℂ`-valued functions on `U`, for the subspace diffeology of `U ⊂ M`. -/
def smoothCFun (U : Opens M) : AddSubgroup (U → ℂ) where
  carrier := {f | DSmooth f}
  zero_mem' := dSmooth_const
  add_mem' := fun {f g} hf hg n p hp ↦
    (show ContDiff ℝ ∞ (f ∘ p) from hf n p hp).add
      (show ContDiff ℝ ∞ (g ∘ p) from hg n p hp)
  neg_mem' := fun {f} hf n p hp ↦
    (show ContDiff ℝ ∞ (f ∘ p) from hf n p hp).neg

/-- The presheaf of **smooth ℂ-valued functions**. -/
def smoothC (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] : AbPresheaf M where
  F U := smoothCFun U
  res h := AddMonoidHom.mk'
    (fun s ↦ ⟨s.1 ∘ inclOpens h, s.2.comp (dSmooth_inclOpens h)⟩) (fun _ _ ↦ rfl)
  res_id _ := rfl
  res_comp _ _ _ := rfl

/-- The smooth `ℂˣ`-valued functions on `U`. -/
def smoothUnitsFun (U : Opens M) : Subgroup (U → ℂˣ) where
  carrier := {f | DSmooth f}
  one_mem' := dSmooth_const
  mul_mem' := fun hf hg ↦
    dSmooth_units_mul.comp (DSmooth.prodMk' hf hg)
  inv_mem' := fun hf ↦ dSmooth_units_inv.comp hf

/-- The presheaf of **smooth ℂˣ-valued functions**, written additively as the coefficients of Čech
cochains (arXiv:math/9908135v1, §2, p.3: `H²(M, ℂ×)`). The zero section is the constant `1`. -/
def smoothUnits (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] : AbPresheaf M where
  F U := Additive (smoothUnitsFun U)
  res h := AddMonoidHom.mk'
    (fun s ↦ Additive.ofMul
      ⟨(Additive.toMul s).1 ∘ inclOpens h, (Additive.toMul s).2.comp (dSmooth_inclOpens h)⟩)
    (fun _ _ ↦ rfl)
  res_id _ := rfl
  res_comp _ _ _ := rfl

/-- The value in `ℂˣ` of a section of `smoothUnits`. -/
def unitsVal {U : Opens M} (s : (smoothUnits M).F U) (x : U) : ℂˣ :=
  (Additive.toMul s).1 x

/-- The value in `ℂ` of a section of `smoothC`. -/
def complexVal {U : Opens M} (s : (smoothC M).F U) (x : U) : ℂ := s.1 x

/-- The value in `ℤ` of a section of `locConstZ`. -/
def intVal {U : Opens M} (s : (locConstZ M).F U) (x : U) : ℤ :=
  (show LocallyConstant U ℤ from s) x

/-- `H³(M, ℤ)` (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*,
arXiv:math/9908135v1, §2, p.3), Čech cohomology with coefficients in the locally constant `ℤ`-valued
functions. -/
abbrev H3 (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] : Type u :=
  cechH (locConstZ M) 3

/-- `H²(M, ℂ×)` (arXiv:math/9908135v1, §2, p.3), Čech cohomology with coefficients in the smooth
`ℂˣ`-valued functions. -/
abbrev H2Cx (M : Type u) [TopologicalSpace M] [DiffeologicalSpace M] : Type u :=
  cechH (smoothUnits M) 2

end BundleGerbeStable


