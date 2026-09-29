-- Prove2me | Definitions.Def_AutomorphicForm_InducedSection
-- name    : AutomorphicForm_InducedSection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/9a7ceb91-77fb-55c3-876f-dcdc080a26e3
-- title:
--   Induced sections for adelic Borel character pairs
-- statement:
--   Fix a Dedekind domain $R$ with fraction field $K$ and work with the adele ring $\mathbb{A} =$ `AdeleRing R K` and the group $G = \mathrm{GL}_2(\mathbb{A})$ (`AdelicGL2 R K`). For two monoid homomorphisms $\chi_1, \chi_2 : \mathbb{A}^\times \to \mathbb{C}^\times$, the predicate `IsInducedSection` on a function $\varphi : G \to \mathbb{C}$ asserts the transformation law
--   $$\varphi(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$$
--   for every $b$ in the adelic Borel subgroup and every $g \in G$. Here the Borel subgroup is the project's `borelSubgroup`, defined as the subgroup of matrices whose $(1,0)$ entry vanishes, and $b_{00}$, $b_{11}$ are the diagonal entries regarded as units of $\mathbb{A}$ via the homomorphisms `borelDiagFst`, `borelDiagSnd` on that subgroup. No modulus factor $\delta^{1/2}$, normalisation of the complex parameters, growth, measurability or integrability condition enters the definition; it is purely the equivariance identity under left multiplication by Borel elements.
--
--   The remaining declarations record the elementary consequences. The zero function is an induced section for every pair. The function `chiDet R K χ`, namely $g \mapsto \chi(\det g)$, is multiplicative in $g$ (`chiDet_mul`) and is an induced section for the pair $(\chi,\chi)$, since the determinant of a Borel element is the product of its two diagonal entries. The set of induced sections for a fixed pair is realised as a $\mathbb{C}$-submodule `inducedSectionSubmodule` of the space of all functions $G \to \mathbb{C}$, with membership equivalent to the predicate by definition, and this submodule is stable under right translation $\varphi \mapsto (g \mapsto \varphi(gh))$ for any $h \in G$. Finally, an induced section is invariant under left multiplication by the unipotent matrices $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, $x \in \mathbb{A}$, and satisfies $\varphi(z\cdot g) = \chi_1(z)\chi_2(z)\varphi(g)$ for central scalars $z \in \mathbb{A}^\times$.
--
--   **Relation to Mathlib.** Mathlib has no notion of principal-series transformation law or of an adelic Borel subgroup; these are the project's own definitions, built on Mathlib's `Matrix.GeneralLinearGroup`, `Submodule` and `NumberField.AdeleRing`.
--
--   **Where it is used.** These definitions belong to the adelic $\mathrm{GL}_2$ scaffolding used on the automorphic side of the argument, beside the $L^2$-growth and central-character conditions of `IsLsXiFunction` and the constant-term/cuspidality predicates: induced sections describe the non-cuspidal, Borel-equivariant part of the relevant function spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_InducedSection.lean

import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AutomorphicForm

section InducedSection

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInducedSection (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL2 R K → ℂ) : Prop :=
  ∀ (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (g : AdelicGL2 R K),
    φ (b * g)
      = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * φ g

variable {R K}

theorem isInducedSection_zero (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ₁ χ₂ (fun _ => (0 : ℂ)) := by
  intro b hb g
  simp

theorem chiDet_mul (χ : (AdeleRing R K)ˣ →* ℂˣ) (x y : AdelicGL2 R K) :
    chiDet R K χ (x * y) = chiDet R K χ x * chiDet R K χ y := by
  unfold chiDet
  rw [map_mul, map_mul, Units.val_mul]

theorem isInducedSection_chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ χ (chiDet R K χ) := by
  intro b hb g
  rw [chiDet_mul]
  congr 1
  show chiDet R K χ b = _
  unfold chiDet
  rw [det_borel_eq_diag_mul hb, map_mul, Units.val_mul]

def inducedSectionSubmodule (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) where
  carrier := {φ | IsInducedSection R K χ₁ χ₂ φ}
  zero_mem' := isInducedSection_zero χ₁ χ₂
  add_mem' := by
    intro φ ψ hφ hψ b hb g
    show φ (b * g) + ψ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (φ g + ψ g)
    rw [hφ b hb g, hψ b hb g]
    ring
  smul_mem' := by
    intro c φ hφ b hb g
    show c * φ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (c * φ g)
    rw [hφ b hb g]
    ring

@[simp] theorem mem_inducedSectionSubmodule_iff (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ)
    {φ : AdelicGL2 R K → ℂ} :
    φ ∈ inducedSectionSubmodule χ₁ χ₂ ↔ IsInducedSection R K χ₁ χ₂ φ := Iff.rfl

theorem IsInducedSection.rightTranslate {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (h : AdelicGL2 R K) :
    IsInducedSection R K χ₁ χ₂ (fun g => φ (g * h)) := by
  intro b hb g
  show φ (b * g * h) = _
  rw [mul_assoc, hφ b hb (g * h)]

theorem rightTranslate_mem_inducedSectionSubmodule {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : φ ∈ inducedSectionSubmodule χ₁ χ₂) (h : AdelicGL2 R K) :
    (fun g => φ (g * h)) ∈ inducedSectionSubmodule χ₁ χ₂ :=
  IsInducedSection.rightTranslate hφ h

theorem isInducedSection_unipotent_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (x : AdeleRing R K)
    (g : AdelicGL2 R K) :
    φ (unipotentGL2 x * g) = φ g := by
  rw [hφ (unipotentGL2 x) (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2]
  simp

theorem isInducedSection_centralScalar_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL2 R K) :
    φ (centralScalar R K z * g) = ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ (centralScalar R K z) (centralScalar_mem_adelicBorel R K z) g,
    borelDiagFst_centralScalar R K z (centralScalar_mem_adelicBorel R K z),
    borelDiagSnd_centralScalar R K z (centralScalar_mem_adelicBorel R K z)]
end InducedSection

end AutomorphicForm


