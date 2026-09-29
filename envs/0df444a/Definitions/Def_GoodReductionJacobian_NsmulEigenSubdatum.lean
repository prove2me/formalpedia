-- Prove2me | Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
-- name    : GoodReductionJacobian_NsmulEigenSubdatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/09e771bb-fb81-5006-976d-88e1b0cbd80b
-- title:
--   Deck action and eigensections along multiplication by n
-- statement:
--   Throughout, $R$ is a commutative ring, $f : A \to \operatorname{Spec} R$ a morphism of schemes carrying a relative group law $L$, and $n$ a natural number; $L.schemeNsmul n : A \to A$ is the $n$-fold multiplication morphism and, for an $R$-point $x$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f`), $L.translate x : A \to A$ is the translation obtained from the group law applied to the identity point of $A$ and to $f$ followed by $x$. For an $x$ satisfying $T_x$ followed by $[n]$ equals $[n]$, `deckApp` is the ring endomorphism of $\Gamma(A, [n]^{-1}U)$ obtained from $T_x$ by `appLE`, using that this identity forces $[n]^{-1}U \le T_x^{-1}([n]^{-1}U)$; accompanying lemmas record that it commutes with restriction along $U \le U'$, fixes sections pulled back along $[n]$, and fixes `nsmulConst n U r`, the image of $r \in R$ under the structure map $R \to \Gamma(A, [n]^{-1}U)$ attached to $[n]$ followed by $f$. Two further lemmas identify the $R$- and $\Gamma(A,U)$-actions on the datum `OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)` with multiplication by `nsmulConst` and by the `appLE`-image.
--
--   Under the standing hypothesis `hG` that every $x$ in `L.torsionSubset` of level $n$ satisfies the above identity, and for a function $\chi$ from $R$-points to $R$, `IsEigensection` asserts that $s \in \Gamma(A, [n]^{-1}U)$ satisfies `deckApp` of $x$ applied to $s$ equals `nsmulConst n U (χ x)` times $s$ for all such $x$. These sections form an $R$-submodule `eigenSubmodule`, stable under multiplication by sections of $\mathcal O_A$ over $U$ and under restriction; `eigenSubdatum` assembles them into an `OModulePresheaf` over $f$, with `eigenInclusion` the componentwise injective inclusion into the pushforward datum. Multiplication carries a $\chi$- and a $\psi$-eigensection to a $\chi\psi$-eigensection (`IsEigensection.mul`, `eigenMul`), and $1$ is a $1$-eigensection (`eigenOne`). Finally `IsNsmulCharacter χ` is the conjunction of three conditions: $\chi$ is $1$ outside the $n$-torsion subset, $\chi$ of the identity point is $1$, and $\chi$ is multiplicative on pairs of points of the $n$-torsion subset for the group law's multiplication; the constant function $1$ satisfies it.
--
--   **Relation to Mathlib.** Mathlib has no relative group law on a scheme over `Spec R`, and no presheaf-of-modules datum of the shape `OModulePresheaf`; both, and hence the eigen-submodules and eigen-datum built here, are the project's own notions.
--
--   **Where it is used.** These definitions belong to the infrastructure for relative group laws and the relative Picard functor used in the good-reduction analysis of Jacobians, where the direct image of the structure sheaf along multiplication by $n$ is decomposed according to characters of the $n$-torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_NsmulEigenSubdatum.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (n : ℕ)

theorem appLE_congr_hom {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V e' := by
  subst h; rfl

theorem preimage_le_preimage_preimage_of_comp_eq {X Y : Scheme.{u}} {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q)
    (U : Y.Opens) : q ⁻¹ᵁ U ≤ T ⁻¹ᵁ (q ⁻¹ᵁ U) := by
  change q ⁻¹ᵁ U ≤ (T ≫ q) ⁻¹ᵁ U
  rw [h]

theorem appLE_comp_appLE_of_comp_eq {X Y : Scheme.{u}} {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q)
    (U : Y.Opens) (V W : X.Opens) (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ T ⁻¹ᵁ V) (e₃ : W ≤ q ⁻¹ᵁ U) :
    q.appLE U V e₁ ≫ T.appLE V W e₂ = q.appLE U W e₃ := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom h U W _ e₃

def deckApp (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) (U : A.Opens) :
    Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) ⟶ Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) :=
  (L.translate x).appLE ((L.schemeNsmul n) ⁻¹ᵁ U) ((L.schemeNsmul n) ⁻¹ᵁ U)
    (preimage_le_preimage_preimage_of_comp_eq hx U)

theorem deckApp_def (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) (U : A.Opens) :
    L.deckApp n x hx U = (L.translate x).appLE ((L.schemeNsmul n) ⁻¹ᵁ U) ((L.schemeNsmul n) ⁻¹ᵁ U)
      (preimage_le_preimage_preimage_of_comp_eq hx U) := rfl

theorem deckApp_map (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) {U U' : A.Opens} (h : U ≤ U') :
    L.deckApp n x hx U' ≫ A.presheaf.map (homOfLE ((Opens.map (L.schemeNsmul n).base).monotone h)).op =
      A.presheaf.map (homOfLE ((Opens.map (L.schemeNsmul n).base).monotone h)).op ≫ L.deckApp n x hx U := by
  simp only [deckApp_def, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem deckApp_appLE (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) (U : A.Opens)
    (a : Γ(A, U)) :
    (L.deckApp n x hx U).hom (((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a) =
      ((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a := by
  change ((L.schemeNsmul n).appLE U _ le_rfl ≫ L.deckApp n x hx U).hom a = _
  rw [deckApp_def, appLE_comp_appLE_of_comp_eq hx U _ _ le_rfl _ le_rfl]

def nsmulConst (U : A.Opens) (r : R) : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeNsmul n ≫ f) ((L.schemeNsmul n) ⁻¹ᵁ U)
  algebraMap R _ r

theorem nsmulConst_def (U : A.Opens) (r : R) :
    L.nsmulConst n U r = ((L.schemeNsmul n ≫ f).appLE ⊤ ((L.schemeNsmul n) ⁻¹ᵁ U) le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) := rfl

theorem pushforwardUnit_smul_eq (U : A.Opens) (r : R)
    (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) :
    r • s = (show (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U from
      L.nsmulConst n U r * (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s)) := rfl

theorem pushforwardUnit_sections_smul_eq (U : A.Opens) (a : Γ(A, U))
    (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) :
    a • s = (show (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U from
      ((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a *
        (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s)) := rfl

theorem map_nsmulConst {U U' : A.Opens} (h : U ≤ U') (r : R) :
    (A.presheaf.map (homOfLE ((Opens.map (L.schemeNsmul n).base).monotone h)).op).hom (L.nsmulConst n U' r) =
      L.nsmulConst n U r :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeNsmul n ≫ f) ((L.schemeNsmul n) ⁻¹ᵁ U)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeNsmul n ≫ f) ((L.schemeNsmul n) ⁻¹ᵁ U')
  (Scheme.TwoAffineOpenCover.restrictAlgHom (L.schemeNsmul n ≫ f)
    ((Opens.map (L.schemeNsmul n).base).monotone h)).commutes r

theorem deckApp_nsmulConst (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) (U : A.Opens) (r : R) :
    (L.deckApp n x hx U).hom (L.nsmulConst n U r) = L.nsmulConst n U r := by
  have hx' : L.translate x ≫ (L.schemeNsmul n ≫ f) = L.schemeNsmul n ≫ f := by
    rw [← Category.assoc, hx]
  change ((L.schemeNsmul n ≫ f).appLE ⊤ _ le_top ≫ L.deckApp n x hx U).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
    ((L.schemeNsmul n ≫ f).appLE ⊤ _ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)
  rw [deckApp_def, appLE_comp_appLE_of_comp_eq hx' ⊤ _ _ le_top _ le_top]

section Eigen

variable (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n,
    L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
  (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R)

def IsEigensection (U : A.Opens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)) : Prop :=
  ∀ (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n),
    (L.deckApp n x (hG x hx) U).hom s = L.nsmulConst n U (χ x) * s

theorem isEigensection_iff (U : A.Opens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)) :
    L.IsEigensection n hG χ U s ↔ ∀ (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
      (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n),
      (L.deckApp n x (hG x hx) U).hom s = L.nsmulConst n U (χ x) * s :=
  Iff.rfl

def eigenSubmodule (U : A.Opens) :
    Submodule R ((OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) where
  carrier := {s | L.IsEigensection n hG χ U s}
  zero_mem' := by
    change L.IsEigensection n hG χ U (0 : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U))
    intro x hx
    rw [map_zero, mul_zero]
  add_mem' := fun {s t} hs ht => by
    change L.IsEigensection n hG χ U
      ((show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s) + (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t))
    intro x hx
    rw [map_add, hs x hx, ht x hx, mul_add]
  smul_mem' := fun r s hs => by
    change L.IsEigensection n hG χ U (L.nsmulConst n U r * (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s))
    intro x hx
    rw [map_mul, deckApp_nsmulConst, hs x hx, mul_left_comm]

theorem mem_eigenSubmodule_iff (U : A.Opens) (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) :
    s ∈ L.eigenSubmodule n hG χ U ↔ L.IsEigensection n hG χ U s :=
  Iff.rfl

theorem sections_smul_mem_eigenSubmodule (U : A.Opens) (a : Γ(A, U))
    (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) (hs : s ∈ L.eigenSubmodule n hG χ U) :
    a • s ∈ L.eigenSubmodule n hG χ U := by
  change L.IsEigensection n hG χ U (((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a *
    (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s))
  intro x hx
  rw [map_mul, deckApp_appLE, hs x hx, mul_left_comm]

theorem res_mem_eigenSubmodule {U U' : A.Opens} (h : U ≤ U')
    (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U') (hs : s ∈ L.eigenSubmodule n hG χ U') :
    (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res h s ∈ L.eigenSubmodule n hG χ U := by
  change L.IsEigensection n hG χ U
    ((A.presheaf.map (homOfLE ((Opens.map (L.schemeNsmul n).base).monotone h)).op).hom
      (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U') from s))
  intro x hx
  have hnat := congrArg (fun φ => φ.hom (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U') from s))
    (L.deckApp_map n x (hG x hx) h)
  simp only [CommRingCat.comp_apply] at hnat
  rw [← hnat, hs x hx, map_mul, L.map_nsmulConst n h]

def eigenSubdatum : OModulePresheaf f where
  obj U := L.eigenSubmodule n hG χ U
  module U := inferInstance
  moduleSections U := OModulePresheaf.submoduleSections U _ (L.sections_smul_mem_eigenSubmodule n hG χ U)
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := OModulePresheaf.submoduleSections U _ (L.sections_smul_mem_eigenSubmodule n hG χ U)
    exact ⟨fun r a s => Subtype.ext (smul_assoc r a s.1)⟩
  res h := ((OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res h).restrict
    fun s hs => L.res_mem_eigenSubmodule n hG χ h s hs
  res_smul h a s := Subtype.ext ((OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res_smul h a s.1)
  res_refl U := LinearMap.ext fun s =>
    Subtype.ext (LinearMap.congr_fun ((OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res_refl U) s.1)
  res_comp h h' := LinearMap.ext fun s =>
    Subtype.ext (LinearMap.congr_fun ((OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res_comp h h') s.1)

@[simp] theorem eigenSubdatum_obj (U : A.Opens) :
    (L.eigenSubdatum n hG χ).obj U = L.eigenSubmodule n hG χ U := rfl

theorem eigenSubdatum_res_coe {U U' : A.Opens} (h : U ≤ U') (s : (L.eigenSubdatum n hG χ).obj U') :
    ((L.eigenSubdatum n hG χ).res h s).1 = (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).res h s.1 := rfl

theorem eigenSubdatum_smul_coe (U : A.Opens) (a : Γ(A, U)) (s : (L.eigenSubdatum n hG χ).obj U) :
    (a • s).1 = a • s.1 := rfl

def eigenInclusion :
    OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)) where
  app U := (L.eigenSubmodule n hG χ U).subtype
  app_smul _ _ _ := rfl
  naturality _ := rfl

@[simp] theorem eigenInclusion_app (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U) :
    (L.eigenInclusion n hG χ).app U s = s.1 := rfl

theorem eigenInclusion_injective (U : A.Opens) : Function.Injective ((L.eigenInclusion n hG χ).app U) :=
  Subtype.val_injective

theorem IsEigensection.mul {χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R} {U : A.Opens}
    {s t : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)} (hs : L.IsEigensection n hG χ U s) (ht : L.IsEigensection n hG ψ U t) :
    L.IsEigensection n hG (χ * ψ) U (s * t) := fun x hx => by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeNsmul n ≫ f) ((L.schemeNsmul n) ⁻¹ᵁ U)
  rw [map_mul, hs x hx, ht x hx, Pi.mul_apply]
  change _ = algebraMap R _ (χ x * ψ x) * (s * t)
  rw [map_mul]
  change _ = L.nsmulConst n U (χ x) * L.nsmulConst n U (ψ x) * (s * t)
  ring

theorem isEigensection_one_appLE (U : A.Opens) (a : Γ(A, U)) :
    L.IsEigensection n hG 1 U (((L.schemeNsmul n).appLE U ((L.schemeNsmul n) ⁻¹ᵁ U) le_rfl).hom a) := fun x hx => by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeNsmul n ≫ f) ((L.schemeNsmul n) ⁻¹ᵁ U)
  rw [deckApp_appLE, Pi.one_apply]
  change _ = algebraMap R _ 1 * _
  rw [map_one, _root_.one_mul]

theorem isEigensection_one_one (U : A.Opens) :
    L.IsEigensection n hG 1 U 1 := by
  have h := L.isEigensection_one_appLE n hG U 1
  rwa [map_one] at h

def eigenMul {χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R} {U : A.Opens}
    (s : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    (L.eigenSubdatum n hG (χ * ψ)).obj U :=
  ⟨(show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1) * (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1),
    IsEigensection.mul L n hG s.2 t.2⟩

theorem eigenMul_coe {χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R} {U : A.Opens}
    (s : (L.eigenSubdatum n hG χ).obj U) (t : (L.eigenSubdatum n hG ψ).obj U) :
    (L.eigenMul n hG s t).1 = (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from s.1) *
      (show Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U) from t.1) := rfl

def eigenOne (U : A.Opens) : (L.eigenSubdatum n hG 1).obj U :=
  ⟨(1 : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)), L.isEigensection_one_one n hG U⟩

theorem eigenOne_coe (U : A.Opens) :
    (L.eigenOne n hG U).1 = (1 : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)) := rfl

end Eigen

def IsNsmulCharacter (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R) : Prop :=
  (∀ x, x ∉ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n → χ x = 1) ∧
  χ (L.one (𝟙 (Spec (CommRingCat.of R)))) = 1 ∧
  ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, ∀ y ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n,
    χ (L.mul (𝟙 (Spec (CommRingCat.of R))) x y) = χ x * χ y

theorem isNsmulCharacter_iff (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R) :
    L.IsNsmulCharacter n χ ↔
      (∀ x, x ∉ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n → χ x = 1) ∧
      χ (L.one (𝟙 (Spec (CommRingCat.of R)))) = 1 ∧
      ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, ∀ y ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n,
        χ (L.mul (𝟙 (Spec (CommRingCat.of R))) x y) = χ x * χ y :=
  Iff.rfl

theorem isNsmulCharacter_one : L.IsNsmulCharacter n 1 :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ _ => (_root_.mul_one _).symm⟩

end GoodReductionJacobian.RelativeGroupLaw

end


