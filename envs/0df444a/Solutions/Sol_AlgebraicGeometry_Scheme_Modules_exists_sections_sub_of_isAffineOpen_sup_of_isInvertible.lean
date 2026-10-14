-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_sections_sub_of_isAffineOpen_sup_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T19:31:13.352438+00:00
-- url     : https://prove2.me/submissions/597b3dfd-ba8b-401c-976c-86efa2ca6176

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Order
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.LinearMap.Basic
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_power_smul_restrict_of_isAffineOpen_of_isInvertible

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace AlgebraicGeometry.Scheme.AffineExactness
open CategoryTheory Opposite
universe u
variable {X : Scheme.{u}}

/-- Functions whose nonvanishing locus is contained in a specified open. -/
def supportedIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {f | X.basicOpen f ≤ U}
  zero_mem' := by simp
  add_mem' := fun hf hg => (X.basicOpen_add_le _ _).trans (sup_le hf hg)
  smul_mem' := by
    intro a f hf
    change X.basicOpen (a * f) ≤ U
    rw [X.basicOpen_mul]
    exact inf_le_right.trans hf

/-- An affine open covered by two opens has complementary principal refinements. -/
theorem exists_complementary_basicOpens (U V W : X.Opens) (hW : IsAffineOpen W)
    (hcover : U ⊔ V = W) :
    ∃ f g : Γ(X, W), X.basicOpen f ≤ U ∧ X.basicOpen g ≤ V ∧ f + g = 1 := by
  let I := supportedIdeal W U
  let J := supportedIdeal W V
  have hsup : I ⊔ J = ⊤ := by
    have hs : Ideal.span ((I ⊔ J : Ideal Γ(X, W)) : Set Γ(X, W)) = ⊤ := by
      apply hW.self_le_iSup_basicOpen_iff.mp
      intro x hx
      have h : x ∈ U ⊔ V := by rw [hcover]; exact hx
      rcases h with hxU | hxV
      · obtain ⟨f, hfU, hxf⟩ := hW.exists_basicOpen_le ⟨x, hxU⟩ hx
        have hf : f ∈ I ⊔ J := Submodule.mem_sup_left hfU
        exact (le_iSup (fun f : (I ⊔ J : Ideal Γ(X, W)) => X.basicOpen f.val) ⟨f, hf⟩) hxf
      · obtain ⟨g, hgV, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
        have hg : g ∈ I ⊔ J := Submodule.mem_sup_right hgV
        exact (le_iSup (fun g : (I ⊔ J : Ideal Γ(X, W)) => X.basicOpen g.val) ⟨g, hg⟩) hxg
    simpa only [Ideal.span_eq] using hs
  have h1 : (1 : Γ(X, W)) ∈ I ⊔ J := by rw [hsup]; trivial
  obtain ⟨f, hf, g, hg, hfg⟩ := Submodule.mem_sup.mp h1
  exact ⟨f, g, hf, hg, hfg⟩

theorem basicOpen_cover_of_add_eq_one {W : X.Opens} (f g : Γ(X, W)) (hfg : f + g = 1) :
    X.basicOpen f ⊔ X.basicOpen g = W := by
  apply le_antisymm (sup_le (X.basicOpen_le f) (X.basicOpen_le g))
  simpa only [hfg, X.basicOpen_one] using X.basicOpen_add_le f g

end AlgebraicGeometry.Scheme.AffineExactness

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.AffineExactness
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules)

abbrev rM {U V : X.Opens} (h : V ≤ U) : Γ(M, U) →+ Γ(M, V) :=
  (M.presheaf.map (homOfLE h).op).hom

abbrev rO {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp] theorem rM_comp {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V) (s : Γ(M, U)) :
    rM M hVW (rM M hUV s) = rM M (hVW.trans hUV) s := by
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem rO_comp {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V) (f : Γ(X, U)) :
    rO hVW (rO hUV f) = rO (hVW.trans hUV) f := by
  change X.presheaf.map _ (X.presheaf.map _ f) = X.presheaf.map _ f
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem rM_self {U : X.Opens} (h : U ≤ U) (s : Γ(M, U)) : rM M h s = s := by
  change M.presheaf.map (𝟙 (op U)) s = s
  simp

@[simp] theorem rM_smul {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (s : Γ(M, U)) :
    rM M h (f • s) = rO h f • rM M h s := M.map_smul (homOfLE h) f s

/-- Gluing two compatible sections on their union, with an explicit ambient domain. -/
theorem glue {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W) (hcover : U ⊔ V = W)
    (s : Γ(M, U)) (t : Γ(M, V))
    (hc : rM M inf_le_left s = rM M inf_le_right t) :
    ∃ z : Γ(M, W), rM M hU z = s ∧ rM M hV z = t := by
  let A : Bool → X.Opens := fun b => if b then V else U
  let sf : ∀ b, Γ(M, A b) := fun b => by cases b; exact s; exact t
  have compatible : TopCat.Presheaf.IsCompatible M.presheaf A sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hc
    · apply (ConcreteCategory.bijective_of_isIso
        (M.presheaf.map (eqToHom (inf_comm U V)).op)).injective
      change rM M (inf_comm U V).le (rM M (inf_le_left : V ⊓ U ≤ V) t) =
        rM M (inf_comm U V).le (rM M (inf_le_right : V ⊓ U ≤ U) s)
      simpa only [rM_comp] using hc.symm
    · rfl
  have cover : W ≤ iSup A := by
    rw [iSup_bool_eq]
    change W ≤ V ⊔ U
    rw [sup_comm, hcover]
  let incl : ∀ b, A b ⟶ W := fun b => by cases b; exact homOfLE hU; exact homOfLE hV
  obtain ⟨z, hz, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    A W incl cover sf compatible
  exact ⟨z, hz false, hz true⟩

/-- A splitting on a two-open refinement extends to a splitting on the original cover. -/
theorem split_of_refinement (U V A B : X.Opens) (hA : A ≤ U) (hB : B ≤ V)
    (hcover : A ⊔ B = U ⊔ V) (s : Γ(M, U ⊓ V))
    (a : Γ(M, A)) (b : Γ(M, B))
    (hab : rM M inf_le_right b - rM M inf_le_left a =
      rM M (inf_le_inf hA hB) s) :
    ∃ a' : Γ(M, U), ∃ b' : Γ(M, V), rM M inf_le_right b' - rM M inf_le_left a' = s := by
  have coverU : A ⊔ (U ⊓ B) = U := by
    apply le_antisymm (sup_le hA inf_le_left)
    intro x hxU
    have hx : x ∈ A ⊔ B := by rw [hcover]; exact Or.inl hxU
    rcases hx with hxA | hxB
    · exact Or.inl hxA
    · exact Or.inr ⟨hxU, hxB⟩
  let a₁ : Γ(M, U ⊓ B) := rM M inf_le_right b - rM M (inf_le_inf le_rfl hB) s
  have compatU : rM M inf_le_left a = rM M inf_le_right a₁ := by
    have h := congrArg (rM M (show A ⊓ (U ⊓ B) ≤ A ⊓ B by order)) hab
    simp only [map_sub, rM_comp] at h
    dsimp only [a₁]
    simp only [map_sub, rM_comp]
    rw [← h]
    abel
  obtain ⟨a', ha', ha₁⟩ := glue M hA inf_le_left coverU a a₁ compatU
  have coverV : (U ⊓ V) ⊔ B = V := by
    apply le_antisymm (sup_le inf_le_right hB)
    intro x hxV
    have hx : x ∈ A ⊔ B := by rw [hcover]; exact Or.inr hxV
    rcases hx with hxA | hxB
    · exact Or.inl ⟨hA hxA, hxV⟩
    · exact Or.inr hxB
  let b₀ : Γ(M, U ⊓ V) := rM M inf_le_left a' + s
  have compatV : rM M inf_le_left b₀ = rM M inf_le_right b := by
    have h := congrArg (rM M (show (U ⊓ V) ⊓ B ≤ U ⊓ B by order)) ha₁
    simp only [a₁, map_sub, rM_comp] at h
    dsimp only [b₀]
    simp only [map_add, rM_comp]
    rw [h]
    abel
  obtain ⟨b', hb₀, hb'⟩ := glue M inf_le_right hB coverV b₀ b compatV
  refine ⟨a', b', ?_⟩
  rw [hb₀]
  dsimp only [b₀]
  abel

end AlgebraicGeometry.Scheme.AffineExactness

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.Scheme.AffineExactness

/-- Clearing a common denominator and a Bezout identity split a two-term cocycle. -/
theorem split_by_bezout
    {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (r₀ : A →ₗ[R] C) (r₁ : B →ₗ[R] C) (f g : R) (hfg : IsCoprime f g)
    (n : ℕ) (s : C) (a₀ : A) (b₀ : B)
    (ha : r₀ a₀ = (f * g) ^ n • s) (hb : r₁ b₀ = (f * g) ^ n • s)
    (hfA : Function.Surjective (fun a : A => f ^ n • a))
    (hgB : Function.Surjective (fun b : B => g ^ n • b))
    (hfC : Function.Injective (fun z : C => f ^ n • z))
    (hgC : Function.Injective (fun z : C => g ^ n • z)) :
    ∃ a : A, ∃ b : B, r₁ b - r₀ a = s := by
  obtain ⟨a, hfa⟩ := hfA a₀
  obtain ⟨b, hgb⟩ := hgB b₀
  have ha' : r₀ a = g ^ n • s := by
    apply hfC
    calc
      f ^ n • r₀ a = r₀ (f ^ n • a) := (map_smul r₀ _ _).symm
      _ = (f * g) ^ n • s := (congrArg r₀ hfa).trans ha
      _ = f ^ n • (g ^ n • s) := by rw [mul_pow, mul_smul]
  have hb' : r₁ b = f ^ n • s := by
    apply hgC
    calc
      g ^ n • r₁ b = r₁ (g ^ n • b) := (map_smul r₁ _ _).symm
      _ = (f * g) ^ n • s := (congrArg r₁ hgb).trans hb
      _ = g ^ n • (f ^ n • s) := by rw [mul_pow, mul_comm, mul_smul]
  obtain ⟨u, v, huv⟩ := hfg.pow (m := n) (n := n)
  refine ⟨-(v • a), u • b, ?_⟩
  rw [map_smul, map_neg, map_smul, ha', hb', sub_neg_eq_add,
    smul_smul, smul_smul, ← add_smul, huv, one_smul]

end AlgebraicGeometry.Scheme.AffineExactness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.AffineExactness
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules)

@[reducible] def sectionsOver {W U : X.Opens} (h : U ≤ W) : Module Γ(X, W) Γ(M, U) :=
  Module.compHom Γ(M, U) (rO h)

def rLinear {W U V : X.Opens} (hU : U ≤ W) (hV : V ≤ W) (h : V ≤ U) :
    letI := sectionsOver M hU; letI := sectionsOver M hV
    Γ(M, U) →ₗ[Γ(X, W)] Γ(M, V) :=
  letI := sectionsOver M hU; letI := sectionsOver M hV
  { toFun := rM M h
    map_add' := map_add _
    map_smul' := fun r s => by
      change rM M h (rO hU r • s) = rO hV r • rM M h s
      rw [rM_smul, rO_comp] }

theorem isUnit_restrict {W U : X.Opens} (f : Γ(X, W)) (h : U ≤ X.basicOpen f) :
    IsUnit (rO (h.trans (X.basicOpen_le f)) f) := by
  have hf : IsUnit (rO (X.basicOpen_le f) f) :=
    X.toRingedSpace.isUnit_res_basicOpen f
  simpa only [rO_comp] using hf.map (rO h)

theorem pow_smul_bijective {W U : X.Opens} (f : Γ(X, W)) (hU : U ≤ W)
    (h : U ≤ X.basicOpen f) (n : ℕ) :
    letI := sectionsOver M hU
    Function.Bijective (fun s : Γ(M, U) => f ^ n • s) := by
  letI := sectionsOver M hU
  change Function.Bijective (fun s : Γ(M, U) => (rO hU (f ^ n)) • s)
  rw [map_pow]
  exact ((isUnit_restrict f h).pow n).smul_bijective

/-- The sole geometric property used below: a power clears a principal-open denominator. -/
def ClearsDenominators : Prop :=
  ∀ (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (s : Γ(M, X.basicOpen f)),
    ∃ (n : ℕ) (t : Γ(M, W)), rM M (X.basicOpen_le f) t =
      (rO (X.basicOpen_le f) f) ^ n • s

/-- Complementary principal opens have surjective restriction difference. -/
theorem split_basicOpens (hclear : ClearsDenominators M)
    (W : X.Opens) (hW : IsAffineOpen W) (f g : Γ(X, W)) (hfg : f + g = 1)
    (s : Γ(M, X.basicOpen f ⊓ X.basicOpen g)) :
    ∃ a : Γ(M, X.basicOpen f), ∃ b : Γ(M, X.basicOpen g),
      rM M inf_le_right b - rM M inf_le_left a = s := by
  let A := X.basicOpen f
  let B := X.basicOpen g
  let T := A ⊓ B
  have hf : A ≤ W := X.basicOpen_le f
  have hg : B ≤ W := X.basicOpen_le g
  have hT : T ≤ W := inf_le_left.trans hf
  have hprod : X.basicOpen (f * g) = T := X.basicOpen_mul f g
  obtain ⟨n, t, ht⟩ := hclear W hW (f * g) (rM M hprod.le s)
  have ht' := congrArg (rM M hprod.ge) ht
  simp only [rM_smul, map_pow, rM_comp, rO_comp, rM_self] at ht'
  letI := sectionsOver M hf
  letI := sectionsOver M hg
  letI := sectionsOver M hT
  let r₀ := rLinear M hf hT (inf_le_left : T ≤ A)
  let r₁ := rLinear M hg hT (inf_le_right : T ≤ B)
  have ha : r₀ (rM M hf t) = (f * g) ^ n • s := by
    change rM M inf_le_left (rM M hf t) = rO hT ((f * g) ^ n) • s
    simpa only [rM_comp, map_pow] using ht'
  have hb : r₁ (rM M hg t) = (f * g) ^ n • s := by
    change rM M inf_le_right (rM M hg t) = rO hT ((f * g) ^ n) • s
    simpa only [rM_comp, map_pow] using ht'
  have coprime : IsCoprime f g := ⟨1, 1, by simpa only [one_mul] using hfg⟩
  exact split_by_bezout r₀ r₁ f g coprime n s (rM M hf t) (rM M hg t) ha hb
    (pow_smul_bijective M f hf le_rfl n).surjective
    (pow_smul_bijective M g hg le_rfl n).surjective
    (pow_smul_bijective M f hT inf_le_left n).injective
    (pow_smul_bijective M g hT inf_le_right n).injective

/-- Principal splitting and sheaf gluing prove exactness for an arbitrary two-open cover. -/
theorem split_affine_union (hclear : ClearsDenominators M)
    (U V : X.Opens) (hUV : IsAffineOpen (U ⊔ V)) (s : Γ(M, U ⊓ V)) :
    ∃ a : Γ(M, U), ∃ b : Γ(M, V), rM M inf_le_right b - rM M inf_le_left a = s := by
  obtain ⟨f, g, hf, hg, hfg⟩ := exists_complementary_basicOpens U V (U ⊔ V) hUV rfl
  obtain ⟨a, b, hab⟩ := split_basicOpens M hclear (U ⊔ V) hUV f g hfg
    (rM M (inf_le_inf hf hg) s)
  exact split_of_refinement M U V (X.basicOpen f) (X.basicOpen g) hf hg
    (basicOpen_cover_of_add_eq_one f g hfg) s a b hab

end AlgebraicGeometry.Scheme.AffineExactness

set_option autoImplicit false
set_option maxHeartbeats 2000000
open AlgebraicGeometry CategoryTheory Opposite
universe u

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U V : X.Opens) (hUV : IsAffineOpen (U ⊔ V))
    (s : Γ(M, U ⊓ V)) :
    ∃ s₀ : Γ(M, U), ∃ s₁ : Γ(M, V),
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s₁ -
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s₀ = s := by
  apply Scheme.AffineExactness.split_affine_union M ?_ U V hUV s
  intro W hW f t
  exact Scheme.Modules.exists_power_smul_restrict_of_isAffineOpen_of_isInvertible M hM W hW f t
