-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionFormsInjective
-- name    : Formalism_PieriBlockIdeals_LatticeInclusionFormsInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:46.356205+00:00
-- url     : https://prove2.me/theorems/0b51a30f-25d6-4488-838a-0da9b7c685a5
-- title:
--   Lattice Inclusion Forms Injective
-- statement:
--   Definitions and structural lemmas for Lattice Inclusion Forms Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LatticeInclusionFormsInjective.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace Formalism.CohomologicalDescent.AutomorphicFormLattices
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization
def TensorProductLattices : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) [∀ i, Module.Free k (B i)] (l : k)
    (e : ι → ℕ), l ∈ nonZeroDivisors k → (∀ i, LatIncl l (B i) (e i)) →
    Function.Injective (PiTensorProduct.map fun i => (B i).subtype) ∧
      ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B
def ExpBaseChange : Prop :=
  ∀ (k k' : Type) [CommRing k] [CommRing k'] [Algebra k k'] [Module.FaithfullyFlat k k']
    (A : Type) [AddCommGroup A] [Module k A] (B : Submodule k A) (l : k),
    Function.Injective (B.subtype.baseChange k') ∧
    (∀ J : ℕ, LatIncl (algebraMap k k' l) (LinearMap.range (B.subtype.baseChange k')) J ↔
      LatIncl l B J) ∧
    sInf {J : ℕ | LatIncl (algebraMap k k' l) (LinearMap.range (B.subtype.baseChange k')) J} =
      sInf {J : ℕ | LatIncl l B J}
section Defs
variable {G : Type} [Group G] {k : Type} [CommRing k]
def IsIntertw {H : Type} [Monoid H] {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] (ρ₁ : Representation k H W₁) (ρ₂ : Representation k H W₂)
    (φ : W₁ →ₗ[k] W₂) : Prop :=
  ∀ (κ : H) (w : W₁), φ (ρ₁ κ w) = ρ₂ κ (φ w)
def invMap {H : Type} [Group H] {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] {ρ₁ : Representation k H W₁} {ρ₂ : Representation k H W₂}
    (φ : W₁ →ₗ[k] W₂) (hφ : IsIntertw ρ₁ ρ₂ φ) : ρ₁.invariants →ₗ[k] ρ₂.invariants :=
  φ.restrict (fun w hw κ => by rw [← hφ, hw κ])
def mapM (Γ K : Subgroup G) {W₁ W₂ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] {ρ₁ : Representation k K W₁} {ρ₂ : Representation k K W₂}
    (φ : W₁ →ₗ[k] W₂) (hφ : IsIntertw ρ₁ ρ₂ φ) : AMFK k Γ K ρ₁ →ₗ[k] AMFK k Γ K ρ₂ :=
  (φ.compLeft G).restrict (fun f hf γ g κ => by
    show φ (f _) = ρ₂ κ⁻¹ (φ (f g))
    rw [hf γ g κ, hφ])
def GamAt (Γ K : Subgroup G) (x : G) : Subgroup G := Γ ⊓ K.map (MulAut.conj x).toMonoidHom
def stabK (Γ K : Subgroup G) (x : G) : Subgroup K :=
  Γ.comap ((MulAut.conj x).toMonoidHom.comp K.subtype)
def resTo {K : Type} [Group K] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (H : Subgroup K) : Representation k H W := MonoidHom.comp ρ H.subtype
def OrdersInvertible (k : Type) [CommRing k] (Γ K : Subgroup G) : Prop :=
  ∀ x : G, Finite (GamAt Γ K x) ∧ IsUnit ((Nat.card (GamAt Γ K x) : ℕ) : k)
theorem isIntertw_subtype {K : Subgroup G} {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (U : Submodule k W) (hU : IsStable ρ U) :
    IsIntertw (resRep ρ U hU) ρ U.subtype := fun _ _ => rfl
theorem isIntertw_rTensor {H : Type} [Monoid H] {W₁ W₂ Θ : Type} [AddCommGroup W₁] [Module k W₁]
    [AddCommGroup W₂] [Module k W₂] [AddCommGroup Θ] [Module k Θ]
    {ρ₁ : Representation k H W₁} {ρ₂ : Representation k H W₂} (θ : Representation k H Θ)
    {φ : W₁ →ₗ[k] W₂} (hφ : IsIntertw ρ₁ ρ₂ φ) :
    IsIntertw (ρ₁.tprod θ) (ρ₂.tprod θ) (φ.rTensor Θ) := by
  intro κ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [hφ κ a]
  | add a b ha hb => simp only [map_add, ha, hb]
def powSub {W : Type} [AddCommGroup W] [Module k W] (l : k) (c : ℕ) : Submodule k W :=
  LinearMap.range ((l ^ c) • (LinearMap.id : W →ₗ[k] W))
theorem isStable_powSub {K : Subgroup G} {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k K W) (l : k) (c : ℕ) : IsStable ρ (powSub (W := W) l c) := by
  rintro κ _ ⟨w, rfl⟩
  exact ⟨ρ κ w, by simp⟩
end Defs
def StabIso : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (x : G),
    ∃ e : GamAt Γ K x ≃* stabK Γ K x, ∀ γ, (((e γ : stabK Γ K x) : K) : G) = x⁻¹ * (γ : G) * x
def AMFKDecomp : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type) [AddCommGroup W]
    [Module k W] (ρ : Representation k K W) (s : ClassSet Γ K → G),
    (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∃ e : AMFK k Γ K ρ ≃ₗ[k] ((c : ClassSet Γ K) → (resTo ρ (stabK Γ K (s c))).invariants),
      ∀ f c, (e f c : W) = (f : G → W) (s c)
def LocIncl : Prop :=
  ∀ (T : Type) [CommRing T] (P' P : Type) [AddCommGroup P'] [Module T P'] [AddCommGroup P]
    [Module T P] (ι : P' →ₗ[T] P) (S : Submonoid T) (t : T) (J : ℕ),
    Function.Injective ι → (∀ x : P, t ^ J • x ∈ LinearMap.range ι) →
    Function.Injective (LocalizedModule.map S ι) ∧
      ∀ y : LocalizedModule S P, t ^ J • y ∈ LinearMap.range (LocalizedModule.map S ι)
def LatticeInclusionFormsInjective : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (B : Type) [AddCommGroup B]
    [Module k B] (ρ : Representation k K B) (A : Submodule k B) (hA : IsStable ρ A) (l : k) (J : ℕ),
    LatIncl l A J →
    (Function.Injective (mapM Γ K A.subtype (isIntertw_subtype ρ A hA)) ∧
      ∀ f : AMFK k Γ K ρ,
        l ^ J • f ∈ LinearMap.range (mapM Γ K A.subtype (isIntertw_subtype ρ A hA))) ∧
    ∀ (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K (resRep ρ A hA))]
      [Module T (AMFK k Γ K ρ)] [IsScalarTower k T (AMFK k Γ K ρ)]
      (ιT : AMFK k Γ K (resRep ρ A hA) →ₗ[T] AMFK k Γ K ρ) (S : Submonoid T),
      (∀ f, ιT f = mapM Γ K A.subtype (isIntertw_subtype ρ A hA) f) →
      Function.Injective (LocalizedModule.map S ιT) ∧
        ∀ y : LocalizedModule S (AMFK k Γ K ρ),
          (algebraMap k T l) ^ J • y ∈ LinearMap.range (LocalizedModule.map S ιT)
def TensorFreeModuleTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (B : Type) [AddCommGroup B]
    [Module k B] (ρ : Representation k K B) (Θ : Type) [AddCommGroup Θ] [Module k Θ]
    [Module.Free k Θ] (θ : Representation k K Θ) (A : Submodule k B) (hA : IsStable ρ A) (l : k)
    (J : ℕ), LatIncl l A J →
    (Function.Injective (A.subtype.rTensor Θ) ∧
      Function.Injective
        (mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA))) ∧
      ∀ f : AMFK k Γ K (ρ.tprod θ), l ^ J • f ∈ LinearMap.range
        (mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA)))) ∧
    ∀ (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ((resRep ρ A hA).tprod θ))]
      [Module T (AMFK k Γ K (ρ.tprod θ))] [IsScalarTower k T (AMFK k Γ K (ρ.tprod θ))]
      (ιT : AMFK k Γ K ((resRep ρ A hA).tprod θ) →ₗ[T] AMFK k Γ K (ρ.tprod θ)) (S : Submonoid T),
      (∀ f, ιT f =
        mapM Γ K (A.subtype.rTensor Θ) (isIntertw_rTensor θ (isIntertw_subtype ρ A hA)) f) →
      Function.Injective (LocalizedModule.map S ιT) ∧
        ∀ y : LocalizedModule S (AMFK k Γ K (ρ.tprod θ)),
          (algebraMap k T l) ^ J • y ∈ LinearMap.range (LocalizedModule.map S ιT)
def OrderBound : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L)
    (g : Matrix (Fin N) (Fin N) E), l.Prime → IsPrimitiveRoot ζ l →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 → g ^ l = 1 → g ≠ 1 → l - 1 ≤ N
def NoOrderL : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L)
    (Δ : Subgroup (GL (Fin N) E)), l.Prime → IsPrimitiveRoot ζ l →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 → Finite Δ → N + 1 < l →
    ¬ l ∣ Nat.card Δ
def CardUnit : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l n : ℕ), l.Prime →
    (l : O) ∈ IsLocalRing.maximalIdeal O → ¬ l ∣ n → IsUnit (n : O)
def InvExact : Prop :=
  ∀ (k : Type) [CommRing k] (H : Type) [Group H] [Finite H] (A B C : Type) [AddCommGroup A]
    [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k H A) (ρB : Representation k H B) (ρC : Representation k H C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    IsUnit ((Nat.card H : ℕ) : k) → Function.Exact f g → Function.Exact (invMap f hf) (invMap g hg)
def MLeftExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    Function.Injective f → Function.Exact f g →
    Function.Injective (mapM Γ K f hf) ∧ Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)
def MExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    OrdersInvertible k Γ K → Function.Exact f g →
    Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)
def MTExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B C : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρC : Representation k K C)
    (Θ : Type) [AddCommGroup Θ] [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ)
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρC g),
    OrdersInvertible k Γ K → Function.Exact f g →
    Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
      (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg))
def PointsLemmaAnyRank : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L) (G : Type) [Group G]
    (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 →
    N + 1 < l → Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    (∀ x : G, ¬ l ∣ Nat.card (GamAt Γ K x)) ∧
    ∀ (A B C : Type) [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C]
      [Module O C] (ρA : Representation O K A) (ρB : Representation O K B)
      (ρC : Representation O K C) (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : IsIntertw ρA ρB f)
      (hg : IsIntertw ρB ρC g), Function.Exact f g →
      Function.Exact (mapM Γ K f hf) (mapM Γ K g hg)
def FormsExactTypes : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (l N : ℕ) (ζ : L) (G : Type) [Group G]
    (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1 →
    N + 1 < l → Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    ∀ (A B C : Type) [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C]
      [Module O C] (ρA : Representation O K A) (ρB : Representation O K B)
      (ρC : Representation O K C) (Θ : Type) [AddCommGroup Θ] [Module O Θ] [Module.Free O Θ]
      (θ : Representation O K Θ) (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : IsIntertw ρA ρB f)
      (hg : IsIntertw ρB ρC g), Function.Exact f g →
      Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
        (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg))
def ShortExactFormsExact : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B Q : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup Q] [Module k Q]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρQ : Representation k K Q)
    (f : A →ₗ[k] B) (g : B →ₗ[k] Q) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρQ g),
    OrdersInvertible k Γ K → Function.Injective f → Function.Exact f g → Function.Surjective g →
    Function.Injective (mapM Γ K f hf) ∧ Function.Exact (mapM Γ K f hf) (mapM Γ K g hg) ∧
    Function.Surjective (mapM Γ K g hg) ∧
    ∃ e : (AMFK k Γ K ρB ⧸ LinearMap.range (mapM Γ K f hf)) ≃ₗ[k] AMFK k Γ K ρQ,
      ∀ φ, e (Submodule.Quotient.mk φ) = mapM Γ K g hg φ
def PowerScaledFormsEq : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (Q : Type)
    [AddCommGroup Q] [Module k Q] (ρ : Representation k K Q) (l : k) (c : ℕ),
    OrdersInvertible k Γ K →
    ∀ φ : G → Q, φ ∈ formsIn Γ K ρ (powSub l c) ↔ ∃ ψ ∈ AMFK k Γ K ρ, φ = l ^ c • ψ
def FiltrationFormsGraded : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (n : ℕ) (F Gr : ℕ → Type)
    [∀ j, AddCommGroup (F j)] [∀ j, Module k (F j)] [∀ j, AddCommGroup (Gr j)]
    [∀ j, Module k (Gr j)] (ρF : ∀ j, Representation k K (F j))
    (ρG : ∀ j, Representation k K (Gr j)) (i : ∀ j, F j →ₗ[k] F (j + 1))
    (p : ∀ j, F (j + 1) →ₗ[k] Gr j) (hi : ∀ j, IsIntertw (ρF j) (ρF (j + 1)) (i j))
    (hp : ∀ j, IsIntertw (ρF (j + 1)) (ρG j) (p j)) (T : Type) [CommRing T]
    [∀ j, Module T (AMFK k Γ K (ρF j))] [∀ j, Module T (AMFK k Γ K (ρG j))] (S : Submonoid T),
    Subsingleton (F 0) → (∀ j < n, Function.Injective (i j)) →
    (∀ j < n, Function.Exact (i j) (p j)) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K (ρF j)),
      mapM Γ K (i j) (hi j) (t • φ) = t • mapM Γ K (i j) (hi j) φ) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K (ρF (j + 1))),
      mapM Γ K (p j) (hp j) (t • φ) = t • mapM Γ K (p j) (hp j) φ) →
    (∀ j < n, Subsingleton (LocalizedModule S (AMFK k Γ K (ρG j)))) →
    Subsingleton (LocalizedModule S (AMFK k Γ K (ρF n)))
def ShortExactFormsExactTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (A B Q : Type)
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup Q] [Module k Q]
    (ρA : Representation k K A) (ρB : Representation k K B) (ρQ : Representation k K Q)
    (Θ : Type) [AddCommGroup Θ] [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ)
    (f : A →ₗ[k] B) (g : B →ₗ[k] Q) (hf : IsIntertw ρA ρB f) (hg : IsIntertw ρB ρQ g),
    OrdersInvertible k Γ K → Function.Injective f → Function.Exact f g → Function.Surjective g →
    Function.Injective (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf)) ∧
    Function.Exact (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))
      (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg)) ∧
    Function.Surjective (mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg)) ∧
    ∃ e : (AMFK k Γ K (ρB.tprod θ) ⧸
        LinearMap.range (mapM Γ K (f.rTensor Θ) (isIntertw_rTensor θ hf))) ≃ₗ[k]
          AMFK k Γ K (ρQ.tprod θ),
      ∀ φ, e (Submodule.Quotient.mk φ) = mapM Γ K (g.rTensor Θ) (isIntertw_rTensor θ hg) φ
def PowerScaledFormsTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (Q : Type)
    [AddCommGroup Q] [Module k Q] (ρ : Representation k K Q) (Θ : Type) [AddCommGroup Θ]
    [Module k Θ] [Module.Free k Θ] (θ : Representation k K Θ) (l : k) (c : ℕ),
    OrdersInvertible k Γ K →
    Function.Injective (mapM Γ K ((powSub (W := Q) l c).subtype.rTensor Θ)
      (isIntertw_rTensor θ (isIntertw_subtype ρ _ (isStable_powSub ρ l c)))) ∧
    ∀ φ : AMFK k Γ K (ρ.tprod θ),
      φ ∈ LinearMap.range (mapM Γ K ((powSub (W := Q) l c).subtype.rTensor Θ)
        (isIntertw_rTensor θ (isIntertw_subtype ρ _ (isStable_powSub ρ l c)))) ↔
      ∃ ψ : AMFK k Γ K (ρ.tprod θ), φ = l ^ c • ψ
def FiltrationFormsGradedTypes : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (n : ℕ) (F Gr : ℕ → Type)
    [∀ j, AddCommGroup (F j)] [∀ j, Module k (F j)] [∀ j, AddCommGroup (Gr j)]
    [∀ j, Module k (Gr j)] (ρF : ∀ j, Representation k K (F j))
    (ρG : ∀ j, Representation k K (Gr j)) (Θ : Type) [AddCommGroup Θ] [Module k Θ]
    [Module.Free k Θ] (θ : Representation k K Θ) (i : ∀ j, F j →ₗ[k] F (j + 1))
    (p : ∀ j, F (j + 1) →ₗ[k] Gr j) (hi : ∀ j, IsIntertw (ρF j) (ρF (j + 1)) (i j))
    (hp : ∀ j, IsIntertw (ρF (j + 1)) (ρG j) (p j)) (T : Type) [CommRing T]
    [∀ j, Module T (AMFK k Γ K ((ρF j).tprod θ))] [∀ j, Module T (AMFK k Γ K ((ρG j).tprod θ))]
    (S : Submonoid T),
    Subsingleton (F 0) → (∀ j < n, Function.Injective (i j)) →
    (∀ j < n, Function.Exact (i j) (p j)) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K ((ρF j).tprod θ)),
      mapM Γ K ((i j).rTensor Θ) (isIntertw_rTensor θ (hi j)) (t • φ) =
        t • mapM Γ K ((i j).rTensor Θ) (isIntertw_rTensor θ (hi j)) φ) →
    (∀ j < n, ∀ (t : T) (φ : AMFK k Γ K ((ρF (j + 1)).tprod θ)),
      mapM Γ K ((p j).rTensor Θ) (isIntertw_rTensor θ (hp j)) (t • φ) =
        t • mapM Γ K ((p j).rTensor Θ) (isIntertw_rTensor θ (hp j)) φ) →
    (∀ j < n, Subsingleton (LocalizedModule S (AMFK k Γ K ((ρG j).tprod θ)))) →
    Subsingleton (LocalizedModule S (AMFK k Γ K ((ρF n).tprod θ)))
def cut {O F V : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module O V]
    [Module F V] [IsScalarTower O F V] (L : Submodule O V) (Z : Submodule F V) : Submodule O V :=
  L ⊓ Z.restrictScalars O
def DVRLatticeIntersection : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (Z : Submodule F V) (l : O) (J : ℕ),
    L.FG → l ≠ 0 → (∀ x ∈ L, l ^ J • x ∈ L') →
    (∀ x ∈ cut L Z, l ^ J • x ∈ cut L' Z) ∧
    Module.length O (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
      (J : ℕ∞) * IsDiscreteValuationRing.addVal O l * (Module.finrank O (cut L Z) : ℕ∞) ∧
    (Finite (O ⧸ Ideal.span {l ^ J}) →
      Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
        Nat.card (O ⧸ Ideal.span {l ^ J}) ^ Module.finrank O (cut L Z))
def LatticeIntersectionRank : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L : Submodule O V) (Z : Submodule F V), L.FG →
    Module.finrank O (cut L Z) = Module.finrank F ↥(Submodule.span F (L : Set V) ⊓ Z) ∧
    (Module.Finite F Z → Module.finrank O (cut L Z) ≤ Module.finrank F Z)
def CardQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (J : ℕ),
    Nat.card (O ⧸ Ideal.span {(l : O) ^ J}) = l ^ (J * Module.finrank ℤ_[l] O)
def LatticeIntersectionIndexCost : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (Z : Submodule F V) (J : ℕ),
    L.FG → (∀ x ∈ L, (l : O) ^ J • x ∈ L') →
    Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype) ≤
      l ^ (J * Module.finrank ℤ_[l] O * Module.finrank O (cut L Z)) ∧
    Real.log (Nat.card (cut L Z ⧸ (cut L' Z).comap (cut L Z).subtype)) /
        (Module.finrank ℤ_[l] O : ℝ) ≤
      (J : ℝ) * (Module.finrank O (cut L Z) : ℝ) * Real.log l
def Translate : Prop :=
  ∀ (N h m : ℤ) (H Hc : Multiset ℤ), Hc = H.map (fun x => N - 1 - x) → m ∈ H →
    (∀ x ∈ H, m ≤ x) → (∀ x ∈ H, x ≤ m + h) →
    (∀ u ∈ H.map (fun x => x + -m), 0 ≤ u ∧ u ≤ h) ∧ (0 : ℤ) ∈ H.map (fun x => x + -m) ∧
    Hc.map (fun x => x + (h - N + 1 - -m)) = (H.map (fun x => x + -m)).map (fun u => h - u) ∧
    (∀ u ∈ Hc.map (fun x => x + (h - N + 1 - -m)), 0 ≤ u ∧ u ≤ h) ∧
    -m + (h - N + 1 - -m) = h - N + 1
def TranslateInv : Prop :=
  (∀ (l : ℕ) (b c : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (b + c) t κ (U.image (fun u => u + c)) = mwCount l b t κ U) ∧
  ∀ (n r : ℕ) (U U' : Fin n → ℤ) (c : ℤ),
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => (a : ℕ) < r), ((U a + c) - (U' a + c)) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => (a : ℕ) < r), (U a - U' a)
def TypeOnReal : Prop :=
  ∀ (M : Type) [CommGroup M] (ι : Type) (Φ : Finset ι) (a : ι → M) (c c' : ι → ℤ) (w₀ : ℤ),
    (∀ τ ∈ Φ, c τ + c' τ = w₀) →
    ∏ τ ∈ Φ, (a τ ^ c τ * a τ ^ c' τ) = (∏ τ ∈ Φ, a τ) ^ w₀
def RootSep : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (𝔮 : Ideal R) (M : ℕ) (z : R), 𝔮.IsPrime →
    (M : R) ∉ 𝔮 → z ^ M = 1 → z - 1 ∈ 𝔮 → z = 1
def CharExt : Prop :=
  ∀ (I : Type) [CommGroup I] (P : Subgroup I) (χ : P →* ℂˣ),
    ∃ χ' : I →* ℂˣ, ∀ x : P, χ' (x : I) = χ x
def ExpExists : Prop :=
  ∀ (O F V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
    (L L' : Submodule O V) (l : O), L.FG → l ∈ IsLocalRing.maximalIdeal O →
    (L : Set V) ⊆ Submodule.span F (L' : Set V) → ∃ J : ℕ, ∀ x ∈ L, l ^ J • x ∈ L'
def DegreeOfInf : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l : ℕ) (ζ : L), l.Prime →
    IsPrimitiveRoot ζ l → E ⊓ IntermediateField.adjoin ℚ {ζ} = ⊥ →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1
def DegreeOfDiscr : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l : ℕ) (ζ : L), l.Prime →
    IsPrimitiveRoot ζ l → ¬ (l : ℤ) ∣ NumberField.discr E →
    Module.finrank E (IntermediateField.adjoin E {ζ}) = l - 1
def NumberFieldOrdersPrime : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : IntermediateField ℚ L) (l N : ℕ) (ζ : L) (G : Type)
    [Group G] (Γ K : Subgroup G) (r : Γ →* GL (Fin N) E) (O : Type) [CommRing O] [IsLocalRing O],
    l.Prime → IsPrimitiveRoot ζ l → ¬ (l : ℤ) ∣ NumberField.discr E → N + 1 < l →
    Function.Injective r → (∀ x : G, Finite (GamAt Γ K x)) →
    (l : O) ∈ IsLocalRing.maximalIdeal O →
    (∀ x : G, ¬ l ∣ Nat.card (GamAt Γ K x)) ∧ OrdersInvertible O Γ K
def TypeCong : Prop :=
  ∀ (R : Type) [CommRing R] (𝔮 : Ideal R) (ι : Type) (Φ : Finset ι) (a : ι → Rˣ) (c : ι → ℤ),
    (∀ τ ∈ Φ, (a τ : R) - 1 ∈ 𝔮) → ((∏ τ ∈ Φ, a τ ^ c τ : Rˣ) : R) - 1 ∈ 𝔮
def TypeTrivialOnUnits : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (𝔮 : Ideal R) (M : ℕ) (ι : Type) (Φ : Finset ι)
    (a : ι → Rˣ) (c : ι → ℤ), 𝔮.IsPrime → (M : R) ∉ 𝔮 → (∀ τ ∈ Φ, (a τ : R) - 1 ∈ 𝔮) →
    (∏ τ ∈ Φ, a τ ^ c τ) ^ M = 1 → ∏ τ ∈ Φ, a τ ^ c τ = 1
def CharOfType : Prop :=
  ∀ (E₁ I : Type) [CommGroup E₁] [CommGroup I] (ι : E₁ →* I) (Ty : E₁ →* ℂˣ),
    (∀ u, ι u = 1 → Ty u = 1) → ∃ χ : I →* ℂˣ, ∀ α, χ (ι α) = Ty α
def HeckeFunct : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (k : Type) [CommRing k]
    (W₁ W₂ : Type) [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    (φ : W₁ →ₗ[k] W₂) (f : G₁ → k) (ψ : G₁ × G₂ → W₁), IsCommensurated K₁ → f ∈ Hecke k K₁ →
    ∀ g, hActK K₁ f (fun x => φ (ψ x)) g = φ (hActK K₁ f ψ g)
end Formalism.CohomologicalDescent.AutomorphicFormLattices


