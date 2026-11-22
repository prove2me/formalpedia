-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:14.870801+00:00
-- url     : https://prove2.me/theorems/8cef6a2a-3a6c-4ad4-9e51-619ad8adeae4
-- title:
--   Galois Conj Central Idempotent
-- statement:
--   Definitions and structural lemmas for Galois Conj Central Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
def glEquiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv
variable {K} in

def transp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (τ : FDRep ℂ (GL ι K)) : FDRep ℂ (GL κ K) :=
  FDRep.of (τ.ρ.comp (glEquiv K e).symm.toMonoidHom)
def SupportExists : Prop :=
  ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)), Simple τ →
    ∃ (s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧
      IsConstituent τ (hcRep K b lam)
structure LabelMap (C : LabelConv K) where
  lab : ∀ d : ℕ, FDRep ℂ (GL (Fin d) K) → K[X]
  lab_iso : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), Nonempty (τ ≅ τ') → lab d τ = lab d τ'
  lab_spec : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    (lab d τ).Monic ∧ Irreducible (lab d τ) ∧ lab d τ ≠ X ∧ (lab d τ).natDegree = d
  lab_inj : ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' → lab d τ = lab d τ' → Nonempty (τ ≅ τ')
  lab_one : ∀ (τ : FDRep ℂ (GL (Fin 1) K)) (x : K), Simple τ → x ≠ 0 →
    (∀ (γ : GL (Fin 1) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m) →
    lab 1 τ = X - Polynomial.C x
variable {K} in

def LabelMapEquivariant {C : LabelConv K} (O : LabelMap K C) : Prop :=
  (∀ (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ τ τ' : FDRep ℂ (GL (Fin d) K), 1 ≤ d → Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) →
      rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· ^ a)) ∧
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ →
    Simple τ' → IsCuspidal K τ' →
    (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (·⁻¹)
def LabelMapExists : Prop := ∀ C : LabelConv K, Nonempty (LabelMap K C)
variable {K} {C : LabelConv K}
def labO (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] (σ : FDRep ℂ (GL κ K)) : K[X] :=
  O.lab (Fintype.card κ) (transp (Fintype.equivFin κ) σ)
def HasLabelO (O : LabelMap K C) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, labO O (lam c)
def CuspParamO (O : LabelMap K C) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
      ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ O.lab d τ = P) ∧
    ∀ τ : FDRep ℂ (GL (Fin d) K), Simple τ → IsCuspidal K τ →
      (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1)
def HCLabelO (O : LabelMap K C) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ →
    (∃ f, HasLabelO O τ f) ∧ ∀ f f', HasLabelO O τ f → HasLabelO O τ f' → f = f'
def LabelSurjO (O : LabelMap K C) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f : K[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
    ∃ τ : FDRep ℂ (GL (Fin n) K), Simple τ ∧ HasLabelO O τ f
def SqfreeO (O : LabelMap K C) : Prop :=
  (∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
    Function.Injective (fun c => labO O (lam c)) →
    IsIrrRep (hcRep K b lam) ∧
      (Module.finrank ℂ (hcSpace K b lam) : ℤ) * ∏ c, ((q K : ℤ) ^ Fintype.card {i // b i = c} - 1) =
        ∏ i ∈ Finset.Icc 1 n, ((q K : ℤ) ^ i - 1)) ∧
  ∀ (n : ℕ) (f : K[X]) (τ τ' : FDRep ℂ (GL (Fin n) K)), Squarefree f → Simple τ → Simple τ' →
    HasLabelO O τ f → HasLabelO O τ' f → Nonempty (τ ≅ τ')
def MackeyPermO (O : LabelMap K C) : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
    Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b lam)) =
      Fintype.card {π : Equiv.Perm (Fin s) // ∀ c, labO O (lam (π c)) = labO O (lam c)}
def DisjointMultO (O : LabelMap K C) : Prop :=
  ∀ (n : ℕ) (b : Fin n → Fin 2) (τ σ : ∀ c : Fin 2, FDRep ℂ (GL {i // b i = c} K)) (f f' : Fin 2 → K[X]),
    Function.Surjective b →
    (∀ c, Simple (τ c) ∧ Simple (σ c) ∧ HasLabelO O (τ c) (f c) ∧ HasLabelO O (σ c) (f' c)) →
    IsCoprime (f 0) (f' 1) → IsCoprime (f 1) (f' 0) →
    Module.finrank ℂ (Intw (hcRep K b τ) (hcRep K b σ)) =
      Module.finrank ℂ (Intw (τ 0).ρ (σ 0).ρ) * Module.finrank ℂ (Intw (τ 1).ρ (σ 1).ρ)
def LabelMulO (O : LabelMap K C) : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (τ : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (f : Fin s → K[X])
    (σ : FDRep ℂ (GL (Fin n) K)), Function.Surjective b →
    (∀ c, Simple (τ c) ∧ HasLabelO O (τ c) (f c)) → Simple σ → IsConstituent σ (hcRep K b τ) →
    HasLabelO O σ (∏ c, f c)
def GaloisLabelO (O : LabelMap K C) : Prop :=
  LabelMapEquivariant O → ∀ (n : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ d ∈ Finset.Icc 1 n, (q K ^ d - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ (τ : FDRep ℂ (GL (Fin n) K)) (f f' : K[X]), Simple τ → HasLabelO O τ f →
      f'.Monic → rootsBar K f' = (rootsBar K f).map (· ^ a) →
      ∃ τ' : FDRep ℂ (GL (Fin n) K), Simple τ' ∧ HasLabelO O τ' f' ∧
        (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) ∧
        ∀ γ, α ((zIdem τ).coeff γ) = (zIdem τ').coeff γ
def DualLabelO (O : LabelMap K C) : Prop :=
  LabelMapEquivariant O → ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)) (f f' : K[X]), Simple τ → HasLabelO O τ f →
    f'.Monic → rootsBar K f' = (rootsBar K f).map (·⁻¹) →
    ∃ τ' : FDRep ℂ (GL (Fin n) K), Simple τ' ∧ HasLabelO O τ' f' ∧
      ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)
variable (K) in

def blockDiagHom (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    Matrix α α K × Matrix β β K →* Matrix (α ⊕ β) (α ⊕ β) K where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p p' := by simp [Matrix.fromBlocks_multiply]
variable (K) in

def leviEmb {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p] :
    GL {i // p i} K × GL {i // ¬ p i} K →* GL ι K :=
  (glEquiv K (Equiv.sumCompl p)).toMonoidHom.comp
    ((Units.map (blockDiagHom K {i // p i} {i // ¬ p i})).comp MulEquiv.prodUnits.symm.toMonoidHom)
def twoBlock (n a : ℕ) : Fin n → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
structure Arr {n s : ℕ} (b : Fin n → Fin s) (ι₀ : Type) (B : Finset (Fin s)) where
  t : ℕ
  bb : ι₀ → Fin t
  surj : Function.Surjective bb
  σ : Fin t ≃ B
  e : ∀ c : Fin t, {i // bb i = c} ≃ {i // b i = (σ c).1}
def arrRep {n s : ℕ} {b : Fin n → Fin s} {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] {B : Finset (Fin s)}
    (A : Arr b ι₀ B) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :=
  hcRep K A.bb (fun c => transp (A.e c).symm (lam (A.σ c)))
def jacHom {n s : ℕ} (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (a : ℕ)
    (σ₁ : FDRep ℂ (GL {i : Fin n // (i : ℕ) < a} K)) (σ₂ : FDRep ℂ (GL {i : Fin n // ¬ (i : ℕ) < a} K)) :
    Submodule ℂ (TensorProduct ℂ (σ₁ : Type) (σ₂ : Type) →ₗ[ℂ] hcSpace K b lam) where
  carrier := {φ | (∀ m₁ m₂, φ ∘ₗ TensorProduct.map (σ₁.ρ m₁) (σ₂.ρ m₂) =
      hcRep K b lam (leviEmb K (fun i : Fin n => (i : ℕ) < a) (m₁, m₂)) ∘ₗ φ) ∧
    ∀ x, ∀ u ∈ unip K (twoBlock n a), hcRep K b lam u (φ x) = φ x}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφ'⟩ ⟨hψ, hψ'⟩
    refine ⟨fun m₁ m₂ => ?_, fun x u hu => ?_⟩
    · rw [LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
    · simp only [LinearMap.add_apply, map_add, hφ' x u hu, hψ' x u hu]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro r φ ⟨hφ, hφ'⟩
    refine ⟨fun m₁ m₂ => ?_, fun x u hu => ?_⟩
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ]
    · simp only [LinearMap.smul_apply, map_smul, hφ' x u hu]
variable (K) in

def JacquetPSH : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (a : ℕ),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → 0 < a → a < n →
    ∃ (A₁ : ∀ B : {B : Finset (Fin s) // ∑ c ∈ B, Fintype.card {i // b i = c} = a},
          Arr b {i : Fin n // (i : ℕ) < a} B.1)
      (A₂ : ∀ B : {B : Finset (Fin s) // ∑ c ∈ B, Fintype.card {i // b i = c} = a},
          Arr b {i : Fin n // ¬ (i : ℕ) < a} B.1ᶜ),
      ∀ (σ₁ : FDRep ℂ (GL {i : Fin n // (i : ℕ) < a} K))
        (σ₂ : FDRep ℂ (GL {i : Fin n // ¬ (i : ℕ) < a} K)), Simple σ₁ → Simple σ₂ →
        Module.finrank ℂ (jacHom b lam a σ₁ σ₂) =
          ∑ B, Module.finrank ℂ (Intw σ₁.ρ (arrRep (A₁ B) lam)) *
            Module.finrank ℂ (Intw σ₂.ρ (arrRep (A₂ B) lam))
variable (K) in
open Classical in

def epsU (n : ℕ) (ψ₀ : AddChar K ℂ) : MonoidAlgebra ℂ (GL (Fin n) K) :=
  ∑ u ∈ Finset.univ.filter (fun u => u ∈ unitri K n),
    MonoidAlgebra.single u ((((Finset.univ.filter (fun u => u ∈ unitri K n)).card : ℂ))⁻¹ * (psiU ψ₀ u)⁻¹)
def wtU {n : ℕ} (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin n) K)) : ℂ :=
  (epsU K n ψ₀ * zIdem τ).coeff 1 / (epsU K n ψ₀).coeff 1
variable (K) in

def TypeWeightHC : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin n) K)),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
    (∀ (c c' : Fin s) (e : {i // b i = c} ≃ {i // b i = c'}), Nonempty (transp e (lam c) ≅ lam c') → c = c') →
    ψ₀ ≠ 1 → Simple τ → IsConstituent τ (hcRep K b lam) →
    wtU ψ₀ τ = ∏ c, ((q K : ℂ) ^ Fintype.card {i // b i = c} - 1)⁻¹
def TypeWeightO (O : LabelMap K C) : Prop :=
  ∀ (n : ℕ) (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin n) K)) (f : K[X]),
    ψ₀ ≠ 1 → Simple τ → Squarefree f → HasLabelO O τ f →
    wtU ψ₀ τ = ((UniqueFactorizationMonoid.normalizedFactors f).map
      (fun P => ((q K : ℂ) ^ P.natDegree - 1)⁻¹)).prod
def EpsIdem : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (J : Subgroup Γ) [Fintype J] (χ : J →* ℂˣ),
    (∑ u : J, MonoidAlgebra.single (u : Γ) ((Fintype.card J : ℂ)⁻¹ * ((χ u : ℂˣ) : ℂ)⁻¹)) *
      (∑ u : J, MonoidAlgebra.single (u : Γ) ((Fintype.card J : ℂ)⁻¹ * ((χ u : ℂˣ) : ℂ)⁻¹)) =
    ∑ u : J, MonoidAlgebra.single (u : Γ) ((Fintype.card J : ℂ)⁻¹ * ((χ u : ℂˣ) : ℂ)⁻¹)
def ZIdemSelfAdj : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ),
    starRingEnd ℂ ((zIdem τ).coeff γ) = (zIdem τ).coeff γ⁻¹
def ZIdemOccurs : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Simple τ →
    ((∃ v : V, ρ.asAlgebraHom (zIdem τ) v ≠ 0) ↔ IsConstituent τ ρ)
end Formalism.IrreducibleCountingLemmas.TYPES
namespace Formalism.IrreducibleCountingLemmas.TYPES
section BaseChange
variable {Γ : Type} [Group Γ]
def bcRepr (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) : Representation ℂ Γ (Fin (Module.finrank ℂ V) → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ ≃ₐ[ℂ]
      ((Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))).toRingEquiv.toMonoidHom.comp
    ((σ.toRingHom.mapMatrix : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →+*
        Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toRingEquiv.toMonoidHom.comp ρ))
def bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : FDRep ℂ Γ := FDRep.of (bcRepr σ τ.ρ)
end BaseChange
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
def BcHCSupport : Prop :=
  (∀ (σ : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
      (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
      ∃ φ ∈ Intw (bcRepr σ (hcRep K b lam)) (hcRep K b (fun c => bc σ (lam c))), Function.Bijective φ) ∧
  (∀ (σ : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)),
      Simple τ → Simple (bc σ τ)) ∧
  (∀ (σ : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)),
      IsCuspidal K τ → IsCuspidal K (bc σ τ)) ∧
  (∀ (σ : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
      (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (τ : FDRep ℂ (GL ι K)),
      IsConstituent τ (hcRep K b lam) → IsConstituent (bc σ τ) (hcRep K b (fun c => bc σ (lam c))))
def BcZIdem : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ),
    σ ((zIdem τ).coeff γ) = (zIdem (bc σ τ)).coeff γ
end Formalism.IrreducibleCountingLemmas.TYPES
namespace Formalism.IrreducibleCountingLemmas.TYPES
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
def LabelMapGreen : Prop :=
  ∀ C : LabelConv K, CuspParam K C → ∃ O : LabelMap K C, LabelMapEquivariant O ∧
    ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → IsCuspidal K τ → HasCuspLabel C τ (O.lab d τ)
end Formalism.IrreducibleCountingLemmas.TYPES


