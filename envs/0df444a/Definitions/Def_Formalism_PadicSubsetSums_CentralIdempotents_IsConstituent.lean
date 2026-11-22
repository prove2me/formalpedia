-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:59.715892+00:00
-- url     : https://prove2.me/theorems/4069ac6e-3a7c-4a5a-a8bd-ab2862535b7b
-- title:
--   Is Constituent
-- statement:
--   Definitions and structural lemmas for Is Constituent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/IsConstituent.lean

import Mathlib
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
def IsBlockUT {ι : Type} {s : ℕ} (b : ι → Fin s) (M : Matrix ι ι K) : Prop :=
  ∀ i j, b j < b i → M i j = 0
variable {K} in
theorem isBlockUT_mul {ι : Type} [Fintype ι] {s : ℕ} (b : ι → Fin s) {A B : Matrix ι ι K}
    (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) : IsBlockUT K b (A * B) := by
  intro i j h
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : b k < b i
  · simp [hA i k hk]
  · simp [hB k j (lt_of_lt_of_le h (not_lt.mp hk))]
def parab {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := {g | IsBlockUT K b (g : Matrix ι ι K) ∧ IsBlockUT K b ((g⁻¹ : GL ι K) : Matrix ι ι K)}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;>
    · intro i j h
      have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne hij]
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨?_, ?_⟩
    · simpa [Units.val_mul] using isBlockUT_mul b hg hh
    · simpa [mul_inv_rev, Units.val_mul] using isBlockUT_mul b hh' hg'
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨hg', by simpa using hg⟩
def unip {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Set (GL ι K) :=
  {g | g ∈ parab K b ∧ ∀ i j, b i = b j → (g : Matrix ι ι K) i j = if i = j then 1 else 0}
def IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  ∀ (s : ℕ) (b : ι → Fin s), Function.Surjective b → 2 ≤ s →
    ∀ v : τ, (∀ u ∈ unip K b, τ.ρ u v = v) → v = 0
def Nd (d : ℕ) : ℕ := Set.ncard {P : K[X] | P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d}
def blk {ι : Type} {s : ℕ} (b : ι → Fin s) (c : Fin s) (M : Matrix ι ι K) :
    Matrix {i // b i = c} {i // b i = c} K :=
  M.submatrix Subtype.val Subtype.val
variable {K} in
theorem blk_mul {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    {A B : Matrix ι ι K} (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) :
    blk K b c (A * B) = blk K b c A * blk K b c B := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = c)]
  have h0 : ∑ k : {k // ¬ b k = c}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ _
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k (by rw [hi]; exact h)]; simp
    · rw [hB k j (by rw [hj]; exact h)]; simp
  rw [h0, add_zero]
def levi {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    (p : parab K b) : GL {i // b i = c} K :=
  ⟨blk K b c (p.1 : Matrix ι ι K), blk K b c ((p.1⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← blk_mul b c p.2.1 p.2.2, Units.mul_inv]; exact Matrix.submatrix_one _ Subtype.val_injective,
    by rw [← blk_mul b c p.2.2 p.2.1, Units.inv_mul]; exact Matrix.submatrix_one _ Subtype.val_injective⟩
section HC
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
def infl (p : parab K b) :
    PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] PiTensorProduct ℂ (fun c => (lam c : Type)) :=
  PiTensorProduct.map (fun c => (lam c).ρ (levi K b c p))
def hcSpace : Submodule ℂ (GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) where
  carrier := {f | ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)}
  add_mem' := by
    intro f g hf hg p x
    simp [hf p x, hg p x]
  zero_mem' := by
    intro p x
    simp
  smul_mem' := by
    intro a f hf p x
    simp [hf p x]
def hcRep : Representation ℂ (GL ι K) (hcSpace K b lam) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (x * g), fun p x => by simpa [mul_assoc] using f.2 p (x * g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    ext f x
    simp
  map_mul' := by
    intro g h
    ext f x
    simp [mul_assoc]
end HC
section Reps
variable {Γ : Type} [Group Γ]
def Intw {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ V') : Submodule ℂ (V →ₗ[ℂ] V') where
  carrier := {φ | ∀ g, φ ∘ₗ ρ g = ρ' g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro a φ hφ g
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]
def IsConstituent {V : Type} [AddCommGroup V] [Module ℂ V] (τ : FDRep ℂ Γ)
    (ρ : Representation ℂ Γ V) : Prop :=
  ∃ φ ∈ Intw τ.ρ ρ, φ ≠ 0
def IsIrrRep {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤
def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))
end Reps
structure LabelConv where
  ι : AlgebraicClosure K →* ℂ
  ι_inj : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → ι x = ι y → x = y
  gen : ℕ → AlgebraicClosure K
  gen_order : ∀ d, 1 ≤ d → orderOf (gen d) = Fintype.card K ^ d - 1
  gen_norm : ∀ d e, 1 ≤ d → 1 ≤ e →
    gen (d * e) ^ ((Fintype.card K ^ (d * e) - 1) / (Fintype.card K ^ d - 1)) = gen d
def rootsBar (f : K[X]) : Multiset (AlgebraicClosure K) :=
  (f.map (algebraMap K (AlgebraicClosure K))).roots
variable {K} in

def HasCuspLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (P : K[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = Fintype.card ι ∧
    ∀ x : AlgebraicClosure K, aeval x P = 0 →
    ∀ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) →
    ∀ z : AlgebraicClosure K, aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0 →
    ∀ m : ℕ, C.gen (Fintype.card ι) ^ m = z →
      LinearMap.trace ℂ τ (τ.ρ γ) =
        (-1) ^ (Fintype.card ι - 1) *
          ∑ a ∈ Finset.range (Fintype.card ι), C.ι x ^ (m * Fintype.card K ^ a)
variable {K} in

def HasLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (P : Fin s → K[X]),
    Function.Surjective b ∧
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) ∧ HasCuspLabel C (lam c) (P c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, P c
abbrev q : ℕ := Fintype.card K
def CuspCountDim : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ τ : Fin (Nd K d) → FDRep ℂ (GL (Fin d) K),
      (∀ i, Simple (τ i) ∧ IsCuspidal K (τ i)) ∧
      (∀ i j, Nonempty (τ i ≅ τ j) → i = j) ∧
      (∀ σ : FDRep ℂ (GL (Fin d) K), Simple σ → IsCuspidal K σ → ∃ i, Nonempty (σ ≅ τ i))) ∧
    (∀ σ : FDRep ℂ (GL (Fin d) K), Simple σ → IsCuspidal K σ →
      (Module.finrank ℂ σ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1))
def RegOrbitCount : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [Algebra K L] (d : ℕ), Module.finrank K L = d → 1 ≤ d →
    Set.ncard {θ : Lˣ →* ℂˣ | ∀ a, 0 < a → a < d → θ ^ (q K ^ a) ≠ θ} = d * Nd K d
def CuspParam (C : LabelConv K) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ τ : FDRep ℂ (GL (Fin d) K), Simple τ → IsCuspidal K τ →
      (∃! P : K[X], HasCuspLabel C τ P) ∧
      (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1)) ∧
    (∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
      ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P) ∧
    (∀ (τ τ' : FDRep ℂ (GL (Fin d) K)) (P : K[X]), Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      HasCuspLabel C τ P → HasCuspLabel C τ' P → Nonempty (τ ≅ τ'))
def ConvExists : Prop := Nonempty (LabelConv K)
def HCLabel (C : LabelConv K) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ →
    (∃ f, HasLabel C τ f) ∧ ∀ f f', HasLabel C τ f → HasLabel C τ f' → f = f'
def LabelSurj (C : LabelConv K) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f : K[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
    ∃ τ : FDRep ℂ (GL (Fin n) K), Simple τ ∧ HasLabel C τ f
def Sqfree (C : LabelConv K) : Prop :=
  (∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (P : Fin s → K[X]),
    Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) ∧ HasCuspLabel C (lam c) (P c)) →
    Function.Injective P →
    IsIrrRep (hcRep K b lam) ∧
      (Module.finrank ℂ (hcSpace K b lam) : ℤ) * ∏ c, ((q K : ℤ) ^ Fintype.card {i // b i = c} - 1) =
        ∏ i ∈ Finset.Icc 1 n, ((q K : ℤ) ^ i - 1)) ∧
  ∀ (n : ℕ) (f : K[X]) (τ τ' : FDRep ℂ (GL (Fin n) K)), Squarefree f → Simple τ → Simple τ' →
    HasLabel C τ f → HasLabel C τ' f → Nonempty (τ ≅ τ')
def MackeyPerm (C : LabelConv K) : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (P : Fin s → K[X]),
    Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) ∧ HasCuspLabel C (lam c) (P c)) →
    Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b lam)) =
      Fintype.card {π : Equiv.Perm (Fin s) // ∀ c, P (π c) = P c}
def DisjointMult (C : LabelConv K) : Prop :=
  ∀ (n : ℕ) (b : Fin n → Fin 2) (τ σ : ∀ c : Fin 2, FDRep ℂ (GL {i // b i = c} K)) (f f' : Fin 2 → K[X]),
    Function.Surjective b →
    (∀ c, Simple (τ c) ∧ Simple (σ c) ∧ HasLabel C (τ c) (f c) ∧ HasLabel C (σ c) (f' c)) →
    IsCoprime (f 0) (f' 1) → IsCoprime (f 1) (f' 0) →
    Module.finrank ℂ (Intw (hcRep K b τ) (hcRep K b σ)) =
      Module.finrank ℂ (Intw (τ 0).ρ (σ 0).ρ) * Module.finrank ℂ (Intw (τ 1).ρ (σ 1).ρ)
def unitri (n : ℕ) : Set (GL (Fin n) K) :=
  {g | ∀ i j, j ≤ i → (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0}
variable {K} in

def psiU {n : ℕ} (ψ₀ : AddChar K ℂ) (u : GL (Fin n) K) : ℂ :=
  ψ₀ (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then (u : Matrix (Fin n) (Fin n) K) i j else 0)
variable {K} in

def ggSub {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ₀ : AddChar K ℂ)
    (ρ : Representation ℂ (GL (Fin n) K) V) : Submodule ℂ V where
  carrier := {v | ∀ u ∈ unitri K n, ρ u v = psiU ψ₀ u • v}
  add_mem' := by
    intro v w hv hw u hu
    rw [map_add, hv u hu, hw u hu, smul_add]
  zero_mem' := by
    intro u _
    simp
  smul_mem' := by
    intro a v hv u hu
    rw [map_smul, hv u hu, smul_comm]
def GelfandGraev : Prop :=
  ∀ (n : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 →
    (∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ → Module.finrank ℂ (ggSub ψ₀ τ.ρ) ≤ 1) ∧
    ∀ (s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
      Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
      Module.finrank ℂ (ggSub ψ₀ (hcRep K b lam)) = 1
def GaloisLabel (C : LabelConv K) : Prop :=
  ∀ (n : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ),
    (∀ ζ : ℂ, ζ ^ (∏ d ∈ Finset.Icc 1 n, (q K ^ d - 1)) = 1 → α ζ = ζ ^ a) →
    ∀ (τ : FDRep ℂ (GL (Fin n) K)) (f f' : K[X]), Simple τ → HasLabel C τ f →
      f'.Monic → rootsBar K f' = (rootsBar K f).map (· ^ a) →
      ∃ τ' : FDRep ℂ (GL (Fin n) K), Simple τ' ∧ HasLabel C τ' f' ∧
        (∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) ∧
        ∀ γ, α ((zIdem τ).coeff γ) = (zIdem τ').coeff γ
def DualLabel (C : LabelConv K) : Prop :=
  ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)) (f f' : K[X]), Simple τ → HasLabel C τ f →
    f'.Monic → rootsBar K f' = (rootsBar K f).map (·⁻¹) →
    ∃ τ' : FDRep ℂ (GL (Fin n) K), Simple τ' ∧ HasLabel C τ' f' ∧
      ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)
open Classical in

def HowlettLehrer : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL (Fin n) K) V),
    let U := {g : GL (Fin n) K | g ∈ unip K b}
    let Um := {g : GL (Fin n) K | g ∈ unip K (fun i => (Fin.revPerm (b i)))}
    let avg : V → V := fun v => ∑ u ∈ Finset.univ.filter (fun u => u ∈ U), ρ u v
    Set.BijOn avg {v | ∀ u ∈ Um, ρ u v = v} {v | ∀ u ∈ U, ρ u v = v}
open Classical in

def GGIdem : Prop :=
  ∀ (n : ℕ) (ψ₀ : AddChar K ℂ),
    let e : MonoidAlgebra ℂ (GL (Fin n) K) :=
      ∑ u ∈ Finset.univ.filter (fun u => u ∈ unitri K n),
        MonoidAlgebra.single u ((((Finset.univ.filter (fun u => u ∈ unitri K n)).card : ℂ))⁻¹ * (psiU ψ₀ u)⁻¹)
    e * e = e
def CentralIdem : Prop :=
  ∀ n : ℕ,
    (∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ →
      zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ) ∧
    (∀ τ τ' : FDRep ℂ (GL (Fin n) K), Simple τ → Simple τ' → IsEmpty (τ ≅ τ') →
      zIdem τ * zIdem τ' = 0) ∧
    ∀ (m : ℕ) (τ : Fin m → FDRep ℂ (GL (Fin n) K)), (∀ i, Simple (τ i)) →
      (∀ i j, Nonempty (τ i ≅ τ j) → i = j) →
      (∀ σ : FDRep ℂ (GL (Fin n) K), Simple σ → ∃ i, Nonempty (σ ≅ τ i)) →
      ∑ i, zIdem (τ i) = 1
end Formalism.IrreducibleCountingLemmas.TYPES


