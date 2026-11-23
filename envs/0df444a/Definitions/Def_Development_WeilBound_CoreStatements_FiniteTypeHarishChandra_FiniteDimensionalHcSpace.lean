-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_FiniteDimensionalHcSpace
-- name    : Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_FiniteDimensionalHcSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:36.296452+00:00
-- url     : https://prove2.me/theorems/de3c84ec-c925-4388-9ac9-dffc99a2b142
-- title:
--   Finite Dimensional Hc Space
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Hc Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/FiniteDimensionalHcSpace.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_HCDisjointO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace ReciprocityTheory.Ty.Fin
section Gen
variable {Γ : Type} [Group Γ]
def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤
def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))
def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))
def Mk.piTensorRep {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (V : ∀ i, FDRep ℂ (G i)) :
    Representation ℂ (∀ i, G i) (PiTensorProduct ℂ fun i => (V i : Type)) where
  toFun g := PiTensorProduct.map fun i => (V i).ρ (g i)
  map_one' := by simp [PiTensorProduct.map_one]
  map_mul' g h := by simp [PiTensorProduct.map_mul]
open Classical in

def ip [Fintype Γ] (S : Set Γ) (a b : Γ → ℂ) : ℂ :=
  (S.ncard : ℂ)⁻¹ * ∑ g, if g ∈ S then a g⁻¹ * b g else 0
open Classical in

def indF [Fintype Γ] (H : Subgroup Γ) (φ : Γ → ℂ) (g : Γ) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x, if x * g * x⁻¹ ∈ H then φ (x * g * x⁻¹) else 0
def cj (x : Γ) (B : Subgroup Γ) : Subgroup Γ := B.comap (MulAut.conj x).toMonoidHom
def IsClassOn (A : Subgroup Γ) (a : Γ → ℂ) : Prop := ∀ x ∈ A, ∀ h ∈ A, a (x * h * x⁻¹) = a h
end Gen
section GeneralLinearIntegers
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ
def glReindex {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β) :
    GL α K ≃* GL β K := glEquiv K e
def CuspIso {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) : Prop :=
  ∃ (e : α ≃ β) (φ : lam ≃ₗ[ℂ] mu), ∀ g x, φ (lam.ρ g x) = mu.ρ (glReindex K e g) (φ x)
abbrev IsSupport {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (τ : FDRep ℂ (GL ι K)) : Prop :=
  Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ IsConstituent τ (hcRep K b lam)
def MackeyCusp : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K)),
    Function.Surjective b → Function.Surjective b' →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → (∀ c, Simple (mu c) ∧ IsCuspidal K (mu c)) →
    Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b' mu)) =
      Nat.card {π : Fin s ≃ Fin s' // ∀ c, CuspIso K (lam c) (mu (π c))}
def SupportUnique : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (τ : FDRep ℂ (GL (Fin n) K)), Simple τ → IsSupport K b lam τ → IsSupport K b' mu τ →
    ∃ π : Fin s ≃ Fin s', ∀ c, CuspIso K (lam c) (mu (π c))
def HC.HCSupportExists : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (τ : FDRep ℂ (GL ι K)), Simple τ →
    ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), IsSupport K b lam τ
def SqfreeIrr : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) →
    (∀ c c', CuspIso K (lam c) (lam c') → c = c') → IsIrrRep (hcRep K b lam)
def SqfreeDim : Prop :=
  ∀ (n s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Function.Surjective b →
    (∀ c, (Module.finrank ℂ (lam c) : ℤ) =
      ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) →
    (Module.finrank ℂ (hcSpace K b lam) : ℤ) * ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1) =
      ∏ i ∈ Finset.Icc 1 n, ((Fintype.card K : ℤ) ^ i - 1)
def SqfreeUnique : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (τ τ' : FDRep ℂ (GL (Fin n) K)), Simple τ → Simple τ' → IsSupport K b lam τ → IsSupport K b' mu τ' →
    (∀ c c', CuspIso K (lam c) (lam c') → c = c') →
    (∃ π : Fin s ≃ Fin s', ∀ c, CuspIso K (lam c) (mu (π c))) → Nonempty (τ ≅ τ')
def SqfreeCore : Prop := SqfreeIrr K ∧ SqfreeDim K ∧ SqfreeUnique K
variable {K} in

def reRep {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β)
    (τ : FDRep ℂ (GL α K)) : FDRep ℂ (GL β K) := transp e τ
def convOurs (C : LabelConv K) : LabelConv K := C
def labOurs (C : LabelConv K) (O : LabelMap K C) : LabelMap K (convOurs K C) := O
instance HC.finiteDimensional_hcSpace {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) : FiniteDimensional ℂ (hcSpace K b lam) := by
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  infer_instance
variable {K}
open Classical in

def blkGL {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s) (g : GL ι K) :
    GL {i // b i = c} K :=
  if h : g ∈ parab K b then levi K b c ⟨g, h⟩ else 1
def hcFun {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
    (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (g : GL ι K) : ℂ :=
  ∏ c, χ c (blkGL b c g)
variable (K) in

def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ
variable (K) in

def patSet {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) : Set (GL ι K) :=
  {u | ∀ i j, (i = j → (u : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬ Φ i j → (u : Matrix ι ι K) i j = 0)}
def patChar {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (u : GL ι K) : ℂ :=
  ψ₀ (∑ i, ∑ j, E i j * (u : Matrix ι ι K) i j)
open Classical in

def wh {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (χ : GL ι K → ℂ) : ℂ :=
  ((patSet K Φ).ncard : ℂ)⁻¹ * ∑ u, if u ∈ patSet K Φ then (patChar E ψ₀ u)⁻¹ * χ u else 0
def IsPat {ι : Type} (Φ : ι → ι → Prop) : Prop := (∀ i, ¬ Φ i i) ∧ ∀ i j k, Φ i j → Φ j k → Φ i k
def IsPatChar {ι : Type} (Φ : ι → ι → Prop) (E : ι → ι → K) : Prop :=
  (∀ i j, E i j ≠ 0 → Φ i j) ∧ ∀ i j k, Φ i j → Φ j k → E i k = 0
variable (K) in
open Classical in

def covE {ι : Type} [LT ι] (i j : ι) : K := if i ⋖ j then 1 else 0
variable (K) in

def cutE (N k : ℕ) (i j : Fin N) : K := if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k then 1 else 0
def colPat (N k : ℕ) (i j : Fin N) : Prop := i < j ∧ (j : ℕ) ≠ k
def rowPat (N k a : ℕ) (i j : Fin N) : Prop := i < j ∧ ¬ ((i : ℕ) = a ∧ (j : ℕ) < k)
variable (K) in

def rowE (N k a : ℕ) (i j : Fin N) : K :=
  if ((i : ℕ) = a ∧ (j : ℕ) = k) ∨ ((j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a) then 1 else 0
def chainPat (m k t : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → Prop
  | .inl a, .inl a' => a < a'
  | .inr w, .inr w' => w < w'
  | .inl a, .inr _ => (a : ℕ) < t
  | .inr _, .inl a => t < (a : ℕ)
variable (K) in

def chainE (m k : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → K
  | .inl a, .inl a' => if (a' : ℕ) = a + 1 then 1 else 0
  | .inr w, .inr w' => if (w' : ℕ) = w + 1 then 1 else 0
  | _, _ => 0
def GoodWord {N s : ℕ} (β : Fin N → Fin s) (k : ℕ) : Prop :=
  ∀ i j : Fin N, i < j → (((j : ℕ) < k ∨ k ≤ (i : ℕ)) → β j ≤ β i) ∧ ((i : ℕ) < k → k ≤ (j : ℕ) → β i ≠ β j)
def jPat (N kk s : ℕ) (i j : Fin N) : Prop := i < j ∧ ¬ (s ≤ (i : ℕ) ∧ (j : ℕ) = s + kk)
variable (K) in

def jE (N kk s : ℕ) (i j : Fin N) : K :=
  if ((j : ℕ) = i + 1 ∧ ((j : ℕ) < s ∨ (s ≤ (i : ℕ) ∧ (j : ℕ) < s + kk) ∨ s + kk ≤ (i : ℕ))) ∨
    ((i : ℕ) + 1 = s ∧ (j : ℕ) = s + kk) then 1 else 0
end GeneralLinearIntegers
namespace Lq
def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)
def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹
def eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N IsUniUp (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀
def phiJ {g : ℕ} (kk s : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : ZMod g :=
  (∑ i ∈ Finset.range (s - 1), entN M i (i + 1)) +
    (if 1 ≤ s then entN M (s - 1) (s + kk) + entN M (s + kk) (s + kk + 1) else 0) +
    (∑ i ∈ Finset.range (s - 1), entN M (s + kk + 1 + i) (s + kk + 2 + i)) +
    ∑ a ∈ Finset.range (kk - 1), entN M (s + a) (s + a + 1)
def eJ (g N : ℕ) [NeZero g] (kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0) (phiJ kk s) ψ₀
def wtE {Γ : Type} [Group Γ] [Fintype Γ] (a : MonoidAlgebra ℂ Γ) (τ : FDRep ℂ Γ) : ℝ :=
  ((a * zIdem τ).coeff 1).re / (a.coeff 1).re
def ClauseA : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] [NeZero g] (N kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) (τ : FDRep ℂ (GL (Fin N) (ZMod g))),
    N = kk + 2 * s + 1 → Simple τ →
    0 ≤ ((eU g N ψ₀ * zIdem τ).coeff 1).re ∧ 0 ≤ ((eJ g N kk s ψ₀ * zIdem τ).coeff 1).re ∧
      0 < ((eU g N ψ₀).coeff 1).re ∧ 0 < ((eJ g N kk s ψ₀).coeff 1).re
def ClauseB : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] [NeZero g] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (N : ℕ)
    (ψ₀ : AddChar (ZMod g) ℂ) (τ : FDRep ℂ (GL (Fin N) (ZMod g))) (f : (ZMod g)[X]),
    ψ₀ ≠ 1 → Simple τ → Squarefree f → HasLabelO O τ f →
    wtE (eU g N ψ₀) τ =
      1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod
def ClauseL : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] [NeZero g] (N kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) (τ : FDRep ℂ (GL (Fin N) (ZMod g))),
    ψ₀ ≠ 1 → N = kk + 2 * s + 1 → Simple τ →
    (1 - 1 / (g : ℝ)) * wtE (eU g N ψ₀) τ ≤ wtE (eJ g N kk s ψ₀) τ
def ClauseD : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] [NeZero g] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (N kk s : ℕ)
    (ψ₀ : AddChar (ZMod g) ℂ) (τ : FDRep ℂ (GL (Fin N) (ZMod g))) (f : (ZMod g)[X]),
    ψ₀ ≠ 1 → N = kk + 2 * s + 1 → Simple τ → Squarefree f → HasLabelO O τ f →
    wtE (eJ g N kk s ψ₀) τ ≤ (1 + 1 / (g : ℝ)) ^ N * wtE (eU g N ψ₀) τ
def LqClauses : Prop := ClauseA ∧ ClauseB ∧ ClauseL ∧ ClauseD
end Lq
end ReciprocityTheory.Ty.Fin


