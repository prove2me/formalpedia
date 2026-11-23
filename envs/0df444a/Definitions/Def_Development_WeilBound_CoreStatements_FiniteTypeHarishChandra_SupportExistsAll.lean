-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- name    : Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:34.165828+00:00
-- url     : https://prove2.me/theorems/d8350c1d-4de7-4b52-9983-a60ea0e34e20
-- title:
--   Support Exists All
-- statement:
--   Definitions and structural lemmas for Support Exists All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/SupportExistsAll.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_FiniteDimensionalHcSpace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
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
namespace ReciprocityTheory.Ty.Fin.St
def SimpleIffIrr : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrr τ.ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v)
def SchurScalar : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V),
    (∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ c : Γ → ℂ, (∀ g k, c (k * g * k⁻¹) = c g) →
    ∃ μ : ℂ, ∑ g, c g • ρ g = μ • (1 : Module.End ℂ V)
def CentralIdemAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ →
    σ.asAlgebraHom (centralIdem ρ) = (open Classical in if Nonempty (Representation.Equiv ρ σ) then 1 else 0)
def SepIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (x : MonoidAlgebra ℂ Γ), (∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = 0) → x = 0
def ZIdemFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → ¬ Nonempty (τ ≅ σ) → zIdem τ * zIdem σ = 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → Nonempty (τ ≅ σ) → Representation.asAlgebraHom σ.ρ (zIdem τ) = 1) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (I : Type) [Fintype I] (V : I → FDRep ℂ Γ), (∀ i, Simple (V i)) →
    (∀ i j, Nonempty (V i ≅ V j) → i = j) → (∀ W : FDRep ℂ Γ, Simple W → ∃ i, Nonempty (W ≅ V i)) → ∑ i, zIdem (V i) = 1
def ZIdemActs : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → (Representation.asAlgebraHom σ.ρ (zIdem τ) ≠ 0 ↔ ∃ φ : τ ⟶ σ, φ ≠ 0)
def PiChar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] (V : ∀ i, FDRep ℂ (G i)) (x : ∀ i, G i),
    (Mk.piTensorRep V).character x = ∏ i, (V i).character (x i)
def IntwIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W),
    (Module.finrank ℂ (Intw ρ σ) : ℂ) = ip Set.univ ρ.character σ.character
def MaschkeFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Simple τ →
    (IsConstituent τ ρ ↔ ∃ ψ ∈ Intw ρ τ.ρ, ψ ≠ 0)) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), Simple τ → IsConstituent τ ρ → IsConstituent τ σ →
    Module.finrank ℂ (Intw ρ σ) ≠ 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V), Module.finrank ℂ (Intw ρ ρ) = 1 → IsIrr ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ → Module.finrank ℂ (Intw ρ σ) ≠ 0 → RepIso ρ σ
def FrobIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (A : Subgroup Γ) (a c : Γ → ℂ), (∀ x g, c (x * g * x⁻¹) = c g) →
    ip Set.univ (indF A a) c = ip (A : Set Γ) a c ∧ ip Set.univ c (indF A a) = ip (A : Set Γ) c a
def MackeyIp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (A B : Subgroup Γ) (a b : Γ → ℂ), IsClassOn A a → IsClassOn B b →
    ∀ (R : Type) [Fintype R] (g : R → Γ),
    (∀ r r', (∃ β ∈ B, ∃ α ∈ A, g r' = β * g r * α) → r = r') →
    (∀ x, (∃ r, ∃ β ∈ B, ∃ α ∈ A, x = β * g r * α) ∨
      ∃ y, (∃ β ∈ B, ∃ α ∈ A, x = β * y * α) ∧ ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) = 0) →
    ip (A : Set Γ) a (indF B b) = ∑ r, ip ((A ⊓ cj (g r) B : Subgroup Γ) : Set Γ) a (fun h => b (g r * h * (g r)⁻¹))
def HCChar : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (hcRep K b lam).character = indF (parab K b) (hcFun b fun c => (lam c).character) ∧
      IsClassOn (parab K b) (hcFun b fun c => (lam c).character)
def HCDim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    Module.finrank ℂ (hcSpace K b lam) * Nat.card (parab K b) = Nat.card (GL ι K) * ∏ c, Module.finrank ℂ (lam c)
def CardParab : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι],
    ((Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1)) ∧
    ∀ (s : ℕ) (b : ι → Fin s), Nat.card (parab K b) =
      Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} * ∏ c, Nat.card (GL {i // b i = c} K) ∧
      (Fintype.card ι).choose 2 = Fintype.card {p : ι × ι // b p.1 < b p.2} + ∑ c, (Fintype.card {i // b i = c}).choose 2
def SqfreeDimAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], SqfreeDim K
def PmFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι),
    (∀ i j, (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0) ∧
    (∀ g : GL ι K, pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g) ∧
    (∀ (s : ℕ) (b : ι → Fin s), cj (pm K σ) (parab K b) = parab K (b ∘ σ)) ∧
    ∀ (s : ℕ) (b : ι → Fin s) (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (g : GL ι K),
      hcFun b χ (glEquiv K σ g) =
        hcFun (b ∘ σ) (fun c x => χ c (glEquiv K (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) x)) g
def BruhatTwo : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (n : ℕ),
    (∀ (s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s') (g : GL (Fin n) K),
      ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b', ∃ α ∈ parab K b, g = β * pm K σ * α) ∧
    ∀ (s : ℕ) (b : Fin n → Fin s) (g : GL (Fin n) K),
      ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b, ∃ u ∈ patSet K (fun i j : Fin n => i < j), g = β * pm K σ * u
def BruhatUniq : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι),
    (∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) →
    ∀ c c', Fintype.card {i // b i = c ∧ b' (σ i) = c'} = Fintype.card {i // b i = c ∧ b' (τ i) = c'}
def CuspVanish : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → (∃ i j, b i = b j ∧ β i ≠ β j) →
    ∀ (H : Subgroup (GL ι K)) (F : GL ι K → ℂ), H ≤ parab K b →
      (∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) → u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) →
      (open Classical in ∑ h, if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0
def SamePart : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s s' : ℕ) (b : ι → Fin s) (π : Fin s ≃ Fin s')
    (χ : ∀ c : Fin s, GL {i // b i = c} K → ℂ) (ψ : ∀ c : Fin s', GL {i // (π ∘ b) i = c} K → ℂ),
    ip ((parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)) : Set (GL ι K)) (hcFun b χ) (hcFun (π ∘ b) ψ) =
      ∏ c, ip Set.univ (χ c) (fun x => ψ (π c) (glEquiv K
        (Equiv.subtypeEquivRight (p := fun i => b i = c) (q := fun i => (π ∘ b) i = π c) fun _ => π.injective.eq_iff.symm) x))
def IpCuspIso : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β), Simple lam → Simple mu →
    (ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0)) ∧
    (CuspIso K lam mu ↔ Nonempty (transp e lam ≅ mu))
def MackeyAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], MackeyCusp K
def CuspIsoFacts : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (α β γ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (lam lam' : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (nu : FDRep ℂ (GL γ K)) (e : α ≃ β),
    (CuspIso K lam mu → CuspIso K mu lam) ∧ (CuspIso K lam mu → CuspIso K mu nu → CuspIso K lam nu) ∧
    (Nonempty (lam ≅ lam') → CuspIso K lam lam') ∧ CuspIso K lam (reRep e lam) ∧
    ∀ g : GL β K, glReindex K e (glReindex K e.symm g) = g
def FromMackey : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], MackeyCusp K → SupportUnique K ∧ SqfreeIrr K ∧ SqfreeUnique K
def ProdSimpleAll : Prop :=
  PI.GreenHCLabel.ProdSimple
def JacquetAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)), Simple τ →
    ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
      (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ Φ ≠ 0 ∧
      ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ
def SupportExistsAll : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K], HC.HCSupportExists K
def MirrorsOf : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C), HC.HCSupportExists K → SupportUnique K → SqfreeCore K →
    (HCLabelO O ∧ (CuspParamO O → LabelSurjO O ∧ SqfreeO O))
def PatGroup : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop), IsPat Φ →
    (∃ H : Subgroup (GL ι K), (H : Set (GL ι K)) = patSet K Φ) ∧
    (patSet K Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} ∧
    ∀ (E : ι → ι → K) (ψ₀ : AddChar K ℂ), IsPatChar Φ E →
      (∀ u ∈ patSet K Φ, ∀ v ∈ patSet K Φ, patChar E ψ₀ (u * v) = patChar E ψ₀ u * patChar E ψ₀ v) ∧
      patChar E ψ₀ (1 : GL ι K) = 1 ∧ (∀ u ∈ patSet K Φ, patChar E ψ₀ u⁻¹ = (patChar E ψ₀ u)⁻¹) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (GL ι K) V), ∃ m : ℕ, wh Φ E ψ₀ ρ.character = m
def WhSym : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (Φ : κ → κ → Prop) (E : κ → κ → K)
    (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ),
    (∀ e : ι ≃ κ, wh (fun i j => Φ (e i) (e j)) (fun i j => E (e i) (e j)) ψ₀ (fun x => χ (glEquiv K e x)) = wh Φ E ψ₀ χ) ∧
    ((∀ x g, χ (x * g * x⁻¹) = χ g) →
      (∀ (e e' : ι ≃ κ) (x : GL ι K), χ (glEquiv K e x) = χ (glEquiv K e' x)) ∧
      ∀ t : κ → Kˣ, wh Φ (fun i j => (t i : K) * E i j * ((t j)⁻¹ : Kˣ)) ψ₀ χ = wh Φ E ψ₀ χ)
def RootExchange : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (W : ι → Prop) (p q : ι)
    (χ : GL ι K → ℂ), IsPat Φ → ψ₀ ≠ 1 → (∀ x g, χ (x * g * x⁻¹) = χ g) →
    (∀ w, W w → Φ p w ∧ Φ w q) → E p q ≠ 0 → (∀ i j, E i j ≠ 0 → Φ i j) → (∀ w, W w → E p w = 0 ∧ E w q = 0) →
    (∀ w z, W w → Φ w z → Φ z q → W z) → (∀ w z, W w → Φ p z → Φ z w → W z) →
    (∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q ∧ W j) →
    wh (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) E ψ₀ χ = wh (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) E ψ₀ χ
def ChainIndep : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (m k t : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin m ⊕ Fin k) K → ℂ), ψ₀ ≠ 1 →
    (∀ x g, χ (x * g * x⁻¹) = χ g) → t < m →
    wh (chainPat m k t) (chainE K m k) ψ₀ χ = wh (chainPat m k 0) (chainE K m k) ψ₀ χ
def RowToCol : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin N) K → ℂ), ψ₀ ≠ 1 → (∀ x g, χ (x * g * x⁻¹) = χ g) →
    (∀ k a, a < k → k < N →
      wh (rowPat N k a) (rowE K N k a) ψ₀ χ = wh (colPat N (k - 1 - a)) (cutE K N (k - 1 - a)) ψ₀ χ) ∧
    ∀ kk s, N = kk + 2 * s + 1 → wh (jPat N kk s) (jE K N kk s) ψ₀ χ = wh (colPat N kk) (cutE K N kk) ψ₀ χ
def ColRec : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin N) K → ℂ), ψ₀ ≠ 1 → (∀ x g, χ (x * g * x⁻¹) = χ g) → k < N →
    wh (colPat N k) (cutE K N k) ψ₀ χ = wh (fun i j : Fin N => i < j) (cutE K N k) ψ₀ χ +
      ((Fintype.card K : ℂ) - 1) * ∑ a ∈ Finset.range k, wh (rowPat N k a) (rowE K N k a) ψ₀ χ
def CuspWh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin d) K)), ψ₀ ≠ 1 → IsCuspidal K τ →
    (Module.finrank ℂ τ : ℂ) = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ τ.character *
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1)
def WhTerm : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N s k : ℕ) (β : Fin N → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // β i = c} K)) (ψ₀ : AddChar K ℂ)
    (U : Subgroup (GL (Fin N) K)), (U : Set (GL (Fin N) K)) = patSet K (fun i j : Fin N => i < j) → ψ₀ ≠ 1 →
    (∀ c, IsCuspidal K (lam c) ∧ (Module.finrank ℂ (lam c) : ℤ) =
      ∏ i ∈ Finset.Ico 1 (Fintype.card {i // β i = c}), ((Fintype.card K : ℤ) ^ i - 1)) →
    ip ((U ⊓ parab K β : Subgroup (GL (Fin N) K)) : Set (GL (Fin N) K)) (patChar (cutE K N k) ψ₀)
      (hcFun β fun c => (lam c).character) = (open Classical in if GoodWord β k then 1 else 0)
def GoodCount : Prop :=
  (∀ (N s k : ℕ) (b : Fin N → Fin s),
    Nat.card {β : Fin N → Fin s // (∃ σ : Equiv.Perm (Fin N), β = b ∘ σ) ∧ GoodWord β k} ≤ N.choose k ∨ N ≤ k) ∧
  (∀ (N s : ℕ) (b : Fin N → Fin s),
    Nat.card {β : Fin N → Fin s // (∃ σ : Equiv.Perm (Fin N), β = b ∘ σ) ∧ GoodWord β 0} = 1)
def HCWh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (N s k : ℕ) (b : Fin N → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → (∀ c, IsCuspidal K (lam c) ∧ (Module.finrank ℂ (lam c) : ℤ) =
      ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) →
    wh (fun i j : Fin N => i < j) (cutE K N k) ψ₀ (hcRep K b lam).character =
      Nat.card {β : Fin N → Fin s // (∃ σ : Equiv.Perm (Fin N), β = b ∘ σ) ∧ GoodWord β k}
def RecSolve : Prop :=
  ∀ (q : ℝ) (N : ℕ) (n D : ℕ → ℝ), 1 ≤ q → (∀ i, i < N → 0 ≤ D i) →
    (∀ k, k < N → n k = D k + (q - 1) * ∑ a ∈ Finset.range k, n (k - 1 - a)) → ∀ k, k < N →
    (1 - 1 / q) * q ^ k * D 0 ≤ n k ∧ ((∀ i, i < N → D i ≤ N.choose i) → n k ≤ q ^ k * (1 + 1 / q) ^ N)
def WtForm : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] [NeZero g] (N : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) (τ : FDRep ℂ (GL (Fin N) (ZMod g))),
    ((Lq.eU g N ψ₀ * zIdem τ).coeff 1 = (Module.finrank ℂ τ : ℂ) / Nat.card (GL (Fin N) (ZMod g)) *
        wh (fun i j : Fin N => i < j) (cutE (ZMod g) N 0) ψ₀ τ.character ∧
      (Lq.eU g N ψ₀).coeff 1 = ((g : ℂ) ^ N.choose 2)⁻¹) ∧
    ∀ kk s, N = kk + 2 * s + 1 →
      (Lq.eJ g N kk s ψ₀ * zIdem τ).coeff 1 = (Module.finrank ℂ τ : ℂ) / Nat.card (GL (Fin N) (ZMod g)) *
        wh (jPat N kk s) (jE (ZMod g) N kk s) ψ₀ τ.character ∧
      (Lq.eJ g N kk s ψ₀).coeff 1 = (g : ℂ) ^ kk * ((g : ℂ) ^ N.choose 2)⁻¹ ∧
      IsPat (jPat N kk s) ∧ IsPatChar (jPat N kk s) (jE (ZMod g) N kk s)
def ClauseAL : Prop :=
  Lq.ClauseA ∧ Lq.ClauseL
def ClauseBD : Prop :=
  (∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C), CuspParamO O ∧ SqfreeO O) → Lq.ClauseB ∧ Lq.ClauseD
end ReciprocityTheory.Ty.Fin.St


