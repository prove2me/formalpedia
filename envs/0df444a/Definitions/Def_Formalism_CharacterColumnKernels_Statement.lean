-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- name    : Formalism_CharacterColumnKernels_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:38.907783+00:00
-- url     : https://prove2.me/theorems/0fd8e64d-93ac-43e2-99e3-d1b4d7028a26
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.NG
section Idem
variable {T A : Type*} [CommRing T] [Ring A] [Algebra T A]
def Eop (x : A) {t : ℕ} (r : Fin (t + 1) → T) : A :=
  aeval x (∏ i ∈ univ.erase (0 : Fin (t + 1)), (X - C (r i)))
def delta {t : ℕ} (r : Fin (t + 1) → T) : T :=
  ∏ i ∈ univ.erase (0 : Fin (t + 1)), (r 0 - r i)
def Roots (x : A) {t : ℕ} (r : Fin (t + 1) → T) : Prop :=
  aeval x (∏ i, (X - C (r i))) = 0
def StatEopLeft : Prop :=
  ∀ (T A : Type*) [CommRing T] [Ring A] [Algebra T A] (x : A) (t : ℕ) (r : Fin (t + 1) → T), Roots x r →
    x * Eop x r = algebraMap T A (r 0) * Eop x r
def StatEopSq : Prop :=
  ∀ (T A : Type*) [CommRing T] [Ring A] [Algebra T A] (x : A) (t : ℕ) (r : Fin (t + 1) → T), Roots x r →
    Eop x r * Eop x r = algebraMap T A (delta r) * Eop x r
end Idem
def StatEopEigen (T A V : Type*) [CommRing T] [Ring A] [Algebra T A] [AddCommGroup V] [Module A V]
    [Module T V] [IsScalarTower T A V] : Prop :=
  ∀ (x : A) (t : ℕ) (r : Fin (t + 1) → T) (c : Fin (t + 1)) (v : V), x • v = r c • v →
    Eop x r • v = (∏ i ∈ univ.erase (0 : Fin (t + 1)), (r c - r i)) • v
def StatPowSubPow : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (x : ℤ), (l : ℤ) ∣ x - 1 → ¬ (l : ℤ) ^ 2 ∣ x - 1 →
    ∀ a b : ℕ, a < b → padicValInt l (x ^ b - x ^ a) = 1 + padicValNat l (b - a)
def StatDeltaVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
    padicValInt l (delta (fun i : Fin (t + 1) => u * (1 + (l : ℤ)) ^ (w + (i : ℕ)))) =
      t + padicValNat l t.factorial
def StatDeltaValLe : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
    padicValInt l (delta (fun i : Fin (t + 1) => u * (1 + (l : ℤ)) ^ (w + (i : ℕ)))) ≤ 2 * t
section Pres
variable {R : Type*} [Ring R] {m g : Type*} [Fintype m] [Fintype g]
def relSpan (Θ : Matrix m g R) : Submodule R (g → R) := Submodule.span R (Set.range Θ)
abbrev Coker (Θ : Matrix m g R) : Type _ := (g → R) ⧸ relSpan Θ
def relMap (O : Type*) [CommRing O] (M : Type*) [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (Θ : Matrix m g R) : (g → M) →ₗ[O] (m → M) where
  toFun v i := ∑ j, Θ i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm]
end Pres
def StatHomCoker : Prop :=
  ∀ (R O M : Type*) [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (m g : Type) [Fintype m] [Fintype g] [DecidableEq g] (Θ : Matrix m g R),
    Nonempty ((Coker Θ →ₗ[R] M) ≃ₗ[O] LinearMap.ker (relMap O M Θ))
def StatDetZero : Prop :=
  ∀ (R K V NN : Type*) [Ring R] [Field K] [AddCommGroup V] [Module K V] [Module R V]
    [SMulCommClass R K V] [FiniteDimensional K V] [AddCommGroup NN] [Module R NN]
    (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R) (n : g → NN),
    Submodule.span R (Set.range n) = ⊤ → (∀ i, ∑ j, Θ i j • n j = 0) →
    ∀ φ : NN →ₗ[R] V, φ ≠ 0 → LinearMap.det (relMap K V Θ) = 0
def StatDetZeroIff : Prop :=
  ∀ (R K V : Type*) [Ring R] [Field K] [AddCommGroup V] [Module K V] [Module R V]
    [SMulCommClass R K V] [FiniteDimensional K V]
    (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R),
    LinearMap.det (relMap K V Θ) = 0 ↔ ∃ φ : Coker Θ →ₗ[R] V, φ ≠ 0
def StatDetZeroColumn : Prop :=
  ∀ (R K V : Type*) [Ring R] [Field K] [AddCommGroup V] [Module K V] [Module R V]
    [SMulCommClass R K V] [FiniteDimensional K V] (I : Submodule R R)
    (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R) (n : g → I),
    Submodule.span R (Set.range n) = ⊤ → (∀ i, ∑ j, Θ i j • n j = 0) →
    ∀ y ∈ I, ∀ v : V, y • v ≠ 0 → LinearMap.det (relMap K V Θ) = 0
section DVR
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
abbrev KO : Type _ := FractionRing O ⧸ (1 : Submodule O (FractionRing O))
def matQ {ι : Type*} [Fintype ι] (A : Matrix ι ι O) : (ι → KO O) →ₗ[O] (ι → KO O) :=
  relMap O (KO O) A
end DVR
def StatLenKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O (LinearMap.ker (matQ O A)) = IsDiscreteValuationRing.addVal O A.det
def bigMat {R O : Type*} [CommRing O] {g d : Type*} (ρ : R → Matrix d d O) (Θ : Matrix g g R) :
    Matrix (g × d) (g × d) O :=
  fun p q => ρ (Θ p.1 q.1) p.2 q.2
def StatDetTri : Prop :=
  ∀ (R O : Type*) [CommRing O] (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (α : Type) [LinearOrder α] (ρ : R → Matrix d d O) (b : d → α),
    (∀ r, (ρ r).BlockTriangular b) → ∀ Θ : Matrix g g R,
    (bigMat ρ Θ).det = ∏ k ∈ univ.image b, (bigMat (fun r => (ρ r).toSquareBlock b k) Θ).det
def congIdeal {T O : Type*} [CommRing T] [CommRing O] (J : Ideal T) (π : T →+* O) : Ideal O :=
  Ideal.map π J
abbrev baseChange {T : Type*} (T' : Type*) [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T) :
    Type _ :=
  T' ⧸ Ideal.map (algebraMap T T') J
def StatCongMem : Prop :=
  ∀ (O T T' : Type*) [CommRing O] [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T)
    (π : T →+* O) (π' : T' →+* O), π'.comp (algebraMap T T') = π →
    ∀ f : T', (Ideal.Quotient.mk (Ideal.map (algebraMap T T') J) f = 0) → π' f ∈ congIdeal J π
def StatPoints : Prop :=
  ∀ (O B Ω : Type*) [CommRing O] [IsDomain O] [CommRing B] [IsReduced B] [Algebra O B]
    [Module.Finite O B] [NoZeroSMulDivisors O B] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ b : B, (∀ φ : B →ₐ[O] Ω, φ b = 0) → b = 0
def vIdeal (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (c : Ideal O) : ℕ∞ :=
  ⨅ x ∈ c, IsDiscreteValuationRing.addVal O x
def StatGlobal : Prop :=
  ∀ (O T T' Ω : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing T]
    [CommRing T'] [Algebra O T] [Algebra O T'] [Algebra T T'] [IsScalarTower O T T']
    [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] (J : Ideal T),
    Function.Injective (algebraMap O Ω) →
    IsReduced (baseChange T' J) → Module.Finite O (baseChange T' J) →
    NoZeroSMulDivisors O (baseChange T' J) →
    ∀ (π : T →+* O) (π' : T' →+* O), π'.comp (algebraMap T T') = π →
    ∀ f : T', (∀ φ : baseChange T' J →ₐ[O] Ω, φ (Ideal.Quotient.mk _ f) = 0) →
    ∀ (R : Type*) (g d : Type) [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
      (α : Type) [LinearOrder α] (ρ : R → Matrix d d O) (b : d → α),
      (∀ r, (ρ r).BlockTriangular b) → ∀ Θ : Matrix g g R, π' f = (bigMat ρ Θ).det →
      vIdeal O (congIdeal J π) ≤
        ∑ k ∈ univ.image b,
          Module.length O (LinearMap.ker (matQ O (bigMat (fun r => (ρ r).toSquareBlock b k) Θ)))
end Formalism.NG


