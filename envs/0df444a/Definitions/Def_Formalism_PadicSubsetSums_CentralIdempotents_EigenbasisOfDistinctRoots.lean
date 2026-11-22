-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:00.367807+00:00
-- url     : https://prove2.me/theorems/7eab3175-fde0-49b4-a021-63d3fe1563f5
-- title:
--   Eigenbasis Of Distinct Roots
-- statement:
--   Definitions and structural lemmas for Eigenbasis Of Distinct Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/EigenbasisOfDistinctRoots.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)
def NormCongrOne : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra ℤ S] [Module.Free ℤ S] [Module.Finite ℤ S] (c : ℤ)
    (π y : S), π = 1 + c • y → c ∣ Algebra.norm ℤ π - 1
def SplitsCompletelyOfCongr : Prop :=
  ∀ (c g : ℕ) (E Kc : Type) [Field E] [NumberField E] [Field Kc] [NumberField Kc]
    [IsCyclotomicExtension {c} ℚ Kc] (_ : E →+* Kc), 0 < c → g.Prime → c ∣ g - 1 →
    ∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
      (g : NumberField.RingOfIntegers E) ∈ P →
      Nat.card (NumberField.RingOfIntegers E ⧸ P) = g ∧
        (g : NumberField.RingOfIntegers E) ∉ P ^ 2
def PrimeToPartEndo : Prop :=
  ∀ (M M' : Type) [CommMonoid M] [Monoid M'] (l : ℕ) (x y : M) (φ : M →* M'), l.Prime →
    IsOfFinOrder x → IsOfFinOrder y →
    primeToPart l (x * y) = primeToPart l x * primeToPart l y ∧
      φ (primeToPart l x) = primeToPart l (φ x)
def PowPolyExists : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (f : K[X])
    (a : ℕ), f.Monic →
    ∃ f' : K[X], f'.Monic ∧ f'.aroots L = (f.aroots L).map (fun x => x ^ a)
def GoodPowStable : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (ι J : Type)
    (N a : ℕ) (f f' : ι → K[X]) (χ : ι → J → Kˣ),
    (∀ d ∈ Finset.Icc 1 N, Nat.Coprime a (Fintype.card K ^ d - 1)) →
    (∀ v, (f' v).Monic ∧ (f' v).aroots L = ((f v).aroots L).map (fun x => x ^ a)) →
    GoodAt K L N f χ → GoodAt K L N f' (fun v j => χ v j ^ a)
def NotMemBBIff : Prop :=
  ∀ g N l : ℕ, 2 ≤ g → l.Prime → l ≠ g →
    (l ∉ BB g N ↔ ∀ d ∈ Finset.Icc 1 N, l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g ^ d)
def ExcludedSimplify : Prop :=
  ∀ (N : ℕ) (Y : ℝ), 1 ≤ N → 1 ≤ Y →
    (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) ≤
      20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4)
def QPThreshold : Prop :=
  ∀ (c d Q m X : ℝ) (N : ℕ), 4 ≤ c → 1 ≤ d → d ≤ c → 0 ≤ Q → Q ≤ c ^ 2 → 0 ≤ m → m ≤ c ^ 2 →
    1 ≤ N → 0 < X → (N : ℝ) ^ 4 * c ^ 500 ≤ (X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4) →
    d ^ 694 * Q ^ 521 + d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) +
      (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ X
def AdmissibleCount : Prop :=
  ∀ (c₀ c X B h P A : ℝ), 0 < c₀ → (2 : ℝ) ^ 14 / c₀ ≤ c → 1 < X → Real.log X ≤ c →
    0 < B → B ≤ 4 * c ^ 3 → 0 < h → h ≤ c ^ 3 →
    c₀ * B ^ (-5 : ℤ) * X / (h * Real.log X) ≤ P → P ≤ 2 * A →
    8 * c ^ (-20 : ℤ) * X ≤ A
open Classical in

def DyadicWindow : Prop :=
  ∀ (P : Finset ℕ) (X κ : ℝ), 0 < X → 0 < κ → (∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ X) →
    8 * κ * X ≤ (P.card : ℝ) →
    ∃ j : ℕ, 1 ≤ j ∧ 2 * κ * X < X / 2 ^ j ∧
      κ * (X / 2 ^ j) ≤
        ((P.filter (fun p : ℕ => X / 2 ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ j))).card : ℝ)
open Classical in

def Prop1FromCount : Prop :=
  ∀ (N : ℕ) (c X : ℝ) (P : Finset ℕ), 21 ≤ N → 1 ≤ c → 0 < X →
    (N : ℝ) ^ 4 * c ^ 500 ≤ (X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4) →
    (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X) → 8 * c ^ (-20 : ℤ) * X ≤ (P.card : ℝ) →
    ∃ Y : ℝ, X * c ^ (-20 : ℤ) ≤ Y ∧ 2 * Y ≤ X ∧
      Y * c ^ (-20 : ℤ) ≤ ((P.filter (fun p : ℕ => Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y)).card : ℝ) ∧
      ∃ g₁ ∈ P, ∃ g₂ ∈ P, g₁ ≠ g₂ ∧ (Y ≤ (g₁ : ℝ) ∧ (g₁ : ℝ) ≤ 2 * Y) ∧
        (Y ≤ (g₂ : ℝ) ∧ (g₂ : ℝ) ≤ 2 * Y) ∧ Disjoint (BB g₁ N) (BB g₂ N)
open Classical in

def LemmaPSubSum : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => IsSubSum σ.partition.parts a)).card ≤ 7 * N.factorial
def eqvSpace {G V ι : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (emb : ι → G) (χ : ι → ℂ) : Submodule ℂ V where
  carrier := {x | ∀ u, ρ (emb u) x = χ u • x}
  add_mem' := by
    intro x y hx hy u
    rw [map_add, hx u, hy u, smul_add]
  zero_mem' := by
    intro u
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro a x hx u
    rw [map_smul, hx u, smul_comm]
open Classical in

def twistedIdem {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    MonoidAlgebra ℂ G :=
  ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) • MonoidAlgebra.of ℂ G (u : G)
def IsIrr {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤
def TraceRegular : Prop :=
  ∀ (K G : Type) [Field K] [Group G] [Fintype G] (e : MonoidAlgebra K G),
    LinearMap.trace K (MonoidAlgebra K G) (LinearMap.mulLeft K e) =
      (Fintype.card G : K) * e.coeff 1
def TwistedIdempotent : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ),
    twistedIdem J χ * twistedIdem J χ = twistedIdem J χ ∧
    (∀ g : G, (twistedIdem J χ).coeff g⁻¹ = (starRingEnd ℂ) ((twistedIdem J χ).coeff g)) ∧
    (twistedIdem J χ).coeff 1 = (Nat.card J : ℂ)⁻¹ ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      LinearMap.range (ρ.asAlgebraHom (twistedIdem J χ)) =
        eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))
def WeightFormula : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (e : MonoidAlgebra ℂ G), e * e = e →
    (e * centralIdem ρ).coeff 1 =
      (Module.finrank ℂ V : ℂ) * (Module.finrank ℂ (LinearMap.range (ρ.asAlgebraHom e)) : ℂ) /
        (Fintype.card G : ℂ)
def WeightOfTwistedIdempotent : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ),
    (twistedIdem J χ * centralIdem ρ).coeff 1 / (twistedIdem J χ).coeff 1 =
      (Nat.card J : ℂ) *
        (Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))) : ℂ) *
        (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)
def CentralIdemSumOne : Prop :=
  ∀ (G I : Type) [Group G] [Fintype G] [Fintype I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, IsIrr (ρ i)) →
    (∀ i j, (∃ φ : V i ≃ₗ[ℂ] V j, ∀ g x, φ (ρ i g x) = ρ j g (φ x)) → i = j) →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ →
      ∃ i, ∃ φ : W ≃ₗ[ℂ] V i, ∀ g x, φ (σ g x) = ρ i g (φ x)) →
    ∑ i, centralIdem (ρ i) = 1
def CentralIdemProduct : Prop :=
  ∀ (G H V W : Type) [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (g : G) (h : H),
    (centralIdem (Representation.tprod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H)))).coeff (g, h) =
      (centralIdem ρ).coeff g * (centralIdem σ).coeff h
def GLCardSplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ),
    Nat.card (GL (Fin N) K) =
      Fintype.card K ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.Icc 1 N, (Fintype.card K ^ i - 1)
def LemmaLWeightU : Prop :=
  ∀ (d : Multiset ℕ) (g : ℕ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g →
    1 / (g : ℝ) ^ d.sum ≤ 1 / (d.map (fun x => (g : ℝ) ^ x - 1)).prod ∧
      (2 * d.sum ≤ g →
        1 / (d.map (fun x => (g : ℝ) ^ x - 1)).prod ≤ (1 + 2 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum)
def rootSet' {n K : Type} [Field K] (Φ : Finset (n × n)) : Set (Matrix n n K) :=
  {u | (∀ a, u a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ Φ → u a b = 0}
def RootSetGroup : Prop :=
  ∀ (n K : Type) [Fintype n] [LinearOrder n] [Field K] [Fintype K] (Φ EE : Finset (n × n)),
    (∀ x ∈ Φ, x.1 < x.2) → (∀ a b c, (a, b) ∈ Φ → (b, c) ∈ Φ → (a, c) ∈ Φ) → EE ⊆ Φ →
    (∀ a b c, (a, b) ∈ Φ → (b, c) ∈ Φ → (a, c) ∉ EE) →
    (1 : Matrix n n K) ∈ rootSet' Φ ∧
    (∀ u ∈ rootSet' (K := K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, u * u' ∈ rootSet' Φ ∧
      ∀ x ∈ EE, (u * u') x.1 x.2 = u x.1 x.2 + u' x.1 x.2) ∧
    (∀ u ∈ rootSet' (K := K) Φ, ∃ u' ∈ rootSet' (K := K) Φ, u * u' = 1 ∧ u' * u = 1) ∧
    Nat.card (rootSet' (K := K) Φ) = Fintype.card K ^ Φ.card
def charRep {H : Type} [Group H] (la : H →* ℂˣ) : Representation ℂ H ℂ :=
  (Module.toModuleEnd ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp la)
def RXHyp {HH : Type} [Group HH] (A C X Y : Subgroup HH) (laX : ↥(A ⊔ C ⊔ X) →* ℂˣ)
    (laY : ↥(A ⊔ C ⊔ Y) →* ℂˣ) : Prop :=
  ((∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) ∧ (∀ y ∈ Y, ∀ c ∈ C, y * c * y⁻¹ ∈ C) ∧
    (∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C) ∧ (∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) ∧
    (∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)) ∧
  (∀ x ∈ X, ∀ y ∈ Y, x⁻¹ * y⁻¹ * x * y ∈ C) ∧
  Function.Bijective (fun q : A × C × X × Y => (q.1 : HH) * q.2.1 * q.2.2.1 * q.2.2.2) ∧
  ((∀ u : ↥(A ⊔ C ⊔ X), (u : HH) ∈ X → laX u = 1) ∧
    (∀ u : ↥(A ⊔ C ⊔ Y), (u : HH) ∈ Y → laY u = 1) ∧
    (∀ (u : ↥(A ⊔ C ⊔ X)) (u' : ↥(A ⊔ C ⊔ Y)), (u : HH) = u' → (u : HH) ∈ A ⊔ C →
      laX u = laY u')) ∧
  ((∀ y ∈ Y, y ≠ 1 → ∃ x ∈ X, ∃ u : ↥(A ⊔ C ⊔ X), (u : HH) = x⁻¹ * y⁻¹ * x * y ∧ laX u ≠ 1) ∧
    (∀ x ∈ X, x ≠ 1 → ∃ y ∈ Y, ∃ u : ↥(A ⊔ C ⊔ X), (u : HH) = x⁻¹ * y⁻¹ * x * y ∧ laX u ≠ 1))
def RootExchange : Prop :=
  ∀ (HH : Type) [Group HH] [Finite HH] (A C X Y : Subgroup HH) (laX : ↥(A ⊔ C ⊔ X) →* ℂˣ)
    (laY : ↥(A ⊔ C ⊔ Y) →* ℂˣ), RXHyp A C X Y laX laY →
    (Representation.ind (A ⊔ C ⊔ X).subtype (charRep laX)).IsIrreducible ∧
    (Representation.ind (A ⊔ C ⊔ Y).subtype (charRep laY)).IsIrreducible ∧
    Nonempty ((Representation.ind (A ⊔ C ⊔ X).subtype (charRep laX)).Equiv
      (Representation.ind (A ⊔ C ⊔ Y).subtype (charRep laY)))
def RootExchangeDim : Prop :=
  ∀ (HH G V : Type) [Group HH] [Finite HH] [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A C X Y : Subgroup HH) (laX : ↥(A ⊔ C ⊔ X) →* ℂˣ)
    (laY : ↥(A ⊔ C ⊔ Y) →* ℂˣ) (j : HH →* G) (ρ : Representation ℂ G V),
    RXHyp A C X Y laX laY →
    Module.finrank ℂ (eqvSpace ρ (fun u : ↥(A ⊔ C ⊔ X) => j u) (fun u => ((laX u : ℂˣ) : ℂ))) =
      Module.finrank ℂ (eqvSpace ρ (fun u : ↥(A ⊔ C ⊔ Y) => j u) (fun u => ((laY u : ℂˣ) : ℂ)))
def besselEdge (s k i j : ℕ) : Prop :=
  (j = i + 1 ∧ (j < s ∨ (s ≤ i ∧ j < s + k) ∨ s + k ≤ i)) ∨ (i + 1 = s ∧ j = s + k)
def besselSet (K : Type) [Field K] (s k N : ℕ) : Set (GL (Fin N) K) :=
  {u | (∀ i, (u : Matrix (Fin N) (Fin N) K) i i = 1) ∧
    (∀ i j, j < i → (u : Matrix (Fin N) (Fin N) K) i j = 0) ∧
    ∀ i j : Fin N, s ≤ (i : ℕ) → (i : ℕ) < s + k → (j : ℕ) = s + k →
      (u : Matrix (Fin N) (Fin N) K) i j = 0}
open Classical in

def besselChar {K : Type} [Field K] (ψ₀ : AddChar K ℂ) (s k N : ℕ) (u : GL (Fin N) K) : ℂ :=
  ψ₀ (∑ i : Fin N, ∑ j : Fin N,
    if besselEdge s k i j then (u : Matrix (Fin N) (Fin N) K) i j else 0)
def besselSpace {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) (s k : ℕ) : Submodule ℂ V :=
  eqvSpace ρ (fun u : besselSet K s k N => (u : GL (Fin N) K))
    (fun u => besselChar ψ₀ s k N (u : GL (Fin N) K))
def BesselCard : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (s k N : ℕ), s + k < N →
    Nat.card (besselSet K s k N) = Fintype.card K ^ (N * (N - 1) / 2 - k)
def RootExchangeDatum : Prop :=
  ∀ (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (s k i : ℕ) (ψ₀ : AddChar K ℂ) (ρ : Representation ℂ (GL (Fin (k + 2 * s + 1)) K) V),
    ψ₀ ≠ 1 → 1 ≤ k → i ≤ s →
    Module.finrank ℂ (besselSpace ρ ψ₀ i k) = Module.finrank ℂ (besselSpace ρ ψ₀ 0 k)
def GelfandGraevMultOne : Prop :=
  ∀ (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (N : ℕ) (ψ₀ : AddChar K ℂ) (ρ : Representation ℂ (GL (Fin N) K) V), ψ₀ ≠ 1 → IsIrr ρ →
    Module.finrank ℂ (besselSpace ρ ψ₀ 0 0) ≤ 1
def GelfandGraevEndDim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n : ℕ) (ψ₀ : AddChar K ℂ)
    (E : Submodule ℂ (GL (Fin n) K → ℂ)), ψ₀ ≠ 1 → 1 ≤ n →
    (∀ φ, φ ∈ E ↔ ∀ u ∈ besselSet K 0 0 n, ∀ u' ∈ besselSet K 0 0 n, ∀ x,
      φ (u * x * u') = besselChar ψ₀ 0 0 n u * besselChar ψ₀ 0 0 n u' * φ x) →
    Module.finrank ℂ E = Fintype.card K ^ n - Fintype.card K ^ (n - 1)
def MirabolicComparison : Prop :=
  ∀ (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (N k : ℕ) (ψ₀ : AddChar K ℂ) (ρ : Representation ℂ (GL (Fin N) K) V), ψ₀ ≠ 1 → 1 ≤ k →
    k + 1 ≤ N →
    (Fintype.card K ^ k - Fintype.card K ^ (k - 1)) * Module.finrank ℂ (besselSpace ρ ψ₀ 0 0) ≤
      Module.finrank ℂ (besselSpace ρ ψ₀ 0 k)
open Classical in

def IrredCountUpperUnit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    d * ((Finset.univ : Finset (Fin d → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card
      ≤ Fintype.card K ^ d - 1
def TypeWeightU : Prop :=
  ∀ (g : ℕ) (D : Finset ℕ) (Nd n : ℕ → ℕ), 2 ≤ g → (∀ d ∈ D, 1 ≤ d) →
    (∀ d ∈ D, d * Nd d ≤ g ^ d - 1) →
    (∏ d ∈ D, ((Nd d).choose (n d) : ℝ) / ((g : ℝ) ^ d - 1) ^ (n d)) ≤
      1 / ∏ d ∈ D, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))
def ComparisonTransfer : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (wU wJ : ∀ v, T v → ℝ) (g : ℝ) (A : Finset (∀ v, T v)), 1 ≤ g →
    (∀ v t, 0 ≤ wU v t) → (∀ v, ∑ t, wU v t = 1) → (∀ v, ∑ t, wJ v t = 1) →
    (∀ v t, (1 - 1 / g) * wU v t ≤ wJ v t) →
    ∑ x ∈ A, ∏ v, wJ v (x v) ≤ ∑ x ∈ A, ∏ v, wU v (x v) + (Fintype.card ι : ℝ) / g
open Classical in

def sqWeight {K : Type} [Field K] [Fintype K] (f : K[X]) : ℝ :=
  ((UniqueFactorizationMonoid.normalizedFactors f).map
    (fun P => ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹)).prod
open Classical in

def sqSet (K : Type) [Field K] [Fintype K] (N : ℕ) : Finset (Fin N → K) :=
  Finset.univ.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)
open Classical in

def degType {K : Type} [Field K] (f : K[X]) : Multiset ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree
def SqMassLeOne : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (M : ℕ), ∑ c ∈ sqSet K M, sqWeight (monicOf c) ≤ 1
def SqMassLower : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 1 ≤ N →
    1 - 2 / (Fintype.card K : ℝ) ≤ ∑ c ∈ sqSet K N, sqWeight (monicOf c)
open Classical in

def DivisorBound : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (h : K[X]), h.Monic → Squarefree h →
    h.coeff 0 ≠ 0 → h.natDegree ≤ N →
    ∑ c ∈ (sqSet K N).filter (fun c => h ∣ monicOf c), sqWeight (monicOf c) ≤ sqWeight h
open Classical in

def TypeWeightExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ∑ c ∈ (sqSet K N).filter (fun c => ∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d),
        sqWeight (monicOf c) =
      ∏ d ∈ Finset.Icc 1 N,
        (((((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) : ℕ) : ℝ) /
          ((Fintype.card K : ℝ) ^ d - 1) ^ (n d)
open Classical in

def TypeSetWeight : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (A : Multiset ℕ → Prop),
    ∑ c ∈ (sqSet K N).filter (fun c => A (degType (monicOf c))), sqWeight (monicOf c) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => A σ.partition.parts)).card : ℝ) / (N.factorial : ℝ)
def PrimeFactorsLogTwo : Prop :=
  ∀ g δ : ℕ, 2 ≤ g → 1 ≤ δ →
    (((g ^ δ - 1).primeFactors.card : ℕ) : ℝ) ≤ (δ : ℝ) * Real.logb 2 g
open Classical in

def SameFactorCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (δ l : ℕ),
    l.Prime → 2 ≤ δ →
    l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ →
    (((Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L))).card : ℝ) ≤
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4)
open Classical in

def CrossFactorCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (δ l : ℕ)
    (P' : K[X]), l.Prime → 1 ≤ δ → Irreducible P' → P'.coeff 0 ≠ 0 →
    l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ →
    (((Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L, ∃ y ∈ P'.rootSet L,
        primeToPart l x = primeToPart l y)).card : ℝ) ≤
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4)
def SeriesBounds : Prop :=
  ∀ (u : ℝ) (N : ℕ), 0 ≤ u → u ≤ 1 / 8 →
    ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * u ^ δ ≤ 6 * u ^ 2 ∧
      ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * u ^ δ ≤ 17 / 10 * u
open Classical in

def LocalEstimateII : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (N : ℕ),
    2 ^ 12 ≤ Fintype.card K →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ l : ℕ, l.Prime ∧ l ∉ BB (Fintype.card K) N ∧
        ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)), sqWeight (monicOf c) ≤
      23 * Real.log (Fintype.card K) / Real.sqrt (Fintype.card K)
def PrimePowerOrderShare : Prop :=
  ∀ g q₁ d : ℕ, 2 ≤ g → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 → 16 ≤ max q₁ d →
    16 ∣ g - 1 → q₁ ∣ g - 1 → d ∣ g - 1 →
    (∑ l ∈ (g - 1).primeFactors, ((l ^ padicValNat l (g - 1) : ℕ) : ℝ)) / ((g - 1 : ℕ) : ℝ) ≤
      1 / (4 * (min q₁ d : ℕ))
def PrimePowerOrderCount : Prop :=
  ∀ g δ : ℕ, 2 ≤ g → 4 ∣ g - 1 → 1 ≤ δ →
    ∑ l ∈ (g ^ δ - 1).primeFactors, l ^ padicValNat l (g ^ δ - 1) ≤
      δ * (g - 1) + (g ^ δ - 1) / (g - 1)
open Classical in

def LocalEstimateIII : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (N q₁ d : ℕ)
    (c₀ : Kˣ), 1 ≤ N → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 → 16 ≤ max q₁ d →
    16 ∣ Fintype.card K - 1 → q₁ ∣ Fintype.card K - 1 → d ∣ Fintype.card K - 1 →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ l : ℕ, l.Prime ∧ l ≠ Fintype.card K ∧
        ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))), sqWeight (monicOf c) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((Fintype.card K : ℝ) - 1)
open Classical in

def LocalEstimateIV : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N a : ℕ), 0 < a → a < N →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a),
      sqWeight (monicOf c) ≤ 7 / 8
open Classical in

def LocalEstimateV : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 100 ≤ N →
    ∑ c ∈ (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧
        P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N), sqWeight (monicOf c) ≤
      1 - 1 / (5 * Real.log N)
open Classical in

def PropW : Prop :=
  ∀ (K L ι J : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] [Fintype ι]
    [Fintype J] (N q₁ d : ℕ) (χ : ι → J → Kˣ) (P : (Fin N → K) → ℝ),
    100 ≤ N → 2 ^ 12 ≤ Fintype.card K → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 →
    16 ≤ max q₁ d → 16 ∣ Fintype.card K - 1 → q₁ ∣ Fintype.card K - 1 →
    d ∣ Fintype.card K - 1 →
    (∀ c, 0 ≤ P c) → ∑ c, P c = 1 → (∀ c ∈ sqSet K N, P c = sqWeight (monicOf c)) →
    ∑ x ∈ (Finset.univ : Finset (ι → Fin N → K)).filter
        (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ), ∏ v, P (x v) ≤
      2 * (Fintype.card ι : ℝ) / (Fintype.card K : ℝ) +
      23 * (Fintype.card ι : ℝ) * Real.log (Fintype.card K) / Real.sqrt (Fintype.card K) +
      2 * (Fintype.card ι : ℝ) * (Fintype.card J : ℝ) *
        (1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((Fintype.card K : ℝ) - 1)) +
      (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι +
      Real.exp (-(Fintype.card ι : ℝ) / (5 * Real.log N))
def ShareFromCount : Prop :=
  ∀ (ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad : ℝ), 0 ≤ ε → ε < 1 → 0 < Dstar →
    0 ≤ PP₁ → PP₁ ≤ W₁ → 0 ≤ PP₂ → PP₂ ≤ W₂ → |Dall - Dstar| ≤ ε * Dstar →
    |D₁ - PP₁ * Dstar| ≤ ε * (PP₁ * Dstar) → |D₂ - PP₂ * Dstar| ≤ ε * (PP₂ * Dstar) →
    bad ≤ D₁ + D₂ → bad / Dall ≤ (1 + ε) / (1 - ε) * (W₁ + W₂)
def BadRankUnion : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p₁ p₂ : V →ₗ[k] V), p₁ ∘ₗ p₁ = p₁ → p₂ ∘ₗ p₂ = p₂ → p₁ ∘ₗ p₂ = p₂ ∘ₗ p₁ →
    Module.finrank k (LinearMap.range (p₁ + p₂ - p₁ ∘ₗ p₂)) ≤
      Module.finrank k (LinearMap.range p₁) + Module.finrank k (LinearMap.range p₂)
def NumbersDominant : Prop :=
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
    x ^ C * Real.exp (-x ^ (ε / 6)) ≤ 1 / 8 * Real.exp (-x ^ (ε / 7))
def IdempotentPositiveType : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (e : MonoidAlgebra ℂ G), e * e = e →
    (∀ x : G, e.coeff x⁻¹ = (starRingEnd ℂ) (e.coeff x)) →
    (Matrix.of fun x y : G => e.coeff (x⁻¹ * y)).PosSemidef
def CyclotomicIrredUnramified : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
      (p : NumberField.RingOfIntegers E) ∈ P → (p : NumberField.RingOfIntegers E) ∉ P ^ 2) →
    Irreducible (Polynomial.cyclotomic p E)
def FiniteOrderTraceFull : Prop :=
  ∀ (K : Type) [Field K] (_ : K →+* ℂ) (n m : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < m →
    γ ^ m = 1 → γ.trace = (n : K) → γ = 1
def EigenbasisOfDistinctRoots : Prop :=
  ∀ (k V ι : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Fintype ι]
    (t : Module.End k V) (c : ι → k), Function.Injective c →
    LinearMap.charpoly t = ∏ i, (X - C (c i)) →
    ∃ b : Module.Basis ι k V, ∀ i, t (b i) = c i • b i
def FrobPermutesLines : Prop :=
  ∀ (k V ι : Type) [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (t : Module.End k V) (Φ : V ≃ₗ[k] V) (g : ℕ) (b : Module.Basis ι k V) (c : ι → k)
    (π : Equiv.Perm ι), Function.Injective c → (∀ i, t (b i) = c i • b i) →
    (∀ x, Φ (t x) = (t ^ g) (Φ x)) → (∀ i, c (π i) ^ g = c i) →
    ∀ i, ∃ a : k, a ≠ 0 ∧ Φ (b i) = a • b (π i)
def SolvableRestrictIrred : Prop :=
  ∀ (K V G ι : Type) [Field K] [AddCommGroup V] [Module K V] [Group G] [Fintype ι]
    [DecidableEq ι] (ρ : Representation K G V) (H : Subgroup G) [H.Normal] (t Φ : G)
    (b : Module.Basis ι K V) (c : ι → K) (π : Equiv.Perm ι) (p : ℕ),
    t ∈ H → Function.Injective c → (∀ i, ρ t (b i) = c i • b i) →
    (∀ i, ∃ a : K, ρ Φ (b i) = a • b (π i)) →
    (∀ W : Submodule K V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    Group.IsSolvable (G ⧸ H) → p.Prime → p ∈ π.cycleType → Fintype.card ι < 2 * p →
    p + 3 ≤ Fintype.card ι →
    ∀ W : Submodule K V, (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤
def FixedByAutInField : Prop :=
  ∀ (F : IntermediateField ℚ ℂ) (z : ℂ), IsAlgebraic ℚ z → (∀ σ : ℂ ≃ₐ[F] ℂ, σ z = z) → z ∈ F
def CommutesWithIdempotents : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (MM : Submodule R V)
    (a eps pr : V →ₗ[R] V), (∀ x ∈ MM, a x ∈ MM) → a ∘ₗ eps = eps ∘ₗ a → a ∘ₗ pr = pr ∘ₗ a →
    (∀ x ∈ MM ⊓ LinearMap.range eps, a x ∈ MM ⊓ LinearMap.range eps) ∧
    (∀ x ∈ MM ⊓ LinearMap.range eps ⊓ LinearMap.range pr,
      a x ∈ MM ⊓ LinearMap.range eps ⊓ LinearMap.range pr) ∧
    (∀ x ∈ (MM ⊓ LinearMap.range eps).map pr, a x ∈ (MM ⊓ LinearMap.range eps).map pr)
def DropLatticeIncl : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (Mt : Submodule R V)
    (e pr : V →ₗ[R] V), e ∘ₗ e = e → pr ∘ₗ pr = pr →
    Mt ⊓ LinearMap.range pr ⊓ LinearMap.range e ≤ (Mt.map pr).map e
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


