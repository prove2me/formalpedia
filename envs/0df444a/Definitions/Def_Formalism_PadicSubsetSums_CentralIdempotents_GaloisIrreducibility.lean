-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:28.710499+00:00
-- url     : https://prove2.me/theorems/487c1c85-403b-45d2-9cf5-f2999126cfd3
-- title:
--   Galois Irreducibility
-- statement:
--   Definitions and structural lemmas for Galois Irreducibility, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisIrreducibility.lean

import Mathlib
import Definitions.Def_Formalism_GaloisIrreducibility_Statement
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
open Classical in

def BB (g N : ℕ) : Finset ℕ :=
  insert g ((Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))))
def BBCard : Prop :=
  ∀ g N : ℕ, 2 ≤ g → (BB g N).card ≤ 3 * N + 1
def BBDivides : Prop :=
  ∀ (l g d j : ℕ) (Y : ℝ), l.Prime → 1 ≤ d → 2 ≤ g → Y ≤ (g : ℝ) →
    g ^ d < l ^ (4 * padicValNat l (g ^ d - 1)) →
    Y < (l : ℝ) ^ (4 * j) → (∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y) →
    l ^ j ∣ g ^ d - 1
def ExcludedCount : Prop :=
  ∀ (N g₁ : ℕ) (Y : ℝ) (S : Finset ℕ), 1 ≤ N → 1 ≤ Y → g₁.Prime →
    (∀ g ∈ S, g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ ¬ Disjoint (BB g₁ N) (BB g N)) →
    (S.card : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))
def Prop1Core : Prop :=
  ∀ (N : ℕ) (Y : ℝ) (P : Finset ℕ), 1 ≤ N → 1 ≤ Y →
    (∀ g ∈ P, g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y) →
    ((3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < P.card) →
    ∃ g₁ ∈ P, ∃ g₂ ∈ P, g₁ ≠ g₂ ∧ Disjoint (BB g₁ N) (BB g₂ N)
def OutsideOneBB : Prop :=
  ∀ g₁ g₂ N l : ℕ, Disjoint (BB g₁ N) (BB g₂ N) → l ∉ BB g₁ N ∨ l ∉ BB g₂ N
def PowerResidueCountBound : Prop :=
  ∀ (l j D : ℕ), l.Prime → 1 ≤ D →
    ((Finset.range (l ^ j)).filter (fun x => x ^ D ≡ 1 [MOD l ^ j])).card ≤ 2 * D
def LogCardProductGLBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, Fintype (k v)] (N : ℕ)
    (Y : ℝ), (∀ v, (Fintype.card (k v) : ℝ) ≤ 2 * Y) →
    Real.log (Nat.card (∀ v, GL (Fin N) (k v))) ≤
      (Fintype.card ι : ℝ) * (N : ℝ) ^ 2 * Real.log (2 * Y)
def primeToPart {M : Type*} [Monoid M] (l : ℕ) (x : M) : M :=
  x ^ ((ordProj[l] (orderOf x)) ^ Nat.totient (ordCompl[l] (orderOf x)))
def PrimeToPartSpec : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x : M), l.Prime → IsOfFinOrder x →
    orderOf (primeToPart l x) = ordCompl[l] (orderOf x) ∧
      ∃ a : ℕ, x ^ (l ^ a) = primeToPart l x ^ (l ^ a)
def PrimeToPartEqIff : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x y : M), l.Prime → IsOfFinOrder x → IsOfFinOrder y →
    (primeToPart l x = primeToPart l y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a))
def GoodAt (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {ι J : Type} (N : ℕ)
    (f : ι → K[X]) (χ : ι → J → Kˣ) : Prop :=
  (∀ v, (f v).Monic ∧ (f v).natDegree = N ∧ (f v).coeff 0 ≠ 0) ∧
  (∀ v, Squarefree (f v)) ∧
  (∀ l : ℕ, l.Prime → l ∉ BB (Fintype.card K) N →
    ∀ v, Set.InjOn (primeToPart l) ((f v).rootSet L)) ∧
  (∀ l : ℕ, l.Prime → l ≠ Fintype.card K → ∀ v j, ∀ x ∈ (f v).rootSet L,
    primeToPart l x ≠ primeToPart l (algebraMap K L (χ v j : K)) ∧
    primeToPart l x ≠ primeToPart l (algebraMap K L ((χ v j)⁻¹ : Kˣ))) ∧
  (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ h : K[X], h ∣ f v ∧ h.natDegree = a) ∧
  (∃ v, ∃ P : K[X], Irreducible P ∧ P ∣ f v ∧ P.natDegree.Prime ∧
    N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N)
def Good (K₁ L₁ K₂ L₂ : Type) [Field K₁] [Fintype K₁] [Field L₁] [Algebra K₁ L₁]
    [Field K₂] [Fintype K₂] [Field L₂] [Algebra K₂ L₂] {ι₁ J₁ ι₂ J₂ : Type} (N : ℕ)
    (f₁ : ι₁ → K₁[X]) (χ₁ : ι₁ → J₁ → K₁ˣ) (f₂ : ι₂ → K₂[X]) (χ₂ : ι₂ → J₂ → K₂ˣ) : Prop :=
  GoodAt K₁ L₁ N f₁ χ₁ ∧ GoodAt K₂ L₂ N f₂ χ₂
def GoodDualStable : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (ι J : Type)
    (N : ℕ) (f : ι → K[X]) (χ : ι → J → Kˣ), GoodAt K L N f χ →
    GoodAt K L N (fun v => C ((f v).coeff 0)⁻¹ * (f v).reverse) χ
open Classical in

def DivisorDegreeSubSum : Prop :=
  ∀ (K : Type) [Field K] (f : K[X]) (a : ℕ), f ≠ 0 →
    ((∃ h : K[X], h ∣ f ∧ h.natDegree = a) ↔
      IsSubSum ((UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree) a)
open Classical in

def LemmaP : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A)).card
      ≤ 7 * N.factorial
def monicOf {K : Type*} [Field K] {N : ℕ} (c : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ)
open Classical in

def SquarefreeCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 1 ≤ N →
    Fintype.card K ^ N ≤
      ((Finset.univ : Finset (Fin N → K)).filter
        (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card
      + 2 * Fintype.card K ^ (N - 1)
open Classical in

def IrredCountUpper : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    d * ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c))).card
      ≤ Fintype.card K ^ d
open Classical in

def IrredCountLower : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    Fintype.card K ^ d ≤
      d * ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c))).card
        + 2 * Fintype.card K ^ (d / 2)
open Classical in

def TypeCountExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((UniqueFactorizationMonoid.normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
    ∏ d ∈ Finset.Icc 1 N,
      (((Finset.univ : Finset (Fin d → K)).filter
        (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d)
open Classical in

def CycleTypeProb : Prop :=
  ∀ (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d)).card *
      ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial
def TypeCountUpper : Prop :=
  ∀ (g : ℕ) (D : Finset ℕ) (Nd n : ℕ → ℕ), (∀ d ∈ D, 1 ≤ d) → (∀ d ∈ D, d * Nd d ≤ g ^ d) →
    (∏ d ∈ D, ((Nd d).choose (n d) : ℝ)) ≤
      (g : ℝ) ^ (∑ d ∈ D, d * n d) / ∏ d ∈ D, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))
def TypeCountLower : Prop :=
  ∀ (g : ℕ) (D : Finset ℕ) (Nd n : ℕ → ℕ), 2 ≤ g → (∀ d ∈ D, 1 ≤ d) →
    (1 ∈ D → g - 1 ≤ Nd 1) →
    (∀ d ∈ D, 2 ≤ d → (g : ℝ) ^ d - 2 * (g : ℝ) ^ ((d : ℝ) / 2) ≤ (d : ℝ) * (Nd d : ℝ)) →
    (1 - 3 * ((∑ d ∈ D, d * n d : ℕ) : ℝ) ^ 2 / (g : ℝ)) * (g : ℝ) ^ (∑ d ∈ D, d * n d) /
        (∏ d ∈ D, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))) ≤
      ∏ d ∈ D, ((Nd d).choose (n d) : ℝ)
def SubsetSumCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (i : ℕ), (∀ c, 1 ≤ deg c) →
    ((Finset.univ : Finset ι).powerset.filter (fun I => ∑ c ∈ I, deg c = i)).card
      ≤ (∑ c, deg c) ^ i
def NTauBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (g k : ℕ) (c : ℕ → ℝ) (n : ℝ),
    (∀ x, 1 ≤ deg x) → 1 ≤ g → 1 ≤ k →
    (∀ i, c i = (((Finset.univ : Finset ι).powerset.filter
      (fun I => ∑ x ∈ I, deg x = i)).card : ℝ)) →
    n = (∑ i ∈ Finset.range k, c i * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + c k →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n ∧
      n ≤ ∑ i ∈ Finset.range (k + 1), ((∑ x, deg x : ℕ) : ℝ) ^ i * (g : ℝ) ^ (k - i)
def LemmaLWeight : Prop :=
  ∀ (d : Multiset ℕ) (g k : ℕ) (n : ℝ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g → 1 ≤ k → k ≤ d.sum →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n →
    n ≤ ∑ i ∈ Finset.range (k + 1), (d.sum : ℝ) ^ i * (g : ℝ) ^ (k - i) →
    (1 - 1 / (g : ℝ)) / (g : ℝ) ^ d.sum ≤
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ∧
      (2 * d.sum ≤ g →
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ≤
          (1 + 6 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum)
def OtherConstituents : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (wt : T → ℝ) (S : Finset T) (g N : ℕ),
    2 ≤ g → 1 ≤ N → (∀ t, 0 ≤ wt t) → ∑ t, wt t = 1 →
    (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ S.card →
    (∀ t ∈ S, (1 - 1 / (g : ℝ)) / (g : ℝ) ^ N ≤ wt t) →
    ∑ t ∈ Sᶜ, wt t ≤ 3 / (g : ℝ)
open Classical in

def CycleProbPrime : Prop :=
  ∀ N p : ℕ, p.Prime → p ≤ N → N < 2 * p →
    p * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => p ∈ σ.cycleType)).card
      = N.factorial
open Classical in

def CycleProbSum : Prop :=
  ∀ N : ℕ,
    (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) =
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
      (N.factorial : ℝ) / p
def PrimeRecipSum : Prop :=
  ∀ N : ℕ, 100 ≤ N →
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p
def PrimeInRange : Prop :=
  ∀ N : ℕ, 8 ≤ N → ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N
def FewPrimeDivisors : Prop :=
  ∀ g N : ℕ, 2 ≤ g → 3 ≤ N →
    ((∏ d ∈ Finset.Icc 1 N, (g ^ d - 1)).primeFactors.card : ℝ) ≤ (N : ℝ) ^ 2 * Real.log g
open Classical in

def SubfieldCount : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] (g d l : ℕ), l.Prime → 2 ≤ g → 2 ≤ d →
    Fintype.card L = g ^ d → l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g ^ d →
    (((Finset.univ : Finset Lˣ).filter
      (fun x => ∃ e, e ∣ d ∧ e < d ∧ primeToPart l x ^ (g ^ e - 1) = 1)).card : ℝ)
      ≤ d * (g : ℝ) ^ ((d : ℝ) / 2) * (g : ℝ) ^ ((d : ℝ) / 4)
open Classical in

def SamePartCount : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] (g d l : ℕ) (y : Lˣ), l.Prime → 2 ≤ g → 1 ≤ d →
    Fintype.card L = g ^ d →
    ((Finset.univ : Finset Lˣ).filter (fun x => primeToPart l x = primeToPart l y)).card
        = l ^ padicValNat l (g ^ d - 1) ∧
      (l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g ^ d →
        (((Finset.univ : Finset Lˣ).filter
          (fun x => primeToPart l x = primeToPart l y)).card : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4))
def FiniteOrderUnipotentModP : Prop :=
  ∀ (p n m : ℕ) [Fact p.Prime] (γ : Matrix (Fin n) (Fin n) ℤ_[p]), 0 < m → γ ^ m = 1 →
    (γ.map (PadicInt.toZMod (p := p)) - 1) ^ n = 0 → ∃ a : ℕ, γ ^ (p ^ a) = 1
def PPowerOrderTrivial : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n p a : ℕ) (γ : Matrix (Fin n) (Fin n) K),
    p.Prime → n < p - 1 → Irreducible (Polynomial.cyclotomic p K) → γ ^ (p ^ a) = 1 → γ = 1
def PrimeToLPartLowerBound : Prop :=
  ∀ (l g d : ℕ), l.Prime → 2 ≤ g → 1 ≤ d →
    (¬ l ∣ g - 1 → g - 1 ≤ (g ^ d - 1) / l ^ padicValNat l (g ^ d - 1)) ∧
    (l ∣ g - 1 → l ^ padicValNat l (g ^ d - 1) ≤ 2 * d * (g - 1))
def PrimeToLPartReciprocalBound : Prop :=
  ∀ (l g d : ℕ), l.Prime → 2 ≤ g → 2 ≤ d →
    (1 : ℝ) / (((g ^ d - 1) / l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) ≤ 2 * d / g
open Classical in

def ShareNV5 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (w : ∀ v, T v → ℝ) (μ : (∀ v, T v) → ℝ) (K c : ℝ) (N J : ℕ) (P : Finset (Finset ι))
    (bad : ℕ → ∀ v, T v → Prop),
    P.card ≤ 2 → (∀ S ∈ P, S.card = J) → 0 ≤ K → 0 ≤ c →
    (∀ v t, 0 ≤ w v t) → (∀ v, ∑ t, w v t ≤ 1) → (∀ x, μ x ≤ K * ∏ v, w v (x v)) →
    (∀ a ∈ Icc 1 (N / 2), ∀ S ∈ P, ∀ v ∈ S, ∑ t ∈ univ.filter (bad a v), w v t ≤ c) →
    ∑ x ∈ univ.filter (fun x => ∃ S ∈ P, ∃ a ∈ Icc 1 (N / 2), ∀ v ∈ S, bad a v (x v)), μ x
      ≤ N * K * c ^ J
def GoodOneSummand : Prop :=
  ∀ (ι : Type) (N : ℕ) (deg : Multiset ℕ) (dv : ι → Multiset ℕ),
    (∀ a ∈ deg, 1 ≤ a) → deg.sum = N → (∀ a ∈ deg, ∀ v, IsSubSum (dv v) a) →
    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ IsSubSum (dv v) a) →
    deg.card ≤ 1
def RootOfUnityReduction : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (l n : ℕ) (z z' : R), l.Prime →
    (l : R) ∈ IsLocalRing.maximalIdeal R → 0 < n → z ^ n = 1 → z' ^ n = 1 →
    (z - z' ∈ IsLocalRing.maximalIdeal R ↔ ∃ a : ℕ, z ^ (l ^ a) = z' ^ (l ^ a))
def GoodEigenvaluesDistinct : Prop :=
  ∀ (K L R : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [CommRing R] [IsLocalRing R]
    (ι J : Type) (N : ℕ) (f : ι → K[X]) (χ : ι → J → Kˣ) (T : Lˣ →* Rˣ) (l : ℕ),
    Function.Injective T → GoodAt K L N f χ → l.Prime →
    (l : R) ∈ IsLocalRing.maximalIdeal R → l ∉ BB (Fintype.card K) N →
    ∀ (v : ι) (x y : Lˣ), (x : L) ∈ (f v).rootSet L → (y : L) ∈ (f v).rootSet L →
      ((T x : R) - (T y : R)) ∈ IsLocalRing.maximalIdeal R → x = y
def GoodNotCongruentChi : Prop :=
  ∀ (K L R : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [CommRing R] [IsLocalRing R]
    (ι J : Type) (N : ℕ) (f : ι → K[X]) (χ : ι → J → Kˣ) (T : Lˣ →* Rˣ) (l : ℕ),
    Function.Injective T → GoodAt K L N f χ → l.Prime →
    (l : R) ∈ IsLocalRing.maximalIdeal R → l ≠ Fintype.card K →
    ∀ (v : ι) (j : J) (x : Lˣ), (x : L) ∈ (f v).rootSet L →
      ((T x : R) - (T (Units.map (algebraMap K L).toMonoidHom (χ v j)) : R))
          ∉ IsLocalRing.maximalIdeal R ∧
      ((T x : R) - (T (Units.map (algebraMap K L).toMonoidHom (χ v j)⁻¹) : R))
          ∉ IsLocalRing.maximalIdeal R
def ReducedOrbitSize : Prop :=
  ∀ (α β : Type) [DecidableEq β] (F : α → α) (G : β → β) (φ : α → β) (O : Finset α),
    (∀ x, φ (F x) = G (φ x)) → IsOrbit F O → Set.InjOn φ (O : Set α) →
    IsOrbit G (O.image φ) ∧ (O.image φ).card = O.card
open Classical in

def FrobOrbitIrred : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (f : K[X]),
    f.Monic → Irreducible f →
    IsOrbit (fun x : L => x ^ Fintype.card K) (f.aroots L).toFinset ∧
      (f.aroots L).toFinset.card = f.natDegree
def IrreducibleOfFrobeniusTwists : Prop :=
  ∀ (K V P ι : Type) [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : P → Module.End K V) (F : P → V ≃ₗ[K] V) (q : P → ℕ)
    (O : P → ι → Finset K) (I : P → Finset ι),
    (∀ v x, F v (τ v x) = (τ v ^ q v) (F v x)) →
    (∀ v, ∀ i ∈ I v, IsOrbit (fun x : K => x ^ q v) (O v i)) →
    (∀ v, (LinearMap.charpoly (τ v)).roots = ∑ i ∈ I v, (O v i).val) →
    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ Module.finrank K V →
      ∃ v, ¬ IsSubSum ((I v).val.map fun i => (O v i).card) a) →
    ∀ W : Submodule K V, (∀ v, ∀ x ∈ W, τ v x ∈ W) → (∀ v, ∀ x ∈ W, F v x ∈ W) →
      W = ⊥ ∨ W = ⊤
def CliffordBlocks : Prop :=
  ∀ (K V G ι : Type) [Field K] [AddCommGroup V] [Module K V] [Group G] [Fintype ι]
    (ρ : Representation K G V) (H : Subgroup G) [H.Normal] (t : G) (b : Module.Basis ι K V)
    (c : ι → K), Nontrivial V → t ∈ H → Function.Injective c → (∀ i, ρ t (b i) = c i • b i) →
    (∀ W : Submodule K V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∃ B : Finset (Submodule K V),
      (∀ W ∈ B, W ≠ ⊥ ∧ (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) ∧
        ∀ W' ≤ W, (∀ h ∈ H, ∀ x ∈ W', ρ h x ∈ W') → W' = ⊥ ∨ W' = W) ∧
      sSupIndep (B : Set (Submodule K V)) ∧ sSup (B : Set (Submodule K V)) = ⊤ ∧
      (∀ g, ∀ W ∈ B, W.map (ρ g) ∈ B) ∧
      (∀ W ∈ B, ∀ W' ∈ B, ∃ g, W.map (ρ g) = W') ∧
      (∀ W ∈ B, W = Submodule.span K {x | x ∈ W ∧ ∃ i, x = b i})
def PowerIsPrimeCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p : ℕ), p.Prime →
    p ∈ σ.cycleType → Fintype.card α < 2 * p →
    ∃ k : ℕ, (σ ^ k).IsCycle ∧ (σ ^ k).support.card = p
def BlocksOfPrimeCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p m : ℕ)
    (B : Finset (Finset α)),
    p.Prime → σ.IsCycle → σ.support.card = p → Fintype.card α < 2 * p →
    (∀ b ∈ B, b.card = m) → (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b') →
    (∀ x, ∃ b ∈ B, x ∈ b) → (∀ b ∈ B, b.map σ.toEmbedding ∈ B) →
    B.card = 1 ∨ m = 1
def PrimitiveOfPrimeCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (p : ℕ),
    p.Prime → σ ∈ G → σ.IsCycle → σ.support.card = p → Fintype.card α < 2 * p →
    MulAction.IsPretransitive G α → MulAction.IsPreprimitive G α
def TransitiveWithPrimeCycle : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (σ : Equiv.Perm α) (p : ℕ),
    p.Prime → σ ∈ G → p ∈ σ.cycleType → Fintype.card α < 2 * p → p + 3 ≤ Fintype.card α →
    MulAction.IsPretransitive G α → ¬ Group.IsSolvable G
def BurnsideDensity : Prop :=
  ∀ (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Subalgebra K (Module.End K V)),
    (∀ W : Submodule K V, (∀ a ∈ A, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = ⊤) → A = ⊤
def IdempotentLattice : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (MM : Submodule R V)
    (e : V →ₗ[R] V) (n : R), e ∘ₗ e = e → (∀ m ∈ MM, n • e m ∈ MM) →
    (∀ m ∈ MM, n • e m ∈ MM ⊓ LinearMap.range e) ∧
    MM ⊓ LinearMap.range e ≤ MM.map e ∧
    (∀ m ∈ MM, n • m ∈ MM ⊓ LinearMap.range e ⊔ MM ⊓ LinearMap.ker e)
def SupportCancel : Prop :=
  ∀ (α : Type) (s s' t : Multiset α), s' + t = s + t → s' = s
def CharValueIntegral : Prop :=
  ∀ (G V : Type) [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G), IsIntegral ℤ (ρ.character g)
def ProjectorIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G]
    (e : MonoidAlgebra K G), e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * e.coeff g)
def centralIdem {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : MonoidAlgebra ℂ G :=
  ∑ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) •
    MonoidAlgebra.of ℂ G g
def CentralIdempotent : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V),
    (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    centralIdem ρ * centralIdem ρ = centralIdem ρ ∧
      ∀ x : MonoidAlgebra ℂ G, centralIdem ρ * x = x * centralIdem ρ
def CentralIdemOrthogonal : Prop :=
  ∀ (G V W : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial V] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    (∀ U : Submodule ℂ V, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (¬ ∃ φ : V ≃ₗ[ℂ] W, ∀ g x, φ (ρ g x) = σ g (φ x)) →
    centralIdem ρ * centralIdem σ = 0
def CentralIdemSelfAdjoint : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    ρ.character g⁻¹ = (starRingEnd ℂ) (ρ.character g) ∧
      (centralIdem ρ).coeff g⁻¹ = (starRingEnd ℂ) ((centralIdem ρ).coeff g)
def DropContain : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (Mt MtZ VZ : Submodule R V)
    (e f : V →ₗ[R] V) (n : R), e ∘ₗ e = e → f ∘ₗ e = e ∘ₗ f →
    (∀ x ∈ MtZ, n • e x ∈ MtZ) → (∀ x ∈ MtZ, f x ∈ Mt ⊓ VZ) →
    ∀ x ∈ MtZ, n • f (e x) ∈ Mt ⊓ VZ ⊓ LinearMap.range e
def VanishOffZ : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (Mt : Submodule R V)
    (p f : V →ₗ[R] V), p ∘ₗ p = p → f ∘ₗ p = p ∘ₗ f → f ∘ₗ (LinearMap.id - p) = 0 →
    (∀ x ∈ Mt, f x ∈ Mt) →
    (∀ y ∈ Mt.map p, f y ∈ Mt ⊓ LinearMap.range p) ∧ (Mt.map p).map f = Mt.map f
def LengthDet : Prop :=
  ∀ (O K W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] [FiniteDimensional K W] (M M' : Submodule O W) (φ : W →ₗ[K] W)
    (δ : O),
    M' ≤ M → Module.Finite O M → Submodule.span K (M : Set W) = ⊤ →
    (∀ x ∈ M, φ x ∈ M') → LinearMap.det φ = algebraMap O K δ → δ ≠ 0 →
    Module.length O (M ⧸ M'.comap M.subtype) ≤ IsDiscreteValuationRing.addVal O δ
def DropLength : Prop :=
  ∀ (O K W ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
    (Wp : ι → Submodule K W) (n : O) (fv : ι → O) (M M' : Submodule O W) (φ : W →ₗ[K] W),
    DirectSum.IsInternal Wp → (∀ i, ∀ x ∈ Wp i, φ x = algebraMap O K (n * fv i) • x) →
    n ≠ 0 → (∀ i, fv i ≠ 0) → M' ≤ M → Module.Finite O M →
    Submodule.span K (M : Set W) = ⊤ → (∀ x ∈ M, φ x ∈ M') →
    Module.length O (M ⧸ M'.comap M.subtype) ≤
      ∑ i, (Module.finrank K (Wp i) : ℕ∞) *
        (IsDiscreteValuationRing.addVal O (fv i) + IsDiscreteValuationRing.addVal O n)
def ChooseGenerator : Prop :=
  ∀ (O cc ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup cc]
    [Module O cc] [Fintype ι] (ev : ι → cc →ₗ[O] O),
    (Fintype.card ι : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O) →
    ∃ f : cc, ∀ i, ∀ h : cc,
      IsDiscreteValuationRing.addVal O (ev i f) ≤ IsDiscreteValuationRing.addVal O (ev i h)
def DiscardRows : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (Q Pi : Matrix n n ℂ) (η δ s Dstar : ℝ),
    η ≤ 1 → 0 < Dstar → Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi →
    (Q * Q).trace.re ≤ (1 + η) * Q.trace.re ^ 2 / Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → (Fintype.card n : ℝ) ≤ (1 + s) * Dstar →
    (1 - Real.sqrt (2 * δ)) * Q.trace.re ≤ ((1 - Pi) * Q * (1 - Pi)).trace.re ∧
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re ≤ (Q * Q).trace.re ∧
    (2 * δ < 1 →
      (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re ≤
        (1 + η) * (1 + s) * ((1 - Real.sqrt (2 * δ)) ^ 2)⁻¹ *
          ((1 - Pi) * Q * (1 - Pi)).trace.re ^ 2 / ((1 - Pi).rank : ℝ))
def DiscardK : Prop :=
  ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq n] (Pi : Matrix n n ℂ)
    (B : Matrix n m ℂ) (c : ℝ), 0 ≤ c → Pi.IsHermitian → Pi * Pi = Pi →
    ((c : ℂ) • (B.conjTranspose * B) - (c : ℂ) • (B.conjTranspose * (1 - Pi) * B)).PosSemidef
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


