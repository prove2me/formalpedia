-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
-- name    : Formalism_PieriBlockIdeals_CapelliCentralEnveloping
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:00.255417+00:00
-- url     : https://prove2.me/theorems/f232c9f5-7f04-423c-8344-a6eca92e18d1
-- title:
--   Capelli Central Enveloping
-- statement:
--   Definitions and structural lemmas for Capelli Central Enveloping, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/CapelliCentralEnveloping.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
namespace Formalism.CohomologicalDescent.HeightDescentMinors
section Series
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
def br (c : ℤ_[l]) : O⟦X⟧ := binomialSeries O c - 1
def act (c : ℤ_[l]) (f : O⟦X⟧) : O⟦X⟧ := f.subst (br l O c)
def phi (f : O⟦X⟧) : O⟦X⟧ := f.subst ((1 + X) ^ l - 1 : O⟦X⟧)
def mu : Finset ℤ_[l] := Polynomial.nthRootsFinset (l - 1) (1 : ℤ_[l])
def pi0 : O⟦X⟧ := ∏ d ∈ mu l, br l O d
def q0 : O⟦X⟧ := pi0 l O - C (l : O)
def q : O⟦X⟧ := PowerSeries.mk fun j => ((l.choose (j + 1) : ℕ) : O)
def inc (g : O⟦X⟧) : O⟦X⟧ := g.subst (pi0 l O)
end Series
def MuFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (mu l).card = l - 1 ∧
    (∀ x : ZMod l, x ≠ 0 → ∃! d, d ∈ mu l ∧ PadicInt.toZMod d = x) ∧
    (l ≠ 2 → ∏ d ∈ mu l, d = -1)
def QMul : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    X * q l O = (1 + X) ^ l - 1 ∧ phi l O X = X * q l O
def QRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (ζ : O),
    IsPrimitiveRoot ζ l → q l O = ∏ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1))
def ActLaws : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (∀ c d : ℤ_[l], act l O c (br l O d) = br l O (d * c)) ∧
    (∀ (c d : ℤ_[l]) (f : O⟦X⟧), act l O c (act l O d f) = act l O (d * c) f) ∧
    (∀ f : O⟦X⟧, act l O 1 f = f) ∧
    (∀ f : O⟦X⟧, phi l O f = act l O (l : ℤ_[l]) f) ∧
    (∀ (c : ℤ_[l]) (f : O⟦X⟧), phi l O (act l O c f) = act l O c (phi l O f)) ∧
    (∀ (c : ℤ_[l]) (f g : O⟦X⟧), act l O c (f * g) = act l O c f * act l O c g ∧
      act l O c (f + g) = act l O c f + act l O c g) ∧
    (∀ (c : ℤ_[l]) (a : O), act l O c (C a) = C a)
def R1 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∃ w : (O⟦X⟧)ˣ, pi0 l O = (w : O⟦X⟧) * X ^ (l - 1) ∧ constantCoeff (w : O⟦X⟧) = -1
def BasisGeneral : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (w : (R⟦X⟧)ˣ), 0 < n → ∀ f : R⟦X⟧,
    ∃! g : Fin n → R⟦X⟧, f = ∑ j, (g j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ)
def DivisibilityInvariant : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    ∀ d ∈ mu l, act l O d (pi0 l O) = pi0 l O
def PowerSeriesFreeBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ f : O⟦X⟧,
    ∃! g : Fin (l - 1) → O⟦X⟧, f = ∑ j, inc l O (g j) * X ^ (j : ℕ)
def RootsOfUnityInvariants : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ f : O⟦X⟧,
    (∀ d ∈ mu l, act l O d f = f) ↔ ∃ g : O⟦X⟧, f = inc l O g
def UnitFactorQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∃ g : (O⟦X⟧)ˣ, q0 l O = (g : O⟦X⟧) * q l O ∧ constantCoeff (g : O⟦X⟧) = -1
def RootOfUnityRemainder : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (ζ : O), l ≠ 2 →
    IsPrimitiveRoot ζ l → ∀ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1)) ∣ pi0 l O - C (l : O)
def ConvergentSeriesEval : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O] [IsLinearTopology O O]
    [T2Space O] [CompleteSpace O] (ζ : O), l ≠ 2 →
    IsPrimitiveRoot ζ l → IsTopologicallyNilpotent (ζ - 1) → ∀ b ∈ Finset.Ioo 0 l,
      PowerSeries.eval₂ (RingHom.id O) (ζ ^ b - 1) (pi0 l O) = (l : O)
def R4 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∀ (S : ℕ) (m y : O⟦X⟧), inc l O m = q l O ^ S * y → ∃ m' : O⟦X⟧, m = (X - C (l : O)) ^ S * m'
def FrobeniusCongruence : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (f : ℤ_[l]⟦X⟧),
    ∃ r : ℤ_[l]⟦X⟧, phi l ℤ_[l] f = f ^ l + C (l : ℤ_[l]) * r
def FrobeniusPiZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    ∃ r : O⟦X⟧, phi l O (pi0 l O) = pi0 l O ^ l + C (l : O) * r
def FrobeniusCharP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [CharP O l] (g : O⟦X⟧),
    phi l O (inc l O g) = inc l O (g.subst (X ^ l : O⟦X⟧))
def R6 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∀ u c : ℤ_[l], u = 1 + (l : ℤ_[l]) * c → ∃ un : O⟦X⟧,
      act l O u (pi0 l O) = pi0 l O * (1 + inc l O un * q0 l O) ∧
      (∃ e : O, constantCoeff un = algebraMap ℤ_[l] O c + (l : O) * e) ∧
      act l O u (q0 l O) = inc l O (1 + X * un) * q0 l O ∧ IsUnit (1 + X * un)
def ZpowCongGen : Prop :=
  ∀ (R : Type) [CommRing R] (x v : R) (U : Rˣ) (κ : ℤ), (U : R) = 1 + x * v →
    x ^ 2 ∣ ((U ^ κ : Rˣ) : R) - (1 + (κ : R) * (x * v))
def ZpowCong : Prop :=
  ∀ (R : Type) [CommRing R] (v : R⟦X⟧) (U : (R⟦X⟧)ˣ) (κ : ℤ), (U : R⟦X⟧) = 1 + v * X →
    (X : R⟦X⟧) ^ 2 ∣ ((U ^ κ : (R⟦X⟧)ˣ) : R⟦X⟧) - (1 + C ((κ : R) * constantCoeff v) * X)
def TwistCong : Prop :=
  ∀ (k : Type) [Field k] (un g : k⟦X⟧) (κ : ℤ), ∃ r : k⟦X⟧,
    (((X * (1 + un * X) : k⟦X⟧) : LaurentSeries k)) ^ κ * ((1 + X * g : k⟦X⟧) : LaurentSeries k) =
      ((X : k⟦X⟧) : LaurentSeries k) ^ κ *
        ((1 + C ((κ : k) * constantCoeff un + constantCoeff g) * X + X ^ 2 * r : k⟦X⟧) :
          LaurentSeries k)
def DbarCong : Prop :=
  ∀ (R : Type) [CommRing R] (v y : R⟦X⟧), (X : R⟦X⟧) ^ 2 ∣ y.subst (X * (1 + v * X)) - y
def ThetaCongPadic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ) (c : ℤ_[l]) (m : ℤ), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c →
    ∃ e : ℤ_[l], ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * (-((m : ℤ_[l]) * c) + (l : ℤ_[l]) * e)
section Capelli
variable {𝒰 : Type} [Ring 𝒰] {N : ℕ}
def GlRel (E : Fin N → Fin N → 𝒰) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)
def capA (E : Fin N → Fin N → 𝒰) (v : 𝒰) (i j : Fin N) : 𝒰 := E i j + if i = j then v else 0
def capelli (E : Fin N → Fin N → 𝒰) (u : 𝒰) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin N => capA E (u - ((j : ℕ) : 𝒰)) (σ j) j).prod
def capelliRow (E : Fin N → Fin N → 𝒰) (u : 𝒰) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun i : Fin N => capA E (u - (((σ i : Fin N) : ℕ) : 𝒰)) i (σ i)).prod
end Capelli
def C1 : Prop :=
  ∀ (𝒰 : Type) [Ring 𝒰] (N : ℕ) (E : Fin N → Fin N → 𝒰) (u : 𝒰), GlRel E →
    (∀ i j, Commute u (E i j)) → ∀ k m, Commute (E k m) (capelli E u)
def CapelliCentralPoly : Prop :=
  ∀ (𝒰 : Type) [Ring 𝒰] (N : ℕ) (E : Fin N → Fin N → 𝒰), GlRel E → ∀ k m n,
    Commute (E k m)
      ((capelli (fun i j => Polynomial.C (E i j)) (Polynomial.X : Polynomial 𝒰)).coeff n)
attribute [local instance 100] LieRing.ofAssociativeRing in

def CapelliCentralEnveloping : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ)
    (x : UniversalEnvelopingAlgebra R (Matrix (Fin N) (Fin N) R)) (n : ℕ),
    Commute x
      ((capelli (fun i j => Polynomial.C
          (UniversalEnvelopingAlgebra.ι R (Matrix.single i j (1 : R))))
        (Polynomial.X :
          Polynomial (UniversalEnvelopingAlgebra R (Matrix (Fin N) (Fin N) R)))).coeff n)
def C2 : Prop :=
  ∀ (k : Type) [CommRing k] (𝒰 : Type) [Ring 𝒰] [Algebra k 𝒰] (V : Type) [AddCommGroup V]
    [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V] (N : ℕ) (E : Fin N → Fin N → 𝒰) (u : k)
    (lam : Fin N → k) (v : V), (∀ i j, i < j → E i j • v = 0) → (∀ i, E i i • v = lam i • v) →
    capelli E (algebraMap k 𝒰 u) • v = (∏ i : Fin N, (u + lam i - ((i : ℕ) : k))) • v
def RowDetNotCentral : Prop :=
  ¬ ∀ (𝒰 : Type) [Ring 𝒰] (N : ℕ) (E : Fin N → Fin N → 𝒰) (u : 𝒰), GlRel E →
    (∀ i j, Commute u (E i j)) → ∀ k m, Commute (E k m) (capelliRow E u)
def MinorsDvd {R : Type} [CommRing R] {m p : ℕ} (x : R) (t : ℕ) (P : Matrix (Fin m) (Fin p) R) :
    Prop :=
  ∀ (f : Fin t → Fin m) (g : Fin t → Fin p), StrictMono f → StrictMono g →
    x ∣ (P.submatrix f g).det
def MinorsDvdAll : Prop :=
  ∀ (R : Type) [CommRing R] (m p t : ℕ) (x : R) (P : Matrix (Fin m) (Fin p) R),
    MinorsDvd x t P ↔ ∀ (f : Fin t → Fin m) (g : Fin t → Fin p), x ∣ (P.submatrix f g).det
def MinorExpand : Prop :=
  ∀ (R : Type) [CommRing R] (m n p t : ℕ) (G : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin p) R) (f : Fin t → Fin m) (g : Fin t → Fin p),
    ((G * P).submatrix f g).det =
      ∑ r : Fin t → Fin n, (∏ i, G (f i) (r i)) * (P.submatrix r g).det
def MinorsDvdMul : Prop :=
  ∀ (R : Type) [CommRing R] (m n p r t : ℕ) (x : R) (G : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin p) R) (H : Matrix (Fin p) (Fin r) R),
    MinorsDvd x t P → MinorsDvd x t (G * P * H)
def MinorsBasisIndep : Prop :=
  ∀ (R : Type) [CommRing R] (n t : ℕ) (x : R) (G P H : Matrix (Fin n) (Fin n) R),
    IsUnit G → IsUnit H → (MinorsDvd x t (G * P * H) ↔ MinorsDvd x t P)
def DiagMinors : Prop :=
  ∀ (R : Type) [CommRing R] (n t S : ℕ) (x : R) (a : Fin n → ℕ) (G H : Matrix (Fin n) (Fin n) R),
    (∀ J : Finset (Fin n), J.card = t → S ≤ ∑ j ∈ J, a j) →
    MinorsDvd (x ^ S) t (G * Matrix.diagonal (fun j => x ^ a j) * H)
def MinorExists : Prop :=
  ∀ (R : Type) [CommRing R] (n t h : ℕ) (x : R) (M M' : Matrix (Fin n) (Fin n) R), t ≤ n →
    M * M' = (x ^ h) • (1 : Matrix (Fin n) (Fin n) R) → ¬ x ^ (t * h + 1) ∣ x ^ (t * h) →
    ∃ (f g : Fin t → Fin n), StrictMono f ∧ StrictMono g ∧
      ¬ x ^ (t * h + 1) ∣ (M.submatrix f g).det
def BlockMinor : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (π : R) (n₁ n₂ t₁ t₂ v₁ v₂ : ℕ)
    (A : Matrix (Fin n₁) (Fin n₁) R) (B : Matrix (Fin n₁) (Fin n₂) R)
    (D : Matrix (Fin n₂) (Fin n₂) R) (f₁ g₁ : Fin t₁ → Fin n₁) (f₂ g₂ : Fin t₂ → Fin n₂), Prime π →
    ¬ π ^ (v₁ + 1) ∣ (A.submatrix f₁ g₁).det → ¬ π ^ (v₂ + 1) ∣ (D.submatrix f₂ g₂).det →
    ((Matrix.fromBlocks A B 0 D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂)).det =
        (A.submatrix f₁ g₁).det * (D.submatrix f₂ g₂).det ∧
      ¬ π ^ (v₁ + v₂ + 1) ∣
        ((Matrix.fromBlocks A B 0 D).submatrix (Sum.map f₁ f₂) (Sum.map g₁ g₂)).det
def MinorBoundExtra : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (π : R) (n h c : ℕ) (Φ : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (ch : Finset ℕ) (al ν : ℕ → ℕ), Prime π → Φ.BlockTriangular b →
    ch ⊆ Finset.univ.image b →
    (∀ r ∈ ch, ∃ s, (∀ j, b j = r ↔ j = s) ∧ ∃ u : Rˣ, Φ s s = (u : R) * π ^ al r) →
    (∀ r ∈ Finset.univ.image b \ ch,
      (∃ M' : Matrix {j // b j = r} {j // b j = r} R,
        Φ.toSquareBlock b r * M' = (π ^ h) • (1 : Matrix {j // b j = r} {j // b j = r} R)) ∧
      ν r ≤ (Finset.univ.filter fun j => b j = r).card) →
    MinorsDvd (π ^ c) (ch.card + ∑ r ∈ Finset.univ.image b \ ch, ν r) Φ →
    c ≤ ∑ r ∈ ch, al r + (∑ r ∈ Finset.univ.image b \ ch, ν r) * h
def CharpolyDiag : Prop :=
  ∀ (O L : Type) [CommRing O] [Field L] (ι : O →+* L) (n : ℕ) (Θ Γ : Matrix (Fin n) (Fin n) O)
    (lam : O) (r : Fin n → O) (G : (Matrix (Fin n) (Fin n) L)ˣ), Function.Injective ι → lam ≠ 0 →
    Γ = 1 + lam • Θ →
    Γ.map ι * (G : Matrix (Fin n) (Fin n) L) =
      (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (1 + lam * r j)) →
    Θ.charpoly = ∏ j, (Polynomial.X - Polynomial.C (r j))
def CharpolyRed : Prop :=
  ∀ (O k : Type) [CommRing O] [CommRing k] (red : O →+* k) (n : ℕ) (Θ : Matrix (Fin n) (Fin n) O)
    (r : Fin n → O) (a : k) (c : Fin n → ℤ),
    Θ.charpoly = ∏ j, (Polynomial.X - Polynomial.C (r j)) → (∀ j, red (r j) = -a * (c j : k)) →
    (Θ.map red).charpoly = ∏ j, (Polynomial.X - Polynomial.C (-a * (c j : k)))
def MinorRed : Prop :=
  ∀ (O k : Type) [CommRing O] [CommRing k] (red : O →+* k) (lam : O) (n t S : ℕ)
    (P : Matrix (Fin n) (Fin n) O⟦X⟧) (f g : Fin t → Fin n), red lam = 0 →
    ((P.map (PowerSeries.map red)).submatrix f g).det = PowerSeries.map red (P.submatrix f g).det ∧
    ((X - C lam) ^ S ∣ (P.submatrix f g).det →
      (X : k⟦X⟧) ^ S ∣ ((P.map (PowerSeries.map red)).submatrix f g).det)
def LinDivision : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I →
    (∀ f : O⟦X⟧, ∃ (f₁ : O⟦X⟧) (a : O), f = (X - C c) * f₁ + C a) ∧
    (∀ (f₁ f₂ : O⟦X⟧) (a₁ a₂ : O), (X - C c) * f₁ + C a₁ = (X - C c) * f₂ + C a₂ →
      f₁ = f₂ ∧ a₁ = a₂)
def LinPrime : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I →
    Prime (X - C c : O⟦X⟧)
def RootsProduct : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (s : Finset ℕ)
    (c : ℕ → O) (S : ℕ) (m : O⟦X⟧), (∀ b ∈ s, c b ∈ I) → Set.InjOn c s →
    (∀ b ∈ s, (X - C (c b)) ^ S ∣ m) → (∏ b ∈ s, (X - C (c b))) ^ S ∣ m
def RootsDescent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (I : Ideal O)
    [IsAdicComplete I O] (ζ : O), l ≠ 2 → IsPrimitiveRoot ζ l → ζ - 1 ∈ I → ∀ (S : ℕ) (m : O⟦X⟧),
    (∀ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1)) ^ S ∣ inc l O m) →
    ∃ m' : O⟦X⟧, m = (X - C (l : O)) ^ S * m'
def HeightDescent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ (n h : ℕ)
    (P Q : Matrix (Fin n) (Fin n) O⟦X⟧),
    P.map (inc l O) * Q = (q l O ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧) →
    ∃ Q' : Matrix (Fin n) (Fin n) O⟦X⟧,
      P * Q' = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)
def DLeibniz : Prop :=
  ∀ (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (p : A) (γA : A →+* A) (γ d : N → N)
    (δ : A → A), (∀ x : N, p • x = 0 → x = 0) → (∀ y x, γ (y • x) = γA y • γ x) →
    (∀ x, p • d x = γ x - x) → (∀ y, p * δ y = γA y - y) →
    (∀ y x, d (y • x) = γA y • d x + δ y • x) ∧
    (∀ q₀ un x, γA q₀ = (1 + p * un) * q₀ → d (q₀ • x) = q₀ • (d x + un • γ x))
end Formalism.CohomologicalDescent.HeightDescentMinors


