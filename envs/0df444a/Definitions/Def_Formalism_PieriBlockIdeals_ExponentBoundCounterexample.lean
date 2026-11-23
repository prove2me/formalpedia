-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
-- name    : Formalism_PieriBlockIdeals_ExponentBoundCounterexample
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:37.965657+00:00
-- url     : https://prove2.me/theorems/bfa479b8-1860-4dd5-bc19-4082a7720ba7
-- title:
--   Exponent Bound Counterexample
-- statement:
--   Definitions and structural lemmas for Exponent Bound Counterexample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/ExponentBoundCounterexample.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementW
import Definitions.Def_Formalism_RankGapBounds_CloudMinFalse
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
abbrev P2 (R : Type) [CommRing R] := MvPolynomial (Fin 2 × Fin 1) R
def vx (R : Type) [CommRing R] : P2 R := X ((0 : Fin 2), (0 : Fin 1))
def vy (R : Type) [CommRing R] : P2 R := X ((1 : Fin 2), (0 : Fin 1))
def opE (R : Type) [CommRing R] : Module.End R (P2 R) :=
  LinearMap.mulLeft R (vx R) ∘ₗ (pderiv ((1 : Fin 2), (0 : Fin 1))).toLinearMap
def opF (R : Type) [CommRing R] : Module.End R (P2 R) :=
  LinearMap.mulLeft R (vy R) ∘ₗ (pderiv ((0 : Fin 2), (0 : Fin 1))).toLinearMap
def DivPowE : Prop :=
  ∀ (R : Type) [CommRing R] (j : ℕ) (f : P2 R), j.factorial • rowDiv R 0 1 j f = (opE R ^ j) f
def DivPowF : Prop :=
  ∀ (R : Type) [CommRing R] (i : ℕ) (f : P2 R), i.factorial • rowDiv R 1 0 i f = (opF R ^ i) f
def FPowHW : Prop :=
  ∀ (R : Type) [CommRing R] (n i : ℕ),
    (opF R ^ i) (vx R ^ n) = n.descFactorial i • (vx R ^ (n - i) * vy R ^ i)
def FDivHW : Prop :=
  ∀ (R : Type) [CommRing R] (n i : ℕ),
    rowDiv R 1 0 i (vx R ^ n) = n.choose i • (vx R ^ (n - i) * vy R ^ i)
def EDivMono : Prop :=
  ∀ (R : Type) [CommRing R] (a b j : ℕ),
    rowDiv R 0 1 j (vx R ^ a * vy R ^ b) = b.choose j • (vx R ^ (a + j) * vy R ^ (b - j))
def FDivMono : Prop :=
  ∀ (R : Type) [CommRing R] (a b j : ℕ),
    rowDiv R 1 0 j (vx R ^ a * vy R ^ b) = a.choose j • (vx R ^ (a - j) * vy R ^ (b + j))
def BinomId : Prop :=
  ∀ n i j : ℕ, j ≤ i → i ≤ n →
    n.choose i * i.choose j = n.choose (i - j) * (n - i + j).choose j
def BinomIdF : Prop :=
  ∀ n i j : ℕ, i + j ≤ n →
    n.choose i * (n - i).choose j = n.choose (i + j) * (i + j).choose j
def EDivLattice : Prop :=
  ∀ (R : Type) [CommRing R] (n i j : ℕ), i ≤ n →
    (j ≤ i → rowDiv R 0 1 j (n.choose i • (vx R ^ (n - i) * vy R ^ i)) =
      (n - i + j).choose j • (n.choose (i - j) • (vx R ^ (n - (i - j)) * vy R ^ (i - j)))) ∧
    (i < j → rowDiv R 0 1 j (n.choose i • (vx R ^ (n - i) * vy R ^ i)) = 0)
def FDivLattice : Prop :=
  ∀ (R : Type) [CommRing R] (n i j : ℕ), i ≤ n →
    (i + j ≤ n → rowDiv R 1 0 j (n.choose i • (vx R ^ (n - i) * vy R ^ i)) =
      (i + j).choose j • (n.choose (i + j) • (vx R ^ (n - (i + j)) * vy R ^ (i + j)))) ∧
    (n < i + j → rowDiv R 1 0 j (n.choose i • (vx R ^ (n - i) * vy R ^ i)) = 0)
def binLat (R : Type) [CommRing R] (n : ℕ) : Submodule R (P2 R) :=
  Submodule.span R (Set.range fun i : Fin (n + 1) =>
    n.choose i.val • (vx R ^ (n - i.val) * vy R ^ i.val))
def SL2BinomialLattice : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    vx R ^ n ∈ binLat R n ∧
    (∀ (j : ℕ), ∀ f ∈ binLat R n, rowDiv R 0 1 j f ∈ binLat R n ∧ rowDiv R 1 0 j f ∈ binLat R n) ∧
    (∀ L : Submodule R (P2 R), vx R ^ n ∈ L → (∀ (j : ℕ), ∀ f ∈ L, rowDiv R 1 0 j f ∈ L) →
      binLat R n ≤ L) ∧
    hw R (by norm_num : 1 ≤ 2) (fun _ : Fin 1 => n) = vx R ^ n ∧
    weyl R 2 1 (by norm_num) (fun _ : Fin 1 => n) = binLat R n
def SL2DiagBinomInjective : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ),
    Function.Injective (Formalism.CohomologicalDescent.diagBinom R n)
def SL2CokernelIso : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    Nonempty (((Fin (n + 1) → R) ⧸ LinearMap.range (Formalism.CohomologicalDescent.diagBinom R n)) ≃ₗ[R]
      ((i : Fin (n + 1)) → R ⧸ Ideal.span {((n.choose i.val : ℕ) : R)}))
def SL2CokernelKilledExactly : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l n e : ℕ), l.Prime → (l : R) ≠ 0 → ¬ IsUnit (l : R) →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ((∀ y : Fin (n + 1) → R, (l : R) ^ e • y ∈ LinearMap.range (Formalism.CohomologicalDescent.diagBinom R n)) ↔
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l n ≤ e)
def LegendreDigits : Prop :=
  ∀ l m : ℕ, l.Prime → (l - 1) * (m.factorial).factorization l + (l.digits m).sum = m
def KummerDigits : Prop :=
  ∀ l n i : ℕ, l.Prime → i ≤ n →
    (l - 1) * (n.choose i).factorization l + (l.digits n).sum =
      (l.digits i).sum + (l.digits (n - i)).sum
def KummerCarries : Prop :=
  ∀ l n i : ℕ, l.Prime → i ≤ n →
    (n.choose i).factorization l =
      ((Finset.Ico 1 (Nat.log l n + 1)).filter
        fun t => l ^ t ≤ i % l ^ t + (n - i) % l ^ t).card ∧
    ∀ t, Nat.log l n < t → ¬ l ^ t ≤ i % l ^ t + (n - i) % l ^ t
def MaxValLeLog : Prop :=
  ∀ l n : ℕ, l.Prime → Formalism.RankGapBounds.JumpSetsAlt.maxVal l n ≤ Nat.log l n ∧ Nat.log l n ≤ Nat.log l (n + 1)
def MaxValZero : Prop := ∀ l n : ℕ, l.Prime → n < l → Formalism.RankGapBounds.JumpSetsAlt.maxVal l n = 0
def AdditiveKills : Prop :=
  ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] (ℬ : Type u') [Category.{v'} ℬ] [Preadditive ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] (C : 𝒜) (m : ℤ), m • 𝟙 C = 0 → m • 𝟙 (F.obj C) = 0
def FourTerm : Prop :=
  ∀ (R : Type) [CommRing R] (X' A B X'' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup X''] [Module R X'']
    (d : X' →ₗ[R] A) (f : A →ₗ[R] B) (g : B →ₗ[R] X'') (t : R),
    Function.Exact d f → Function.Exact f g → (∀ x : X', t • x = 0) → (∀ x : X'', t • x = 0) →
    (∀ a : A, f a = 0 → t • a = 0) ∧ ∀ b : B, t • b ∈ LinearMap.range f
def OneStep : Prop :=
  ∀ (R : Type) [CommRing R] (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
    (Hp Hj : 𝒜 ⥤ ModuleCat.{0} R) [Hp.Additive] [Hj.Additive] (D N C : 𝒜) (i : D ⟶ N) (p : N ⟶ C)
    (δ : Hp.obj C ⟶ Hj.obj D) (l c : ℕ), ((l ^ c : ℕ) : ℤ) • 𝟙 C = 0 →
    Function.Exact δ.hom (Hj.map i).hom → Function.Exact (Hj.map i).hom (Hj.map p).hom →
    (∀ x : Hj.obj D, (Hj.map i).hom x = 0 → (l : R) ^ c • x = 0) ∧
      ∀ y : Hj.obj N, (l : R) ^ c • y ∈ LinearMap.range (Hj.map i).hom
def IsoAfterInvert : Prop :=
  ∀ (R : Type) [CommRing R] (A B : Type) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (t : R) (c : ℕ), (∀ a : A, f a = 0 → t ^ c • a = 0) →
    (∀ b : B, t ^ c • b ∈ LinearMap.range f) →
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) A)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) B) f)
def chainComp {R : Type} [CommRing R] {H : ℕ → Type} [∀ r, AddCommGroup (H r)]
    [∀ r, Module R (H r)] (f : ∀ r, H (r + 1) →ₗ[R] H r) : ∀ N, H N →ₗ[R] H 0
  | 0 => LinearMap.id
  | N + 1 => chainComp f N ∘ₗ f N
def ChainCok : Prop :=
  ∀ (R : Type) [CommRing R] (H : ℕ → Type) [∀ r, AddCommGroup (H r)] [∀ r, Module R (H r)]
    (f : ∀ r, H (r + 1) →ₗ[R] H r) (t : R) (c : ℕ → ℕ) (N : ℕ),
    (∀ r < N, ∀ y : H r, t ^ c r • y ∈ LinearMap.range (f r)) →
    ∀ z : H 0, t ^ (∑ r ∈ Finset.range N, c r) • z ∈ LinearMap.range (chainComp f N)
def ChainKer : Prop :=
  ∀ (R : Type) [CommRing R] (H : ℕ → Type) [∀ r, AddCommGroup (H r)] [∀ r, Module R (H r)]
    (f : ∀ r, H (r + 1) →ₗ[R] H r) (t : R) (c : ℕ → ℕ) (N : ℕ),
    (∀ r < N, ∀ x : H (r + 1), f r x = 0 → t ^ c r • x = 0) →
    ∀ x : H N, chainComp f N x = 0 → t ^ (∑ r ∈ Finset.range N, c r) • x = 0
def permAct {m : ℕ} (w : Equiv.Perm (Fin m)) (μ : Fin m → ℤ) : Fin m → ℤ := fun i => μ (w⁻¹ i)
def dotAct {m : ℕ} (ρ : Fin m → ℤ) (w : Equiv.Perm (Fin m)) (μ : Fin m → ℤ) : Fin m → ℤ :=
  permAct w (μ + ρ) - ρ
def IsRho {n : ℕ} (ρ : Fin (n + 1) → ℤ) : Prop := ∀ a : Fin n, ρ a.castSucc - ρ a.succ = 1
def rhoStd (m : ℕ) : Fin m → ℤ := fun i => (m : ℤ) - 1 - (i.val : ℤ)
def twoRho (m : ℕ) : Fin m → ℤ :=
  ∑ p ∈ posPairs m, ((Pi.single p.1 1 : Fin m → ℤ) - Pi.single p.2 1)
def DotActMul : Prop :=
  ∀ (m : ℕ) (ρ μ : Fin m → ℤ) (w w' : Equiv.Perm (Fin m)),
    dotAct ρ (w * w') μ = dotAct ρ w (dotAct ρ w' μ) ∧ dotAct ρ 1 μ = μ
def RhoStdSpec : Prop :=
  ∀ n : ℕ, IsRho (rhoStd (n + 1)) ∧
    (∀ i : Fin (n + 1), permAct Fin.revPerm (rhoStd (n + 1)) i = (i.val : ℤ)) ∧
    (1 ≤ n → permAct Fin.revPerm (rhoStd (n + 1)) ≠ -rhoStd (n + 1))
def PairingStep : Prop :=
  ∀ (n : ℕ) (ρ lam : Fin (n + 1) → ℤ) (w : Equiv.Perm (Fin (n + 1))) (a : Fin n),
    (dotAct ρ w lam + ρ) a.castSucc - (dotAct ρ w lam + ρ) a.succ =
      (lam + ρ) (w⁻¹ a.castSucc) - (lam + ρ) (w⁻¹ a.succ)
def SimpleReflPairing : Prop :=
  ∀ (n : ℕ) (ρ μ : Fin (n + 1) → ℤ) (a : Fin n), IsRho ρ →
    dotAct ρ (adjSwap a) μ a.castSucc - dotAct ρ (adjSwap a) μ a.succ =
      -(μ a.castSucc - μ a.succ) - 2
def TwoRhoSpec : Prop :=
  ∀ (n : ℕ) (ρ : Fin (n + 1) → ℤ), IsRho ρ → ρ - permAct Fin.revPerm ρ = twoRho (n + 1)
def DotActionLongestElement : Prop :=
  ∀ (n : ℕ) (ρ lam : Fin (n + 1) → ℤ), IsRho ρ →
    dotAct ρ Fin.revPerm lam = permAct Fin.revPerm lam - twoRho (n + 1) ∧
    -dotAct ρ Fin.revPerm lam - twoRho (n + 1) = -permAct Fin.revPerm lam ∧
    (Antitone lam → Antitone (-permAct Fin.revPerm lam))
def rootList {n : ℕ} : List (Fin n) → List (Fin (n + 1) × Fin (n + 1))
  | [] => []
  | a :: ω => ((wordPerm ω)⁻¹ a.castSucc, (wordPerm ω)⁻¹ a.succ) :: rootList ω
def stepRoot {n : ℕ} (ω : List (Fin n)) (r : ℕ) : Fin (n + 1) × Fin (n + 1) :=
  (rootList ω).reverse.getD r (0, 0)
def StepRootSpec : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)) (r : ℕ), r < ω.length →
    ∃ a : Fin n, ω[ω.length - 1 - r]? = some a ∧
      stepRoot ω r = ((wordPerm (ω.drop (ω.length - r)))⁻¹ a.castSucc,
        (wordPerm (ω.drop (ω.length - r)))⁻¹ a.succ)
def WordRoots : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) →
    (rootList ω).Nodup ∧ (∀ p : Fin (n + 1) × Fin (n + 1), p ∈ rootList ω ↔ p.1 < p.2) ∧
      ω.length = (n + 1).choose 2
def stepN {n : ℕ} (U : Fin (n + 1) → ℤ) (ω : List (Fin n)) (r : ℕ) : ℕ :=
  (U (stepRoot ω r).1 - U (stepRoot ω r).2 - 1).toNat
def WordSum : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)) (U : Fin (n + 1) → ℤ) (l : ℕ), wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) → StrictAnti U →
    (∀ r < ω.length, 1 ≤ U (stepRoot ω r).1 - U (stepRoot ω r).2) ∧
      ∑ r ∈ Finset.range ω.length, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (stepN U ω r) = eExp U l
def ScalarOfCyclic : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (D N : Type) [AddCommGroup D] [Module R D]
    [Module A D] [IsScalarTower R A D] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (F ι : D →ₗ[A] N) (v : D) (c : R),
    Submodule.span A {v} = ⊤ → F v = c • ι v → ∀ x : D, F x = c • ι x
def ScalarStep : Prop :=
  ∀ (R : Type) [CommRing R] (D N : Type) [AddCommGroup D] [Module R D] [AddCommGroup N] [Module R N]
    (F ι : D →ₗ[R] N) (c t : R) (e : ℕ), (∀ x : D, F x = c • ι x) →
    (∀ z : N, t ^ e • z ∈ LinearMap.range F) →
    (∀ z : N, t ^ e • z ∈ LinearMap.range ι) ∧
      ∀ (π : N →ₗ[R] R) (v : D), π (ι v) = 1 → c ∣ t ^ e
def DualTorsionFree : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (M : Type) [AddCommGroup M] [Module R M] (a : R)
    (φ : Module.Dual R M), a • φ = 0 → a = 0 ∨ φ = 0
def ExponentBoundLongestWord : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (ω : List (Fin n)) (U : Fin (n + 1) → ℤ) (l : ℕ),
    wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) → StrictAnti U →
    ∀ (H : ℕ → Type) [∀ r, AddCommGroup (H r)] [∀ r, Module R (H r)]
      (f : ∀ r, H (r + 1) →ₗ[R] H r) (ι : H ω.length →ₗ[R] H 0) (c : R),
      (∀ r < ω.length, ∀ y : H r, (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (stepN U ω r) • y ∈ LinearMap.range (f r)) →
      (∀ x : H ω.length, chainComp f ω.length x = c • ι x) →
      ∀ z : H 0, (l : R) ^ eExp U l • z ∈ LinearMap.range ι
def LemmaABounds : Prop :=
  ∀ (l N : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U →
    eExp U l ≤ ∑ p ∈ posPairs N, Nat.log l (U p.1 - U p.2).toNat ∧
    ((∀ p ∈ posPairs N, U p.1 - U p.2 - 1 < (l : ℤ)) → eExp U l = 0) ∧
    ((∀ p ∈ posPairs N, U p.1 - U p.2 < (l : ℤ)) → eExp U l = 0)
def FlatBaseChangeInj : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O] (M : Type)
    [AddCommGroup M] [Module R M] (N : Submodule R M),
    Function.Injective (N.subtype.baseChange O)
def BaseChangeQuot : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (M : Type) [AddCommGroup M] [Module R M]
    (N : Submodule R M),
    Nonempty ((O ⊗[R] (M ⧸ N)) ≃ₗ[O] ((O ⊗[R] M) ⧸ N.baseChange O))
def BaseChangeIncl : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O] (M : Type)
    [AddCommGroup M] [Module R M] (N : Submodule R M) (t : R) (J : ℕ),
    (∀ x : M, t ^ J • x ∈ N) ↔ ∀ y : O ⊗[R] M, (algebraMap R O t) ^ J • y ∈ N.baseChange O
def ExpIndep : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O] (M : Type)
    [AddCommGroup M] [Module R M] (N : Submodule R M) (t : R),
    sInf {J : ℕ | ∀ x : M, t ^ J • x ∈ N} =
      sInf {J : ℕ | ∀ y : O ⊗[R] M, (algebraMap R O t) ^ J • y ∈ N.baseChange O}
def ProductBaseChange : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (ι : Type) [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (t : R)
    (e : ι → ℕ), (∀ i, ∀ x : M i, t ^ e i • x ∈ N i) →
    ∀ y : ⨂[O] i, (O ⊗[R] M i), (algebraMap R O t) ^ (∑ i, e i) • y ∈
      Formalism.RankGapBounds.FormsTensorLocalization.tensSub (fun i => (N i).baseChange O)
def FiniteFaithfullyFlat : Prop :=
  ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] [IsDomain O]
    [Algebra R O] [Module.Finite R O], Function.Injective (algebraMap R O) →
    Module.FaithfullyFlat R O
def LgLog : Prop :=
  ∀ l y : ℕ, (Nat.log l y : ℝ) * Real.log l ≤ Real.log y
def EExpInterval : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ) (lo : ℤ), l.Prime → StrictAnti U →
    (∀ a, lo ≤ U a ∧ U a ≤ lo + (h : ℤ)) →
    eExp U l ≤ N.choose 2 * Nat.log l h ∧ (h ≤ l → eExp U l = 0)
def JALogBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (l N : ℕ) (U : ι → Fin N → ℤ) (lo : ι → ℤ) (h ex : ι → ℕ), l.Prime →
    (∀ τ, StrictAnti (U τ)) → (∀ τ a, lo τ ≤ U τ a ∧ U τ a ≤ lo τ + (h τ : ℤ)) →
    (∀ τ, ex τ ≤ eExp (U τ) l) →
    ((∑ τ, ex τ : ℕ) : ℝ) * Real.log l ≤ ∑ τ, (N.choose 2 : ℝ) * Real.log (h τ)
def SpecialPrimeCost : Prop :=
  ∀ (ι : Type) [Fintype ι] (l N : ℕ) (b : ℝ) (U : ι → Fin N → ℤ) (lo : ι → ℤ) (h ex : ι → ℕ),
    l.Prime → (∀ τ, StrictAnti (U τ)) → (∀ τ a, lo τ ≤ U τ a ∧ U τ a ≤ lo τ + (h τ : ℤ)) →
    (∀ τ, ex τ ≤ eExp (U τ) l) → 0 < b → (∀ τ, (h τ : ℝ) ≤ 2 * b) → 2 ≤ Real.log b →
    ((∑ τ, ex τ : ℕ) : ℝ) * Real.log l ≤
        (Fintype.card ι : ℝ) * (N.choose 2 : ℝ) * Real.log (2 * b) ∧
      (Fintype.card ι : ℝ) * (N.choose 2 : ℝ) * Real.log (2 * b) ≤
        (Fintype.card ι : ℝ) * ((N : ℝ) ^ 2 / 2) * (Real.log b + Real.log 2) ∧
      (Fintype.card ι : ℝ) * ((N : ℝ) ^ 2 / 2) * (Real.log b + Real.log 2) ≤
        (Fintype.card ι : ℝ) * (N : ℝ) ^ 2 * Real.log b
def LargePrimeZero : Prop :=
  ∀ (g N h k b : ℕ) (U : Fin N → ℤ) (lo : ℤ), g.Prime → StrictAnti U →
    (∀ a, lo ≤ U a ∧ U a ≤ lo + (h : ℤ)) → 1 ≤ k → 2 ≤ b → h ≤ 2 * b → (k * b) ^ 8 ≤ g →
    2 * b < (k * b) ^ 8 ∧ eExp U g = 0
structure Shape (N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ) : Prop where
  anti : StrictAnti U
  inRange : ∀ a, 0 ≤ U a ∧ U a ≤ (h : ℤ)
  k_le : k ≤ N
  cloudIn : ∀ a : Fin N, a.val < k → xm ≤ U a ∧ U a ≤ xm + (S : ℤ)
  restIn : ∀ a : Fin N, k ≤ a.val → lo ≤ U a ∧ U a ≤ lo + (eta : ℤ)
def eCl {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat
def eRest {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat
def eCross {N : ℕ} (U : Fin N → ℤ) (k l : ℕ) : ℕ :=
  ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val),
    Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat
def cloudOf {N k : ℕ} (hk : k ≤ N) (U : Fin N → ℤ) : Fin k → ℤ := fun a => U (Fin.castLE hk a)
def restOf {N k : ℕ} (hk : k ≤ N) (U : Fin N → ℤ) : Fin (N - k) → ℤ :=
  fun a => U ⟨k + a.val, by have := a.isLt; omega⟩
def ESplit3 : Prop :=
  ∀ (N k l : ℕ) (U : Fin N → ℤ), eExp U l = eCl U k l + eRest U k l + eCross U k l
def EPartsEq : Prop :=
  ∀ (N k l : ℕ) (hk : k ≤ N) (U : Fin N → ℤ),
    eCl U k l = eExp (cloudOf hk U) l ∧ eRest U k l = eExp (restOf hk U) l
def ChooseSplit : Prop :=
  ∀ N k : ℕ, k ≤ N →
    k.choose 2 + (N - k).choose 2 + k * (N - k) = N.choose 2 ∧
    ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 ∧
    ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 ∧
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k)
def ThreeBounds : Prop :=
  ∀ (l N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime → Shape N k h S eta xm lo U →
    eCl U k l ≤ k.choose 2 * Nat.log l S ∧ (S ≤ l → eCl U k l = 0) ∧
    eRest U k l ≤ (N - k).choose 2 * Nat.log l eta ∧ (eta ≤ l → eRest U k l = 0) ∧
    eCross U k l ≤ k * (N - k) * Nat.log l h ∧
    k * (N - k) * Nat.log l h ≤ k * (N - k) * Nat.log l (2 * h + N)
def ExactSplit : Prop :=
  LemmaAZ → ∀ (l N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime →
    ∀ sh : Shape N k h S eta xm lo U,
    exZ N N le_rfl (nuOf U) l ≤ eCl U k l + eRest U k l + eCross U k l ∧
    exZ k k le_rfl (nuOf (cloudOf sh.k_le U)) l ≤ eCl U k l
def SizeAll : Prop :=
  ∀ (l N k h S eta ex : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime → Shape N k h S eta xm lo U →
    ex ≤ eExp U l →
    (ex : ℝ) * Real.log l ≤
        ((k.choose 2 : ℝ) + ((N - k).choose 2 : ℝ) + (k : ℝ) * ((N - k : ℕ) : ℝ)) * Real.log h ∧
      ((k.choose 2 : ℝ) + ((N - k).choose 2 : ℝ) + (k : ℝ) * ((N - k : ℕ) : ℝ)) * Real.log h =
        (N.choose 2 : ℝ) * Real.log h ∧
      (N.choose 2 : ℝ) * Real.log h ≤ (N : ℝ) ^ 2 * Real.log (2 * (h : ℝ) + N)
def SizeLarge : Prop :=
  ∀ (l N k h S eta ex m t : ℕ) (xm lo : ℤ) (U : Fin N → ℤ), l.Prime →
    Shape N k h S eta xm lo U → ex ≤ eExp U l → eta ≤ l → N - k ≤ m + t →
    (ex : ℝ) * Real.log l ≤
        (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ∧
      (k : ℝ) * ((N - k : ℕ) : ℝ) * Real.log h + (k.choose 2 : ℝ) * Real.log S ≤
        (k : ℝ) * ((m : ℝ) + t) * Real.log (3 * (h : ℝ)) + (k : ℝ) ^ 2 * Real.log ((S : ℝ) + k)
def ExponentBoundCounterexample : Prop :=
  eExp (fun a : Fin 24 => (46 : ℤ) - 2 * (a.val : ℤ)) 13 = 142 ∧
    ((24 : ℝ) * (46 + 24) / (13 - 1) = 140)
def polyBC (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ) :
    (O ⊗[R] MvPolynomial (Fin r × Fin n) R) ≃ₗ[O] MvPolynomial (Fin r × Fin n) O :=
  (MvPolynomial.algebraTensorAlgEquiv R O).toLinearEquiv
def LatticeTensor : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
    ((weyl R r n hn ν).baseChange O).map (polyBC R O r n).toLinearMap = weyl O r n hn ν ∧
    (IsDomain O →
      ((dualWeyl R r n ν).baseChange O).map (polyBC R O r n).toLinearMap = dualWeyl O r n ν)
def LatticeBaseChange : Prop :=
  ∀ (R O : Type) [CommRing R] [CommRing O] [IsDomain O] [Algebra R O] [Module.FaithfullyFlat R O]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (t : R) (e : ℕ),
    (∀ x ∈ dualWeyl R r n ν, t ^ e • x ∈ weyl R r n hn ν) ↔
      ∀ x ∈ dualWeyl O r n ν, (algebraMap R O t) ^ e • x ∈ weyl O r n hn ν
def LatticeExpIndep : Prop :=
  ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] [IsDomain O]
    [Algebra R O] [Module.Finite R O], Function.Injective (algebraMap R O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (t : R),
    sInf {e : ℕ | ∀ x ∈ dualWeyl R r n ν, t ^ e • x ∈ weyl R r n hn ν} =
      sInf {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (algebraMap R O t) ^ e • x ∈ weyl O r n hn ν}
def RhoDominant : Prop :=
  ∀ (n : ℕ) (ρ lam : Fin (n + 1) → ℤ), IsRho ρ →
    (∀ i j : Fin (n + 1), ρ i - ρ j = (j.val : ℤ) - (i.val : ℤ)) ∧
    (Antitone lam → StrictAnti (lam + ρ))
def DotWordStep : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)) (ρ lam : Fin (n + 1) → ℤ) (r : ℕ), r < ω.length →
    ∃ a : Fin n, ω[ω.length - 1 - r]? = some a ∧
      dotAct ρ (wordPerm (ω.drop (ω.length - (r + 1)))) lam =
        dotAct ρ (adjSwap a) (dotAct ρ (wordPerm (ω.drop (ω.length - r))) lam) ∧
      (dotAct ρ (wordPerm (ω.drop (ω.length - r))) lam + ρ) a.castSucc -
          (dotAct ρ (wordPerm (ω.drop (ω.length - r))) lam + ρ) a.succ =
        (lam + ρ) (stepRoot ω r).1 - (lam + ρ) (stepRoot ω r).2 ∧
      stepN (lam + ρ) ω r =
        ((dotAct ρ (wordPerm (ω.drop (ω.length - r))) lam + ρ) a.castSucc -
          (dotAct ρ (wordPerm (ω.drop (ω.length - r))) lam + ρ) a.succ - 1).toNat
def EExpShift : Prop :=
  ∀ (N l : ℕ) (U : Fin N → ℤ) (c : ℤ), eExp (fun a => U a + c) l = eExp U l
def ExZZero : Prop :=
  LemmaAZ → ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    eExp (lamU r n ν) l = 0 → exZ r n hn ν l = 0 ∧ InclZ r n hn ν l 0
end Formalism.CohomologicalDescent.SL2BinomialLattices


