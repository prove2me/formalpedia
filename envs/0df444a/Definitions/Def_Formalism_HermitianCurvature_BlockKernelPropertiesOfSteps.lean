-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
-- name    : Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:48.099492+00:00
-- url     : https://prove2.me/theorems/ab83d495-280f-4081-a1cd-9b8c4bfd4f62
-- title:
--   Block Kernel Properties Of Steps
-- statement:
--   Definitions and structural lemmas for Block Kernel Properties Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/BlockKernelPropertiesOfSteps.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.A5
structure LocalDatum (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ψ : AddChar K ℂ) : Prop where

  t2 : T2Space K

  isOpen : IsOpen (R : Set K)

  isCompact : IsCompact (R : Set K)

  unif : ∃ ϖ : Kˣ, (ϖ : K) ∈ R ∧ ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R

  artin : IsArtinianRing K

  red : IsReduced K

  unitRep : ∀ x : K, ∃ r ∈ R, IsUnit (x + r)

  unitary : ∀ x : K, conj (ψ x) = ψ (-x)

  selfDual : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R
section Defs
variable {K : Type} [CommRing K]
def mulR (R : Subring K) (x : K) : AddSubgroup K :=
  R.toAddSubgroup.map (AddMonoidHom.mulLeft x)
def modK (R : Subring K) (x : K) : ℝ :=
  (R.toAddSubgroup.relIndex (mulR R x) : ℝ) / ((mulR R x).relIndex R.toAddSubgroup : ℝ)
abbrev Point (K : Type) [CommRing K] : Type := List ℕ × (ℕ → Kˣ)
def addBlock (h : Point K) (s : ℕ) (t : Kˣ) : Point K :=
  (h.1 ++ [s], Function.update h.2 h.1.length t)
def cSize (R : Subring K) (h : Point K) : ℝ := (modK R (pt h.1 h.2).det)⁻¹
def InGLR (R : Subring K) (h : Point K) : Prop :=
  IsInt R (pt h.1 h.2) ∧ IsInt R (pt h.1 h.2)⁻¹
def IsPSD {X : Type} (F : Finset X) (k : X → X → ℂ) : Prop :=
  ∀ a : X → ℂ, (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y).re
variable (R : Subring K)
def psiKR (ψ : AddChar K ℂ) (x : KR R) : ℂ := ψ (Quotient.out x)
def rowN {n : ℕ} (j : ℕ) : (Fin n → K) →ₗ[R] K :=
  ∑ a : Fin n, if a.val = j then (LinearMap.proj a : (Fin n → K) →ₗ[R] K) else 0
def lamTil {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (j : ℕ) : (Fin n → R) →ₗ[R] K :=
  (rowN R j).comp ((Z⁻¹.mulVecLin.restrictScalars R).comp (coeLin R))
def lamN {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (j : ℕ) : (Fin n → R) →ₗ[R] KR R :=
  (Submodule.mkQ _).comp (lamTil R Z j)
def isoZZ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K) :
    Set (coker R Z ≃ₗ[R] coker R Z') :=
  {φ | φ (eZ R Z) = eZ R Z' ∧ ∀ (v : Fin n → R) (v' : Fin n' → R),
    φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' → lamLin R Z' v' = lamLin R Z v}
def autSet (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    Set (C ≃ₗ[R] C) := {φ | φ e = e ∧ ∀ c, lam (φ c) = lam c}
def InTT {n n' : ℕ} (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (φ : coker R Z ≃ₗ[R] coker R Z') : Prop :=
  ∀ j, k ≤ j → j < n → ∃ a : ℕ → R, ∀ (v : Fin n → R) (v' : Fin n' → R),
    φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
      lamN R Z' j v' = lamN R Z j v + ∑ l ∈ Finset.Ioo j n, a l • lamN R Z l v
def InTTeq {n n' : ℕ} (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (φ : coker R Z ≃ₗ[R] coker R Z') : Prop :=
  ∀ j, k ≤ j → j < n → ∀ (v : Fin n → R) (v' : Fin n' → R),
    φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' → lamN R Z' j v' = lamN R Z j v
def LiftRel {n n' : ℕ} (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (φ : coker R Z ≃ₗ[R] coker R Z') (v : Fin n → R) (v' : Fin n' → R) : Prop :=
  φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' ∧
    ∀ j, k ≤ j → lamTil R Z' j v' = lamTil R Z j v
end Defs
section Kernel
variable {K : Type} [CommRing K] (R : Subring K)
abbrev Cos (w : Point K) : Type :=
  Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) ×
    (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))
def rep {w : Point K} (q : Cos R w) : lowW K w.1 w.2 × upUniG K w.1.sum := (q.1.out, q.2.out)
def orbZ (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    Matrix (Fin w.1.sum) (Fin w.1.sum) K :=
  ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) * pt w.1 w.2 *
    ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)
def phase (ψ : AddChar K ℂ) {w : Point K} (p : lowW K w.1 w.2 × upUniG K w.1.sum) : ℂ :=
  ψ (sLow ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) +
    sUp ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K))
open Classical in

def pairTerm (ψ : AddChar K ℂ) (w w' : Point K) (q : Cos R w × Cos R w') : ℂ :=
  (if IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2)) then
    (Nat.card (isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2))) : ℂ) else 0) *
    phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
def Kp (ψ : AddChar K ℂ) (w w' : Point K) : ℂ := ∑ᶠ q : Cos R w × Cos R w', pairTerm R ψ w w' q
open Classical in

def intTT (ψ : AddChar K ℂ) (k : ℕ) (w w' : Point K) : ℂ :=
  ∑ᶠ q : Cos R w × Cos R w',
    (if IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2)) then
      (Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
        InTT R k (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} : ℂ) else 0) *
      phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
def N0 (ψ : AddChar K ℂ) (h h' : Point K) : ℂ := Kp R ψ h h'
def Ns (ψ : AddChar K ℂ) (s : ℕ) (h h' : Point K) (t t' : Kˣ) : ℂ :=
  ((modK R ((t : K) * (t' : K)) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
    Kp R ψ (addBlock h s t) (addBlock h' s t')
end Kernel
def IsoZZIsIso : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n n' : ℕ) (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (lam' : coker R Z' →ₗ[R] KR R),
    (∀ v', lam' (Submodule.Quotient.mk v') = lamLin R Z' v') →
      isoZZ R Z Z' = isoSet R Z (coker R Z') (eZ R Z') lam'
def LamLast : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n : ℕ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) K),
    lamN R Z n = lamLin R Z
def IsoCount : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n n' : ℕ) (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (ι : Type) [Fintype ι] (C : ι → Type)
    [∀ a, AddCommGroup (C a)] [∀ a, Module R (C a)] (e : ∀ a, C a) (lam : ∀ a, C a →ₗ[R] KR R),
    (∀ a b, a ≠ b → ¬ ∃ φ : C a ≃ₗ[R] C b, φ (e a) = e b ∧ ∀ c, lam b (φ c) = lam a c) →
    (∃ a, (isoSet R Z (C a) (e a) (lam a)).Nonempty) →
    ∑ a, (Nat.card (isoSet R Z (C a) (e a) (lam a)) : ℂ) *
        (Nat.card (isoSet R Z' (C a) (e a) (lam a)) : ℂ) /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) = (Nat.card (isoZZ R Z Z') : ℂ)
def KpFinite : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ w w' : Point K,
      (Function.support (pairTerm R ψ w w')).Finite
def IntFinite : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ w : Point K,
      {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite
def GramIdentity : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (w w' : Point K)
    (μ₁ : Measure (lowW K w.1 w.2)) (μ₂ : Measure (upUniG K w.1.sum))
    (μ₁' : Measure (lowW K w'.1 w'.2)) (μ₂' : Measure (upUniG K w'.1.sum))
    [μ₁.IsMulRightInvariant] [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂]
    [μ₁'.IsMulRightInvariant] [μ₂'.IsMulLeftInvariant] [SFinite μ₁'] [SFinite μ₂'],
    μ₁ (intSub R (lowW K w.1 w.2) : Set (lowW K w.1 w.2)) = 1 →
    μ₂ (intSub R (upUniG K w.1.sum) : Set (upUniG K w.1.sum)) = 1 →
    μ₁' (intSub R (lowW K w'.1 w'.2) : Set (lowW K w'.1 w'.2)) = 1 →
    μ₂' (intSub R (upUniG K w'.1.sum) : Set (upUniG K w'.1.sum)) = 1 →
    ∀ (ι : Type) [Fintype ι] (C : ι → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module R (C a)]
      (e : ∀ a, C a) (lam : ∀ a, C a →ₗ[R] KR R),
    (∀ a b, a ≠ b → ¬ ∃ φ : C a ≃ₗ[R] C b, φ (e a) = e b ∧ ∀ c, lam b (φ c) = lam a c) →
    (∀ p, IsInt R (orbZ w p) → ∃ a, (isoSet R (orbZ w p) (C a) (e a) (lam a)).Nonempty) →
    ∑ a, BB R w.1 w.2 ψ (C a) (e a) (lam a) μ₁ μ₂ *
        conj (BB R w'.1 w'.2 ψ (C a) (e a) (lam a) μ₁' μ₂') /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) = Kp R ψ w w'
def KpGram : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ F : Finset (Point K), IsPSD F (Kp R ψ)
def ModMul : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ x y : Kˣ,
      0 < modK R (x : K) ∧ modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K)
def CokerCard : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) K),
      IsInt R Z → IsUnit Z.det →
        Finite (coker R Z) ∧ (Nat.card (coker R Z) : ℝ) = (modK R Z.det)⁻¹
def KpBlockDiag : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ w w' : Point K, Kp R ψ w w' ≠ 0 →
      modK R (pt w.1 w.2).det = modK R (pt w'.1 w'.2).det
def NsBlockDiag : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ h h' : Point K, h.1.sum = h'.1.sum →
      (N0 R ψ h h' ≠ 0 → modK R (pt h.1 h.2).det = modK R (pt h'.1 h'.2).det) ∧
      ∀ (s : ℕ) (t : Kˣ), Ns R ψ s h h' t t ≠ 0 →
        modK R (pt h.1 h.2).det = modK R (pt h'.1 h'.2).det
def DualSpan : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ),
    (∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) →
    ∀ (C : Type) [AddCommGroup C] [Module R C] [Finite C] (ι : Type) [Fintype ι]
      (lam : ι → C →ₗ[R] KR R) (μ : C →ₗ[R] KR R),
      (∀ c, (∀ j, lam j c = 0) → μ c = 0) → μ ∈ Submodule.span R (Set.range lam)
def EndKR : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ f : KR R →ₗ[R] KR R, ∃ r : R, ∀ x, f x = r • x
def InvLastCol : Prop :=
  ∀ (K : Type) [CommRing K] (h : Point K) (s : ℕ) (t : Kˣ), 1 ≤ s →
    ∀ x y : Matrix (Fin (addBlock h s t).1.sum) (Fin (addBlock h s t).1.sum) K,
      IsLowUni x → IsUpUni y →
      ∀ a b c : Fin (addBlock h s t).1.sum, b.val + 1 = (addBlock h s t).1.sum →
        c.val = h.1.sum →
        (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)⁻¹ a b = ((t⁻¹ : Kˣ) : K) * y⁻¹ a c ∧
        (c < a → (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)⁻¹ a b = 0) ∧
        (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)⁻¹ c b = ((t⁻¹ : Kˣ) : K)
def ColOp : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (Z u : Matrix (Fin n) (Fin n) K) (m : Fin n → K)
    (c r : Fin n), IsUnit Z.det → IsUpUni u → r.val + 1 = c.val →
    (∀ a, c ≤ a → (Z⁻¹ *ᵥ m) a = 0) →
      IsUpUni (1 + vecMulVec (Z⁻¹ *ᵥ m) (Pi.single c 1)) ∧
      Z * (1 + vecMulVec (Z⁻¹ *ᵥ m) (Pi.single c 1)) = Z + vecMulVec m (Pi.single c 1) ∧
      (∀ a b, c ≤ a → (Z + vecMulVec m (Pi.single c 1))⁻¹ a b = Z⁻¹ a b) ∧
      sUp (u * (1 + vecMulVec (Z⁻¹ *ᵥ m) (Pi.single c 1))) = sUp u + (Z⁻¹ *ᵥ m) r
def ColOpRow : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K)
    (c : Fin n), IsUnit Z.det → (∀ a, c ≤ a → (Z⁻¹ *ᵥ m) a = 0) →
      ∀ a b, (Z + vecMulVec m (Pi.single c 1))⁻¹ a b = Z⁻¹ a b - (Z⁻¹ *ᵥ m) a * Z⁻¹ c b
def ColOpTriple : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) K),
    IsInt R Z → IsInt R Z' → IsUnit Z.det → IsUnit Z'.det →
    ∀ φ ∈ isoZZ R Z Z', ∀ c : Fin n, InTTeq R c.val Z Z' φ →
    LiftRel R c.val Z Z' φ (eLast R) (eLast R) →
    ∀ m m' : Fin n → R, LiftRel R c.val Z Z' φ m m' → (∀ j, c.val ≤ j → lamTil R Z j m = 0) →
    ∃ φn : coker R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) ≃ₗ[R]
        coker R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)),
      φn ∈ isoZZ R (Z + vecMulVec (coeLin R m) (Pi.single c 1))
        (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) ∧
      InTTeq R c.val (Z + vecMulVec (coeLin R m) (Pi.single c 1))
        (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) φn ∧
      ∀ v v', LiftRel R c.val Z Z' φ v v' →
        φn (Submodule.Quotient.mk v) = Submodule.Quotient.mk v'
def TripleForm : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (w w' : Point K) (k : ℕ),
    w.1.sum = k + 1 → w'.1.sum = k + 1 → Kp R ψ w w' = intTT R ψ k w w'
def TTStep : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ),
    (∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) →
    ∀ (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) K), IsUnit Z.det → IsUnit Z'.det →
    Finite (coker R Z) → ∀ φ : coker R Z ≃ₗ[R] coker R Z', ∀ k, k < n →
    InTT R (k + 1) Z Z' φ →
      (InTT R k Z Z' φ ↔ ∀ (v : Fin n → R) (v' : Fin n → R),
        φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        (∀ j, k < j → lamN R Z j v = 0) → lamN R Z' k v' = lamN R Z k v)
def AvgClaim : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ),
    h.1.sum = h'.1.sum → h.1.sum ≤ k → k + 2 ≤ h.1.sum + s →
      intTT R ψ (k + 1) (addBlock h s t) (addBlock h' s t') =
        intTT R ψ k (addBlock h s t) (addBlock h' s t')
def TTEnd : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (h h' : Point K) (s : ℕ) (t t' : Kˣ),
    h.1.sum = h'.1.sum → 1 ≤ s →
    ∀ (x y : Matrix (Fin (addBlock h s t).1.sum) (Fin (addBlock h s t).1.sum) K)
      (x' y' : Matrix (Fin (addBlock h' s t').1.sum) (Fin (addBlock h' s t').1.sum) K),
      IsLowUni x → IsUpUni y → IsLowUni x' → IsUpUni y' →
      ∀ φ ∈ isoZZ R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)
          (x' * pt (addBlock h' s t').1 (addBlock h' s t').2 * y'),
        InTT R h.1.sum (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)
          (x' * pt (addBlock h' s t').1 (addBlock h' s t').2 * y') φ →
        ((t⁻¹ : Kˣ) : K) - ((t'⁻¹ : Kˣ) : K) ∈ R
def BlockKernelSupport : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (s : ℕ), 1 ≤ s → ∀ (h h' : Point K) (t t' : Kˣ),
    h.1.sum = h'.1.sum → Ns R ψ s h h' t t' ≠ 0 → ((t⁻¹ : Kˣ) : K) - ((t'⁻¹ : Kˣ) : K) ∈ R
def BlockKernelPosSemidef : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (s : ℕ), 1 ≤ s → ∀ (m : ℕ)
    (F : Finset (Point K × Kˣ)), (∀ x ∈ F, x.1.1.sum = m) →
      IsPSD F (fun x y => Ns R ψ s x.1 y.1 x.2 y.2)
def A2 : Prop := BlockKernelPosSemidef ∧ BlockKernelSupport
def BlockKernelPropertiesOfSteps : Prop :=
  KpGram → ModMul → TripleForm → AvgClaim → TTEnd → A2
open Classical in

def CharOrthDual : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) K),
      IsInt R Z → IsUnit Z.det → Finite (coker R Z →ₗ[R] KR R) ∧ ∀ x : coker R Z,
        ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) =
          ((if x = 0 then Nat.card (coker R Z) else 0 : ℕ) : ℂ)
open Classical in

def CharOrth : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) K),
      IsInt R Z → IsUnit Z.det → ∀ μ : coker R Z →ₗ[R] KR R,
        ∑ᶠ β : coker R Z, psiKR R ψ (μ β) =
          ((if μ = 0 then Nat.card (coker R Z) else 0 : ℕ) : ℂ)
open Classical in

def singleBlockInner {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) {n n' : ℕ}
    (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K) (c : K) : ℂ :=
  ∑ᶠ θ : coker R Z ≃ₗ[R] coker R Z', ∑ᶠ α : coker R Z →ₗ[R] KR R, ∑ᶠ β : coker R Z,
    if α β = -(Submodule.Quotient.mk c : KR R) then
      psiKR R ψ (α (eZ R Z - θ.symm (eZ R Z')) +
        (lamLin R Z (Quotient.out β) - lamLin R Z' (Quotient.out (θ β))))
    else 0
open Classical in

def SingleBlockFormula : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (h h' : Point K) (c : Kˣ), h.1.sum = h'.1.sum →
      Ns R ψ 1 h h' c c = ∑ᶠ q : Cos R h × Cos R h',
        (if IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) then
          singleBlockInner R ψ (orbZ h (rep R q.1)) (orbZ h' (rep R q.2)) (c : K) else 0) *
          phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
def SingleBlockPeriodic : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (h h' : Point K) (c c' : Kˣ), h.1.sum = h'.1.sum →
      (c : K) - (c' : K) ∈ R → Ns R ψ 1 h h' c c = Ns R ψ 1 h h' c' c'
def SingleBlockPosSemidef : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m : ℕ) (F : Finset (Point K)),
      (∀ h ∈ F, h.1.sum = m) → ∀ c : Kˣ, IsPSD F (fun h h' => Ns R ψ 1 h h' c c)
def SingleBlockParseval : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (h h' : Point K), h.1.sum = h'.1.sum →
    ∀ cr : K ⧸ R.toAddSubgroup → Kˣ, (∀ x, ((cr x : K) : K ⧸ R.toAddSubgroup) = x) →
      (Function.support (fun x => Ns R ψ 1 h h' (cr x) (cr x))).Finite ∧
      ∑ᶠ x : K ⧸ R.toAddSubgroup, Ns R ψ 1 h h' (cr x) (cr x) =
        ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h'
def SingleBlockOfSteps : Prop :=
  SingleBlockFormula → IntFinite → CharOrthDual → CharOrth → CokerCard → BlockKernelPosSemidef →
    SingleBlockPeriodic ∧ SingleBlockPosSemidef ∧ SingleBlockParseval
def NsSupport : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (s : ℕ), 1 ≤ s →
    ∀ (h h' : Point K) (t t' : Kˣ), Ns R ψ s h h' t t' ≠ 0 →
      (pt h.1 h.2).det * (t : K) ∈ R ∧ (pt h'.1 h'.2).det * (t' : K) ∈ R
def BaseKernelOne : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ), (∀ r ∈ R, ψ r = 1) →
    ∀ h h' : Point K, h.1.sum = h'.1.sum → InGLR R h → InGLR R h' → N0 R ψ h h' = 1
open Classical in

def ThetaProps {K : Type} [CommRing K] [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ)
    (s : ℕ) (F : Finset (Point K)) (Θ : K → Point K → Point K → ℂ) : Prop :=
  (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
  (∀ x, IsPSD F (Θ x)) ∧
  (∃ L : Submodule R K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
    ∀ x, x ∉ L → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) ∧
  (∀ t : Kˣ, IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ s h h' t t)) ∧
  IsPSD F (fun h h' => ((cSize R h ^ s * cSize R h' ^ s : ℝ) : ℂ) * N0 R ψ h h' -
    ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h') ∧
  (∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det →
    Θ x h h' = 0) ∧
  ((∀ h ∈ F, InGLR R h) →
    ∀ x, IsPSD F (fun h h' => (if x ∈ R then N0 R ψ h h' else 0) - Θ x h h'))
def ThetaExists {K : Type} [CommRing K] [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ)
    (s : ℕ) : Prop :=
  ∀ (m : ℕ) (F : Finset (Point K)), (∀ h ∈ F, h.1.sum = m) →
    ∃ Θ : K → Point K → Point K → ℂ, ThetaProps R ψ s F Θ
def A13 (s : ℕ) : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) → ThetaExists R ψ s
def Th1Eq : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ m : ℕ,
    ∃ Θ : K → Point K → Point K → ℂ,
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      (∀ (t : Kˣ) (h h' : Point K), h.1.sum = m → h'.1.sum = m →
        Θ (t : K) h h' = Ns R ψ 1 h h' t t) ∧
      (∀ h h' : Point K, h.1.sum = m → h'.1.sum = m →
        ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
          ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h')
def SingleBlockThetaProps : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ m : ℕ,
    ∃ Θ : K → Point K → Point K → ℂ,
      (∀ (t : Kˣ) (h h' : Point K), h.1.sum = m → h'.1.sum = m →
        Θ (t : K) h h' = Ns R ψ 1 h h' t t) ∧
      (∀ h h' : Point K, h.1.sum = m → h'.1.sum = m →
        ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
          ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h') ∧
      ∀ F : Finset (Point K), (∀ h ∈ F, h.1.sum = m) → ThetaProps R ψ 1 F Θ
def SingleBlockThetaOfSteps : Prop :=
  SingleBlockPeriodic → SingleBlockPosSemidef → SingleBlockParseval → NsSupport → NsBlockDiag → BaseKernelOne → Th1Eq ∧ SingleBlockThetaProps
def ThetaExistsStep : Prop :=
  A2 → SingleBlockParseval →
    ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
      (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
      ∀ s, 1 ≤ s → ThetaExists R ψ s → ThetaExists R ψ (s + 1)
def LemmaA : Prop :=
  A2 ∧ (∀ s, 1 ≤ s → A13 s) ∧ Th1Eq ∧ SingleBlockThetaProps ∧ BaseKernelOne ∧ NsSupport ∧ NsBlockDiag
def LemmaAAssemble : Prop :=
  A2 → SingleBlockParseval → Th1Eq → SingleBlockThetaProps → ThetaExistsStep → BaseKernelOne → NsSupport → NsBlockDiag → LemmaA
def DatumPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∃ ψ : AddChar ℚ_[p] ℂ, LocalDatum ℚ_[p] (PadicInt.subring p) ψ) ∧
      ∀ n : ℕ, n ≠ 0 → IsUnit (n : ℚ_[p])
end Formalism.FourierDecayAlt.A5


