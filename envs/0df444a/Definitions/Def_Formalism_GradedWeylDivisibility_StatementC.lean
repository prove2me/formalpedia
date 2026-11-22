-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
-- name    : Formalism_GradedWeylDivisibility_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:23.642201+00:00
-- url     : https://prove2.me/theorems/391e4b29-28b6-4396-a3bc-d23ccb5f31dc
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementC.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
def cmIdx (r n : ℕ) : Fin r × Fin n ≃ Fin (n * r) :=
  (Equiv.prodComm (Fin r) (Fin n)).trans finProdFinEquiv
def colLex (r n : ℕ) : MonomialOrder (Fin r × Fin n) where
  syn := Lex (Fin (n * r) →₀ ℕ)
  toSyn :=
    { toEquiv := (Finsupp.domCongr (cmIdx r n)).toEquiv.trans toLex
      map_add' := fun a b => by
        show toLex (Finsupp.domCongr (cmIdx r n) (a + b)) =
          toLex (Finsupp.domCongr (cmIdx r n) a) + toLex (Finsupp.domCongr (cmIdx r n) b)
        rw [map_add]; rfl }
  toSyn_monotone := fun a b h => Finsupp.toLex_monotone (α := Fin (n * r)) (N := ℕ)
    (show Finsupp.domCongr (cmIdx r n) a ≤ Finsupp.domCongr (cmIdx r n) b from fun i => h _)
def bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    Fin r × Fin n →₀ ℕ :=
  ∑ k : Fin K, ∑ p : Fin (sz k), Finsupp.single (I k p, Fin.castLE (hsz k) p) 1
def colExp {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) : Fin r × Fin n →₀ ℕ :=
  ∑ p : Fin h, Finsupp.single (c p, Fin.castLE hh p) 1
def InterlacedAt {r n : ℕ} (s : ℕ) (l j : Fin n) (m : Fin r × Fin n →₀ ℕ) : Prop :=
  ∀ a : Fin r, (∑ b : Fin r with b ≤ a, m (b, j)) ≤ s + ∑ b : Fin r with b < a, m (b, l)
def Interlaced {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) : Prop :=
  ∀ l j : Fin n, j.val = l.val + 1 → InterlacedAt 0 l j m
def pairW {r n : ℕ} (l j : Fin n) : Fin r × Fin n → (Fin r × Fin n →₀ ℕ) :=
  fun v => if v.2 = j then Finsupp.single (v.1, l) 1 else Finsupp.single v 1
def peel {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) : MvPolynomial (Fin r × Fin n) B :=
  ∑ m ∈ g.support.filter (fun m => m (a0, l) = k),
    monomial ((m.erase (a0, l)).erase (a0, j)) (coeff m g)
open scoped MonomialOrder
def ColLexInitMinor : Prop :=
  ∀ (R : Type) [CommRing R] [Nontrivial R] (r n s : ℕ) (I : Fin s → Fin r) (hs : s ≤ n), StrictMono I →
    (colLex r n).degree (initMinor R I hs) = ∑ p : Fin s, Finsupp.single (I p, Fin.castLE hs p) 1 ∧
    (colLex r n).leadingCoeff (initMinor R I hs) = 1
def MinorExpLt : Prop :=
  ∀ (r n s : ℕ) (I : Fin s → Fin r) (hs : s ≤ n), StrictMono I → ∀ σ : Equiv.Perm (Fin s), σ ≠ 1 →
    (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1) ≺[colLex r n]
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1)
def ColumnLexBideterminant : Prop :=
  ∀ (R : Type) [CommRing R] [Nontrivial R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r), (∀ k, StrictMono (I k)) →
    (colLex r n).degree (bideterminant R sz hsz I) = bidetExp sz hsz I ∧
    (colLex r n).leadingCoeff (bideterminant R sz hsz I) = 1
def ColSums : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R),
    f ∈ dualWeyl R r n ν → ∀ m ∈ f.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t
def SSYTPeel : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ),
    (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m → m ≠ 0 →
    ∃ (h : ℕ) (hh : h ≤ n) (c : Fin h → Fin r), StrictMono c ∧ (∀ t : Fin n, t.val < h ↔ 0 < ν t) ∧
      colExp c hh ≤ m ∧ Interlaced (m - colExp c hh) ∧
      ∀ t : Fin n, ∑ a : Fin r, (m - colExp c hh) (a, t) = ν t - (if t.val < h then 1 else 0)
def SSYTExists : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ),
    (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m →
    ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
      shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧ bidetExp sz hsz I = m
def CompDeg : Prop :=
  ∀ (B : Type) [CommRing B] (r n : ℕ) (l j : Fin n) (ω : Fin r × Fin n →₀ ℕ) (s : ℕ)
    (f : MvPolynomial (Fin r × Fin n) B),
    degreeOf none (colAddGen B l j f) ≤ s →
      degreeOf none (colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f)) ≤ s
def LeadComp : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (M : Type) [AddCommMonoid M] (w : Fin r × Fin n → M)
    (f : MvPolynomial (Fin r × Fin n) R),
    (colLex r n).degree (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f) =
      (colLex r n).degree f
def PeelDecomp : Prop :=
  ∀ (B : Type) [CommRing B] (r n : ℕ) (l j : Fin n), l ≠ j → ∀ (a0 : Fin r) (ω : Fin r × Fin n →₀ ℕ)
    (g : MvPolynomial (Fin r × Fin n) B), IsWeightedHomogeneous (pairW l j) g ω →
    g = ∑ k ∈ Finset.range (ω (a0, l) + 1),
      X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g
def PeelHomog : Prop :=
  ∀ (B : Type) [CommRing B] (r n : ℕ) (l j : Fin n), l ≠ j → ∀ (a0 : Fin r) (ω : Fin r × Fin n →₀ ℕ) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B), IsWeightedHomogeneous (pairW l j) g ω →
    IsWeightedHomogeneous (pairW l j) (peel l j a0 k g) (ω.erase (a0, l)) ∧
      ∀ m ∈ (peel l j a0 k g).support, m (a0, l) = 0 ∧ m (a0, j) = 0
def PeelLead : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n), l < j → ∀ (a0 : Fin r)
    (ω : Fin r × Fin n →₀ ℕ) (g : MvPolynomial (Fin r × Fin n) B) (K : ℕ),
    IsWeightedHomogeneous (pairW l j) g ω → (∀ b : Fin r, b < a0 → ω (b, l) = 0) →
    peel l j a0 K g ≠ 0 → (∀ k, K < k → peel l j a0 k g = 0) →
    (colLex r n).degree g = Finsupp.single (a0, l) K + Finsupp.single (a0, j) (ω (a0, l) - K) +
      (colLex r n).degree (peel l j a0 K g)
def EvalDeg : Prop :=
  ∀ (B : Type) [CommRing B] (τ : Type) [DecidableEq τ] (x y c : τ), x ≠ y → x ≠ c → y ≠ c →
    ∀ p : MvPolynomial τ B,
      degreeOf c (aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v) p) ≤
        degreeOf c p + degreeOf y p
def PeelDegBound : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n), l ≠ j → ∀ (a0 : Fin r) (K e s : ℕ)
    (w : ℕ → MvPolynomial (Fin r × Fin n) B),
    (∀ k, ∀ m ∈ (w k).support, m (a0, l) = 0 ∧ m (a0, j) = 0) → w K ≠ 0 →
    degreeOf none (colAddGen B l j
        (∑ k ∈ Finset.range (K + 1), X (a0, l) ^ k * X (a0, j) ^ (e + (K - k)) * w k)) ≤ s →
    e ≤ s ∧ degreeOf none (colAddGen B l j (w K)) ≤ s - e + K
def TwoColumn : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n), l < j → ∀ (a0 s : ℕ)
    (ω : Fin r × Fin n →₀ ℕ) (g : MvPolynomial (Fin r × Fin n) B),
    g ≠ 0 → IsWeightedHomogeneous (pairW l j) g ω → (∀ b : Fin r, b.val < a0 → ω (b, l) = 0) →
    degreeOf none (colAddGen B l j g) ≤ s → InterlacedAt s l j ((colLex r n).degree g)
def LeadInterlaced : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) B),
    f ∈ dualWeyl B r n ν → f ≠ 0 → Interlaced ((colLex r n).degree f)
def StandardMonomialSpanDomain : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (ν : Fin n → ℕ),
    dualWeyl B r n ν = Submodule.span B
      {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ f = bideterminant B sz hsz I}
def ColLexInitMinorOf : Prop := MinorExpLt → ColLexInitMinor
def ColumnLexBideterminantOf : Prop := ColLexInitMinor → ColumnLexBideterminant
def SSYTExistsOf : Prop := SSYTPeel → SSYTExists
def PeelDegBoundOf : Prop := EvalDeg → PeelDegBound
def TwoColumnOf : Prop := PeelDecomp → PeelHomog → PeelLead → PeelDegBound → TwoColumn
def LeadInterlacedOf : Prop := CompDeg → LeadComp → TwoColumn → LeadInterlaced
def SMSAssembly : Prop :=
  ColumnLexBideterminant → ColSums → SSYTExists → LeadInterlaced → StandardMonomialSpanDomain
def StandardMonomialSpanOf : Prop := StandardMonomialSpanDomain → StandardMonomialSpan
example : ((cmIdx 2 3 (1, 2) : Fin (3 * 2)) : ℕ) = 5 := by decide
example : ((cmIdx 3 2 (2, 0) : Fin (2 * 3)) : ℕ) = 2 := by decide
end Formalism.GradedWeylDivisibility


