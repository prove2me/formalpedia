-- Prove2me | Definitions.Def_Submission_PaperStatements
-- name    : Submission_PaperStatements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:46.377071+00:00
-- url     : https://prove2.me/theorems/e2bbcbd2-2833-4236-9016-5640e2b4893b
-- title:
--   Paper Statements
-- statement:
--   Paper statements and supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/PaperStatements.lean

import Definitions.Def_Submission_EndStatement
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit false
section Sec2Definitions
open Finset
namespace ThreeSumApsp
inductive LeftVar : Type
  | x (i : Fin 3)
  | p (i j : Fin 2)
  deriving DecidableEq, Fintype
inductive RightVar : Type
  | y (j : Fin 3)
  | q (i j : Fin 2)
  deriving DecidableEq, Fintype
inductive OutVar : Type
  | z (i j : Fin 3)
  | z0
  deriving DecidableEq, Fintype
inductive Term : Type
  | P (i j : Fin 3)
  | P0
  deriving DecidableEq, Fintype
def xForm (i : Fin 3) : LeftVar → ℤ := Pi.single (LeftVar.x i) 1
def pForm (i j : Fin 2) : LeftVar → ℤ := Pi.single (LeftVar.p i j) 1
def yForm (j : Fin 3) : RightVar → ℤ := Pi.single (RightVar.y j) 1
def qForm (i j : Fin 2) : RightVar → ℤ := Pi.single (RightVar.q i j) 1
def zForm (i j : Fin 3) : OutVar → ℤ := Pi.single (OutVar.z i j) 1
def z0Form : OutVar → ℤ := Pi.single OutVar.z0 1
def pHat : Matrix (Fin 3) (Fin 3) (LeftVar → ℤ) :=
  !![pForm 0 0, pForm 0 1, 0;
     pForm 1 0, pForm 1 1, 0;
     -pForm 0 0 - pForm 1 0, -pForm 0 1 - pForm 1 1, 0]
def qHat : Matrix (Fin 3) (Fin 3) (RightVar → ℤ) :=
  !![qForm 0 0, qForm 0 1, -qForm 0 0 - qForm 0 1;
     qForm 1 0, qForm 1 1, -qForm 1 0 - qForm 1 1;
     0, 0, 0]
def phi : Term → LeftVar → ℤ
  | .P i j => xForm i + pHat i j
  | .P0 => -(xForm 0 + xForm 1 + xForm 2)
def psi : Term → RightVar → ℤ
  | .P i j => yForm j + qHat i j
  | .P0 => yForm 0 + yForm 1 + yForm 2
def chi : Term → OutVar → ℤ
  | .P i j => zForm i j + z0Form
  | .P0 => z0Form
abbrev Var : Type := LeftVar ⊕ RightVar ⊕ OutVar
abbrev TriPoly : Type := MvPolynomial Var ℤ
noncomputable def polyL (s : LeftVar) : TriPoly := MvPolynomial.X (Sum.inl s)
noncomputable def polyR (t : RightVar) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inl t))
noncomputable def polyO (z : OutVar) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inr z))
noncomputable def formL (f : LeftVar → ℤ) : TriPoly := ∑ s, MvPolynomial.C (f s) * polyL s
noncomputable def formR (f : RightVar → ℤ) : TriPoly := ∑ t, MvPolynomial.C (f t) * polyR t
noncomputable def formO (f : OutVar → ℤ) : TriPoly := ∑ z, MvPolynomial.C (f z) * polyO z
noncomputable def G : TriPoly :=
  (∑ i : Fin 3, ∑ j : Fin 3, polyL (.x i) * polyR (.y j) * polyO (.z i j))
    + (∑ i : Fin 2, ∑ j : Fin 2, polyL (.p i j) * polyR (.q i j)) * polyO .z0
noncomputable def E : TriPoly :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (polyL (.x i) * formR (qHat i j) + formL (pHat i j) * polyR (.y j)
      + formL (pHat i j) * formR (qHat i j)) * polyO (.z i j)
def LeftVar.IsInner : LeftVar → Prop
  | .x _ => False
  | .p _ _ => True
def RightVar.IsInner : RightVar → Prop
  | .y _ => False
  | .q _ _ => True
def OutVar.IsInner : OutVar → Prop
  | .z _ _ => False
  | .z0 => True
instance LeftVar.instDecidablePredIsInner : DecidablePred LeftVar.IsInner
  | .x _ => isFalse fun h => h
  | .p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred RightVar.IsInner
  | .y _ => isFalse fun h => h
  | .q _ _ => isTrue trivial
instance OutVar.instDecidablePredIsInner : DecidablePred OutVar.IsInner
  | .z _ _ => isFalse fun h => h
  | .z0 => isTrue trivial
def Term.Contributes (lam : Term) (z : OutVar) : Prop := chi lam z ≠ 0
instance Term.instDecidableContributes (lam : Term) (z : OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (chi lam z ≠ 0))
abbrev LeftStr (L : ℕ) : Type := Fin L → LeftVar
abbrev RightStr (L : ℕ) : Type := Fin L → RightVar
abbrev OutStr (L : ℕ) : Type := Fin L → OutVar
abbrev Vertex (k : ℕ) : Type := Fin k → Term
abbrev Leaf (L : ℕ) : Type := Vertex L
def sliceAt {α β : Type} {L : ℕ} (a : (Fin (L + 1) → α) → β) (s : α) : (Fin L → α) → β :=
  fun u' => a (Fin.cons s u')
def encodeStepL {L : ℕ} (lam : Term) (a : LeftStr (L + 1) → ℤ) : LeftStr L → ℤ :=
  fun u' => ∑ s, phi lam s * sliceAt a s u'
def encodeStepR {L : ℕ} (lam : Term) (b : RightStr (L + 1) → ℤ) : RightStr L → ℤ :=
  fun v' => ∑ t, psi lam t * sliceAt b t v'
def Full.run : (L : ℕ) → (LeftStr L → ℤ) → (RightStr L → ℤ) → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ)
  | 0, a, b => (fun _ => a Fin.elim0 * b Fin.elim0, fun _ => (a Fin.elim0, b Fin.elim0))
  | L + 1, a, b =>
    let R : Term → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ) := fun lam =>
      Full.run L (encodeStepL lam a) (encodeStepR lam b)
    (fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w),
      fun τ => (R (τ 0)).2 (Fin.tail τ))
def Full (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ := (Full.run L a b).1
def Full.multipliedAt (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ × ℤ :=
  (Full.run L a b).2 τ
def Phi {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, phi (τ ℓ) (u ℓ)
def Psi {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ := ∑ v, b v * ∏ ℓ, psi (τ ℓ) (v ℓ)
def Leaf.Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)
instance Leaf.instDecidableContributes {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Decidable (Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))
def Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  fun w => ∑ τ : Leaf L with Leaf.Contributes τ w, Phi τ a * Psi τ b
def gamma (s : LeftVar) (t : RightVar) (z : OutVar) : ℤ :=
  ∑ lam : Term with lam.Contributes z, phi lam s * psi lam t
def innerSetL {L : ℕ} (u : LeftStr L) : Finset (Fin L) := univ.filter fun ℓ => (u ℓ).IsInner
def innerSetR {L : ℕ} (v : RightStr L) : Finset (Fin L) := univ.filter fun ℓ => (v ℓ).IsInner
def innerSetO {L : ℕ} (w : OutStr L) : Finset (Fin L) := univ.filter fun ℓ => (w ℓ).IsInner
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)
def D (m : ℕ) : ℕ := 4 ^ m
def K (L m : ℕ) : ℕ := L.choose m
def LeftVar.outerIndex : LeftVar → Fin 3
  | .x i => i
  | .p _ _ => 0
def LeftVar.innerIndex : LeftVar → Fin 2 × Fin 2
  | .x _ => (0, 0)
  | .p i j => (i, j)
def RightVar.outerIndex : RightVar → Fin 3
  | .y j => j
  | .q _ _ => 0
def RightVar.innerIndex : RightVar → Fin 2 × Fin 2
  | .y _ => (0, 0)
  | .q i j => (i, j)
def OutVar.rowIndex : OutVar → Fin 3
  | .z i _ => i
  | .z0 => 0
def OutVar.colIndex : OutVar → Fin 3
  | .z _ j => j
  | .z0 => 0
abbrev OuterStr (L m : ℕ) : Type := Fin (L - m) → Fin 3
abbrev InnerStr (m : ℕ) : Type := Fin m → Fin 2 × Fin 2
def innerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin m ↪o Fin L :=
  Q.orderEmbOfFin hQ
theorem card_compl_of_card_eq {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Qᶜ.card = L - m := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]
def outerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin (L - m) ↪o Fin L :=
  Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)
def outerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : OuterStr L m :=
  fun k => (u (outerLevel (innerSetL u) h k)).outerIndex
def innerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : InnerStr m :=
  fun k => (u (innerLevel (innerSetL u) h k)).innerIndex
def outerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : OuterStr L m :=
  fun k => (v (outerLevel (innerSetR v) h k)).outerIndex
def innerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : InnerStr m :=
  fun k => (v (innerLevel (innerSetR v) h k)).innerIndex
def rowO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (outerLevel (innerSetO w) h k)).rowIndex
def colO {L m : ℕ} (w : OutStr L) (h : (innerSetO w).card = m) : OuterStr L m :=
  fun k => (w (outerLevel (innerSetO w) h k)).colIndex
abbrev LeftMat (L m : ℕ) : Type := Matrix (OuterStr L m) (InnerStr m) ℤ
abbrev RightMat (L m : ℕ) : Type := Matrix (InnerStr m) (OuterStr L m) ℤ
def arrayL {L : ℕ} (m : ℕ) (X : Finset (Fin L) → LeftMat L m) : LeftStr L → ℤ :=
  fun u =>
    if h : (innerSetL u).card = m then X (innerSetL u) (outerPartL u h) (innerPartL u h) else 0
def arrayR {L : ℕ} (m : ℕ) (Y : Finset (Fin L) → RightMat L m) : RightStr L → ℤ :=
  fun v =>
    if h : (innerSetR v).card = m then Y (innerSetR v) (innerPartR v h) (outerPartR v h) else 0
def M (L m : ℕ) : ℕ := K L m * N0 L m ^ 2
def encodingL {L : ℕ} (a : LeftStr L → ℤ) : Leaf L → ℤ := fun τ => Phi τ a
def encodingR {L : ℕ} (b : RightStr L → ℤ) : Leaf L → ℤ := fun τ => Psi τ b
def sliceSet {n : ℕ} (S : Finset (OutStr (n + 1))) (z : OutVar) : Finset (OutStr n) :=
  univ.filter fun w' => (Fin.cons z w' : OutStr (n + 1)) ∈ S
def childSet {n : ℕ} (S : Finset (OutStr (n + 1))) (lam : Term) : Finset (OutStr n) :=
  (univ.filter fun z => lam.Contributes z).biUnion fun z => sliceSet S z
def restrictTo {n : ℕ} (S : Finset (OutStr n)) (c : OutStr n → ℤ) : OutStr n → ℤ :=
  fun w => if w ∈ S then c w else 0
structure PrunedCall where
  vertex : Σ k, Vertex k
  passed : Σ n, Finset (OutStr n)
def PrunedCall.under (lam : Term) (c : PrunedCall) : PrunedCall where
  vertex := ⟨c.vertex.1 + 1, (Fin.cons lam c.vertex.2 : Vertex (c.vertex.1 + 1))⟩
  passed := c.passed
def Pruned.run : (n : ℕ) → (Leaf n → ℤ) → (Leaf n → ℤ) → Finset (OutStr n) →
    (OutStr n → ℤ) × Multiset PrunedCall
  | 0, encA, encB, S =>
    (restrictTo S fun _ => encA Fin.elim0 * encB Fin.elim0, {⟨⟨0, Fin.elim0⟩, ⟨0, S⟩⟩})
  | n + 1, encA, encB, S =>
    let R : Term → (OutStr n → ℤ) × Multiset PrunedCall := fun lam =>
      if (childSet S lam).Nonempty then
        Pruned.run n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
      else (0, 0)
    (restrictTo S fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w),
      ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ
        univ.val.bind fun lam => ((R lam).2).map (PrunedCall.under lam))
def Pruned (n : ℕ) (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) : OutStr n → ℤ :=
  (Pruned.run n encA encB S).1
def Pruned.calls (n : ℕ) (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) : Multiset PrunedCall :=
  (Pruned.run n encA encB S).2
def Pruned.Visits {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (τ : Leaf L) : Prop :=
  ∃ c ∈ Pruned.calls L encA encB U, c.vertex = ⟨L, τ⟩
def Pruned.totalSize {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) : ℕ :=
  ((Pruned.calls L encA encB U).map fun c => c.passed.2.card).sum
def Leaves {L : ℕ} (U : Finset (OutStr L)) : Finset (Leaf L) :=
  univ.filter fun τ => ∃ w ∈ U, Leaf.Contributes τ w
def OutVar.privateTerm : OutVar → Term
  | .z i j => .P i j
  | .z0 => .P0
def privateLeaf {L : ℕ} (w : OutStr L) : Leaf L := fun ℓ => (w ℓ).privateTerm
def P0Levels {L : ℕ} (τ : Leaf L) : Finset (Fin L) := univ.filter fun ℓ => τ ℓ = Term.P0
def order {L : ℕ} (m : ℕ) (τ : Leaf L) : ℤ := (m : ℤ) - ((P0Levels τ).card : ℤ)
def alpha (m d : ℕ) : ℕ := m.choose d * 9 ^ d
def beta (L m d : ℕ) : ℕ := L.choose (m - d) * 9 ^ (L - m + d)
end ThreeSumApsp
end Sec2Definitions
section Sec2Statements
open Finset
namespace PaperStatements
open ThreeSumApsp
def Eq_1 : Prop :=
  ∀ {R : Type} [Ring R] (a11 a12 a21 a22 b11 b12 b21 b22 : R),
    !![a11, a12; a21, a22] * !![b11, b12; b21, b22] =
      !![(a11 + a22) * (b11 + b22) + a22 * (b21 - b11) - (a11 + a12) * b22
            + (a12 - a22) * (b21 + b22),
         a11 * (b12 - b22) + (a11 + a12) * b22;
         (a21 + a22) * b11 + a22 * (b21 - b11),
         (a11 + a22) * (b11 + b22) - (a21 + a22) * b11 + a11 * (b12 - b22)
            + (a21 - a11) * (b11 + b12)]
def Lemma_6 : Prop :=
  ∑ lam, formL (phi lam) * formR (psi lam) * formO (chi lam) = G + E
def Figure_3 : Prop :=
  ∀ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (u' : LeftStr L),
    encodeStepL (.P 2 0) a u' = sliceAt a (.x 2) u' - sliceAt a (.p 0 0) u' - sliceAt a (.p 1 0) u'
      ∧ encodeStepL .P0 a u'
        = -sliceAt a (.x 0) u' - sliceAt a (.x 1) u' - sliceAt a (.x 2) u'
def Lemma_7 : Prop :=
  ∀ {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ),
    (∀ τ : Leaf L, Full.multipliedAt L a b τ = (Phi τ a, Psi τ b)) ∧ Full L a b = Mult a b
def Lemma_8 : Prop :=
  ∀ {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L),
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)) * a u * b v
def Figure_4 : Prop :=
  innerSetL (![.x 0, .p 0 0, .x 1, .x 2, .p 1 1, .x 0] : LeftStr 6) = {1, 4}
    ∧ innerSetR (![.y 2, .q 0 0, .y 0, .y 2, .q 1 1, .y 1] : RightStr 6) = {1, 4}
    ∧ innerSetO (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6) = {1, 4}
    ∧ ∃ (hu : (innerSetL (![.x 0, .p 0 0, .x 1, .x 2, .p 1 1, .x 0] : LeftStr 6)).card = 2)
        (hv : (innerSetR (![.y 2, .q 0 0, .y 0, .y 2, .q 1 1, .y 1] : RightStr 6)).card = 2)
        (hw : (innerSetO (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6)).card = 2),
        outerPartL _ hu = ![0, 1, 2, 0] ∧ innerPartL _ hu = ![(0, 0), (1, 1)]
          ∧ innerPartR _ hv = ![(0, 0), (1, 1)] ∧ outerPartR _ hv = ![2, 0, 2, 1]
          ∧ rowO _ hw = ![0, 1, 2, 0] ∧ colO _ hw = ![2, 0, 2, 1]
def Lemma_9 : Prop :=
  ∀ {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Y : Finset (Fin L) → RightMat L m)
    (w : OutStr L) (h : (innerSetO w).card = m),
    Mult (arrayL m X) (arrayR m Y) w
      = (X (innerSetO w) * Y (innerSetO w)) (rowO w h) (colO w h)
def Lemma_10 : Prop :=
  ∀ {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (U : Finset (OutStr L)),
    Pruned L (encodingL a) (encodingR b) U = restrictTo U (Mult a b)
      ∧ (0 < L ∨ U.Nonempty →
          ∀ τ : Leaf L, Pruned.Visits (encodingL a) (encodingR b) U τ ↔ τ ∈ Leaves U)
      ∧ Pruned.totalSize (encodingL a) (encodingR b) U ≤ (L + 1) * (Leaves U).card
def Sec2_card_contributing_of_order : Prop :=
  ∀ {L m : ℕ} (w : OutStr L), (innerSetO w).card = m →
  ∀ d : ℕ,
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w ∧ order m τ = d).card = alpha m d
def Sec2_card_outStr_of_leaf : Prop :=
  ∀ {L m : ℕ}, m ≤ L →
  ∀ (d : ℕ) (τ : Leaf L), order m τ = d →
    (univ.filter fun w : OutStr L => (innerSetO w).card = m ∧ Leaf.Contributes τ w).card
      = (L - m + d).choose d
def Eq_5_ratio : Prop :=
  ∀ {L m : ℕ}, m ≤ L →
  ∀ d : ℕ, 1 ≤ d → d ≤ m →
    (beta L m d : ℚ) / (beta L m (d - 1) : ℚ)
      = 9 * ((m : ℚ) - (d : ℚ) + 1) / ((L : ℚ) - (m : ℚ) + (d : ℚ))
def Eq_5_bound : Prop :=
  ∀ m d : ℕ, 1 ≤ d → d ≤ m →
    (beta (19 * m) m d : ℚ) / (beta (19 * m) m (d - 1) : ℚ) ≤ 9 * (m : ℚ) / (18 * (m : ℚ) + 1)
      ∧ 9 * (m : ℚ) / (18 * (m : ℚ) + 1) < 1 / 2
def Eq_5 : Prop :=
  ∀ m d : ℕ, d ≤ m → 2 ^ d * beta (19 * m) m d ≤ M (19 * m) m
def Figure_6 : Prop :=
  privateLeaf (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6)
      = ![.P 0 2, .P0, .P 1 0, .P 2 2, .P0, .P 0 1]
    ∧ alpha 2 0 = 1 ∧ alpha 2 1 = 18 ∧ alpha 2 2 = 81
    ∧ (6 - 2 + 1).choose 1 = 5 ∧ (6 - 2 + 2).choose 2 = 15
def Lemma_11 : Prop :=
  ∀ {L m : ℕ} (U : Finset (OutStr L)), (∀ w ∈ U, (innerSetO w).card = m) →
    (Leaves U).card ≤ ∑ d ∈ range (m + 1), min (U.card * alpha m d) (beta L m d)
      ∧ (L = 19 * m →
          ((Leaves U).card : ℝ)
            ≤ (2 : ℝ) ^ (-(m : ℝ) / 9) * ((2 : ℝ) ^ m * (U.card : ℝ) + 2 * (M L m : ℝ)))
def Eq_6 : Prop :=
  ∀ m N : ℕ, D m ^ 18 ≤ N →
    (10 : ℝ) ^ (19 * m) ≤ (2 : ℝ) ^ (-(m : ℝ) / 9) * (N : ℝ) * (N0 (19 * m) m : ℝ)
end PaperStatements
end Sec2Statements
section Sec3Definitions
namespace ThreeSumApsp
structure LopInstance (n : ℕ) where
  /-- The middle part `M`. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- `adjA a v`: the vertex `a ∈ A` and the middle vertex `v ∈ M` are adjacent. -/
  adjA : Fin n → M → Prop
  /-- `adjB v b`: the middle vertex `v ∈ M` and the vertex `b ∈ B` are adjacent. -/
  adjB : M → Fin n → Prop
  /-- The set `W ⊆ A × B` of edges between `A` and `B`; Section 3.1 calls its elements the query
  pairs. -/
  W : Finset (Fin n × Fin n)
attribute [instance] LopInstance.fintypeM
def LopInstance.MiddleAtMost {n : ℕ} (I : LopInstance n) (D : ℕ) : Prop :=
  Fintype.card I.M ≤ D
def LopInstance.commonNeighbors {n : ℕ} (I : LopInstance n) (a b : Fin n) : Set I.M :=
  {v | I.adjA a v ∧ I.adjB v b}
def LopInstance.InTriangle {n : ℕ} (I : LopInstance n) (a b : Fin n) : Prop :=
  ∃ v : I.M, I.adjA a v ∧ I.adjB v b
noncomputable def LopInstance.numTriangles {n : ℕ} (I : LopInstance n) (a b : Fin n) : ℕ :=
  (I.commonNeighbors a b).ncard
def LopInstance.IsDetectionAnswer {n : ℕ} (I : LopInstance n) (ans : Fin n × Fin n → Bool) : Prop :=
  ∀ q ∈ I.W, (ans q = true ↔ I.InTriangle q.1 q.2)
def LopInstance.ofMatrices {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) : LopInstance n where
  M := Fin D
  adjA a v := X a v = 1
  adjB v b := Y v b = 1
  W := W
def pairIndex {n : ℕ} (q : Fin n × Fin n) : ℕ := q.1.val * n + q.2.val
def rankIn {n : ℕ} (S : Finset (Fin n × Fin n)) (q : Fin n × Fin n) : ℕ :=
  (S.filter fun r => pairIndex r < pairIndex q).card
def chunk {n : ℕ} (S : Finset (Fin n × Fin n)) (cap j : ℕ) : Finset (Fin n × Fin n) :=
  S.filter fun q => rankIn S q / cap = j
noncomputable def numChunks {n : ℕ} (S : Finset (Fin n × Fin n)) (cap : ℕ) : ℕ :=
  ⌈(S.card : ℝ) / (cap : ℝ)⌉₊
noncomputable def queryCap (n D : ℕ) : ℕ := ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊
structure TriangleInstance (R : Type) (n : ℕ) where
  /-- `wAB a b` is the weight `w(a,b)` of the edge between `a ∈ A` and `b ∈ B`. -/
  wAB : Fin n → Fin n → R
  /-- `wBC b c` is the weight `w(b,c)` of the edge between `b ∈ B` and `c ∈ C`. -/
  wBC : Fin n → Fin n → R
  /-- `wAC a c` is the weight `w(a,c)` of the edge between `a ∈ A` and `c ∈ C`. -/
  wAC : Fin n → Fin n → R
namespace TriangleInstance
def S {R : Type} [Add R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) : R :=
  T.wAB a b + T.wBC b c + T.wAC a c
def IsZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) :
    Prop :=
  T.S a b c = 0
def HasZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.IsZeroTriangle a b c
def WeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (T : TriangleInstance R n)
    (U : R) : Prop :=
  (∀ a b, |T.wAB a b| ≤ U) ∧ (∀ b c, |T.wBC b c| ≤ U) ∧ (∀ a c, |T.wAC a c| ≤ U)
def WeightsPolyBounded {n : ℕ} (T : TriangleInstance ℤ n) (κ : ℝ) : Prop :=
  (∀ a b, ((|T.wAB a b| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧ (∀ b c, ((|T.wBC b c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧
    (∀ a c, ((|T.wAC a c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ)
def IsSearchAnswer {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n)
    (r : Option (Fin n × Fin n × Fin n)) : Prop :=
  (∀ a b c, r = some (a, b, c) → T.IsZeroTriangle a b c) ∧ (r = none → ¬ T.HasZeroTriangle)
end TriangleInstance
def GraphHasZeroTriangle {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → Fin n → ℤ) : Prop :=
  ∃ u v x : Fin n, G.Adj u v ∧ G.Adj v x ∧ G.Adj u x ∧ w u v + w v x + w u x = 0
open Classical in
/-- Proof of Theorem 17: the primes "p ∈ [√D/2, √D)", called "the primes in the range". -/
noncomputable def primesInRange (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun p => p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D
namespace TriangleInstance
def countZeroMod {n : ℕ} (T : TriangleInstance ℤ n) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun ((a, b, c) : Fin n × Fin n × Fin n) => T.S a b c ≡ 0 [ZMOD (p : ℤ)]).card
def IsSelectedPrime {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : Prop :=
  p ∈ primesInRange D ∧ ∀ q ∈ primesInRange D, T.countZeroMod p ≤ T.countZeroMod q
end TriangleInstance
noncomputable def sOf (D : ℕ) : ℕ := ⌊Real.sqrt D⌋₊
noncomputable def pieceSize (D g : ℕ) : ℕ := ⌈(sOf D : ℝ) / (g : ℝ)⌉₊
noncomputable def piece (n D g k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c : Fin n => c.val / pieceSize D g = k
noncomputable def numPieces (n D g : ℕ) : ℕ := ⌈(n : ℝ) / (pieceSize D g : ℝ)⌉₊
abbrev InstanceIndex (p : ℕ) : Type := Fin p × ℕ × ℕ
namespace TriangleInstance
def residueClass {n : ℕ} (T : TriangleInstance ℤ n) (p : ℕ) (ϱ : Fin p) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q : Fin n × Fin n => T.wAB q.1 q.2 ≡ ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]
noncomputable def chunkOf {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) (ϱ : Fin p) (j : ℕ) :
    Finset (Fin n × Fin n) :=
  chunk (T.residueClass p ϱ) (queryCap n D) j
noncomputable def lopInstance {n : ℕ} (T : TriangleInstance ℤ n) (D g p : ℕ) :
    InstanceIndex p → LopInstance n
  | (ϱ, j, k) =>
    { M := {c : Fin n // c ∈ piece n D g k} × Fin p
      adjA := fun a (c, σ) => ((σ : ℕ) : ℤ) ≡ T.wAC a c + ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]
      adjB := fun (c, σ) b => ((σ : ℕ) : ℤ) ≡ -T.wBC b c [ZMOD (p : ℤ)]
      W := T.chunkOf D p ϱ j }
noncomputable def instanceIndices {n : ℕ} (T : TriangleInstance ℤ n) (D g p : ℕ) :
    Finset (InstanceIndex p) :=
  Finset.univ.biUnion fun ϱ : Fin p =>
    ((Finset.range (numChunks (T.residueClass p ϱ) (queryCap n D))) ×ˢ
      (Finset.range (numPieces n D g))).image fun jk => (ϱ, jk)
noncomputable def scanPiece {n : ℕ} (T : TriangleInstance ℤ n) (D g k : ℕ) (a b : Fin n) :
    Option (Fin n) :=
  ((List.finRange n).filter fun c => c ∈ piece n D g k).find? fun c => T.S a b c = 0
noncomputable def acceptedPairs {n : ℕ} (T : TriangleInstance ℤ n) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) : Finset (InstanceIndex p × (Fin n × Fin n)) :=
  ((T.instanceIndices D g p) ×ˢ Finset.univ).filter fun (ι, q) =>
    q ∈ (T.lopInstance D g p ι).W ∧ ans ι q = true
noncomputable def runScans {n : ℕ} (T : TriangleInstance ℤ n) (D g : ℕ) {p : ℕ} :
    List (InstanceIndex p × (Fin n × Fin n)) → Option (Fin n × Fin n × Fin n) × ℕ
  | [] => (none, 0)
  | ((_, _, k), a, b) :: rest =>
    match T.scanPiece D g k a b with
    | some c => (some (a, b, c), 1)
    | none => ((runScans T D g rest).1, (runScans T D g rest).2 + 1)
def IsScanOrder {n : ℕ} (T : TriangleInstance ℤ n) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) (L : List (InstanceIndex p × (Fin n × Fin n))) :
    Prop :=
  L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ T.acceptedPairs D g p ans
end TriangleInstance
abbrev ThreeSum {n : ℕ} (x : Fin n → ℤ) : Prop := EndStatement.ThreeSum.yes x
def Convolution3SUM {R : Type} [Add R] {N : ℕ} (x : Fin N → R) : Prop :=
  ∃ (i j : Fin N) (h : i.val + j.val < N), x i + x j = x ⟨i.val + j.val, h⟩
def TriangleInstance.HasNegativeTriangle {R : Type} [Add R] [Zero R] [LT R] {n : ℕ}
    (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.S a b c < 0
def IsMinPlusProduct {R : Type} [Add R] [LE R] {n m l : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin m) (Fin l) R) (C : Matrix (Fin n) (Fin l) R) : Prop :=
  ∀ i j, (∃ k, C i j = A i k + B k j) ∧ ∀ k, C i j ≤ A i k + B k j
def minPlus {R : Type} [Add R] [LinearOrder R] {n m l : ℕ} (A : Matrix (Fin n) (Fin m) (WithTop R))
    (B : Matrix (Fin m) (Fin l) (WithTop R)) : Matrix (Fin n) (Fin l) (WithTop R) :=
  Matrix.of fun i j => Finset.univ.inf fun k => A i k + B k j
def walkEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | i, [] => i
  | _, j :: rest => walkEnd j rest
def walkWeight {R : Type} [Add R] [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Fin n → List (Fin n) → WithTop R
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest
def NoNegativeCycle {R : Type} [Add R] [Zero R] [LE R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Prop :=
  ∀ (i : Fin n) (rest : List (Fin n)), walkEnd i rest = i → 0 ≤ walkWeight w i rest
def IsDistanceMatrix {R : Type} [Add R] [Zero R] [Preorder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (d : Fin n → Fin n → WithTop R) : Prop :=
  ∀ i j, IsLeast {x | ∃ rest : List (Fin n), walkEnd i rest = j ∧ walkWeight w i rest = x} (d i j)
def EdgeWeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (w : Fin n → Fin n → WithTop R)
    (U : R) : Prop :=
  ∀ (i j : Fin n) (x : R), w i j = (x : WithTop R) → |x| ≤ U
def weightMatrix {R : Type} [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Matrix (Fin n) (Fin n) (WithTop R) :=
  Matrix.of fun i j => if i = j then 0 else w i j
def minPlusSquares {R : Type} [Add R] [Zero R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) : ℕ → Matrix (Fin n) (Fin n) (WithTop R)
  | 0 => weightMatrix w
  | t + 1 => minPlus (minPlusSquares w t) (minPlusSquares w t)
def TriangleInstance.mapWeights {n : ℕ} (T : TriangleInstance ℤ n) :
    (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ) → TriangleInstance ℤ n
  | (fAB, fBC, fAC) =>
    { wAB := fun a b => fAB (T.wAB a b)
      wBC := fun b c => fBC (T.wBC b c)
      wAC := fun a c => fAC (T.wAC a c) }
structure TriangleTemplate (t N : ℕ) where
  /-- The source of `w(a,b)`. -/
  eAB : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(b,c)`. -/
  eBC : Fin t → Fin t → Option (Bool × Fin N)
  /-- The source of `w(a,c)`. -/
  eAC : Fin t → Fin t → Option (Bool × Fin N)
def templateWeight {N : ℕ} (x : Fin N → ℤ) (fill : ℤ) : Option (Bool × Fin N) → ℤ
  | none => fill
  | some (false, i) => x i
  | some (true, i) => -x i
def TriangleTemplate.instantiate {t N : ℕ} (τ : TriangleTemplate t N) (x : Fin N → ℤ) (fill : ℤ) :
    TriangleInstance ℤ t where
  wAB a b := templateWeight x fill (τ.eAB a b)
  wBC b c := templateWeight x fill (τ.eBC b c)
  wAC a c := templateWeight x fill (τ.eAC a c)
def IsPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in Filter.atTop, |f n| ≤ (n : ℝ) ^ (a + ε n)
def IsPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ e : ℕ, Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e
def IsBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a
end ThreeSumApsp
end Sec3Definitions
section ChanHeDefinitions
namespace ThreeSumApsp
namespace ChanHe
open Finset
def coll (S : Finset ℤ) (M : ℕ) : ℕ := #{p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}
def heavy (S : Finset ℤ) (M : ℕ) : Finset ℤ := {x ∈ S | ∃ y ∈ S, y ≠ x ∧ (M : ℤ) ∣ x - y}
def bucket (S : Finset ℤ) (M : ℕ) (r : ℤ) : Finset ℤ := {x ∈ S | x % (M : ℤ) = r}
def arr (S : Finset ℤ) (M : ℕ) (pad : ℤ) (i : ℕ) : ℤ :=
  if #(bucket S M i) = 1 then ∑ x ∈ bucket S M i, x else pad
def pad (U : ℕ) : ℤ := 2 * U + 1
def arrXY (S : Finset ℤ) (M U : ℕ) : ℕ → ℤ := arr S M (pad U)
def arrZ (S : Finset ℤ) (M U : ℕ) (k : ℕ) : ℤ :=
  if k < 2 * M then arr (S.image fun c => -c) M (-pad U) (k % M) else -pad U
def pick (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.min' h else 1
def firstP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  pick {p ∈ Q | coll S₁ p * #Q ≤ 3 * Λ * #S₁ ^ 2 ∧ coll S₂ p * #Q ≤ 3 * Λ * #S₂ ^ 2 ∧
    coll S₃ p * #Q ≤ 3 * Λ * #S₃ ^ 2}
def secondP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) (p : ℕ) : ℕ :=
  pick {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Λ * coll S₁ p ∧
    coll S₂ (p * q) * #Q ≤ 3 * Λ * coll S₂ p ∧ coll S₃ (p * q) * #Q ≤ 3 * Λ * coll S₃ p}
def modulus (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  firstP Q Λ S₁ S₂ S₃ * secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃)
structure Node where
  /-- The first set. -/
  S₁ : Finset ℤ
  /-- The second set. -/
  S₂ : Finset ℤ
  /-- The third set. -/
  S₃ : Finset ℤ
  /-- The modulus. -/
  M : ℕ
def nodes (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → List Node
  | 0, _, _, _ => []
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then [] else
      let M := modulus Q Λ S₁ S₂ S₃
      ⟨S₁, S₂, S₃, M⟩ ::
        (nodes Q Λ f (heavy S₁ M) S₂ S₃ ++ nodes Q Λ f S₁ (heavy S₂ M) S₃ ++
          nodes Q Λ f S₁ S₂ (heavy S₃ M))
def Lam (U : ℕ) : ℕ := Nat.log 2 (2 * U) + 1
def height (n : ℕ) : ℕ := Nat.clog 2 (Nat.log 2 n + 2)
def fuel (n : ℕ) : ℕ := 3 * height n - 2
def wPar (n U : ℕ) : ℕ := 5 * Lam U * (Nat.sqrt n + 1)
def mPar (n U : ℕ) : ℕ := (wPar n U + 1) * (2 * Nat.log 2 (wPar n U + 1) + 4)
def reduction (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : List Node :=
  nodes (Nat.primesLE (mPar n U)) (Lam U) (fuel n) S₁ S₂ S₃
def lab (U : ℕ) (x : ℤ) : ℕ := (x + U).toNat
def splitA (U β : ℕ) (v : Bool) (S : Finset ℤ) : Finset ℤ := {x ∈ S | (lab U x).testBit β = v}
def splitB (U β β' : ℕ) (v w : Bool) (S : Finset ℤ) : Finset ℤ :=
  {x ∈ S | (lab U x).testBit β = !v ∧ (lab U x).testBit β' = w}
def twiceSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ :=
  ({a ∈ univ.image x | a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a}}).image fun a => 2 * a
def zeroSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ := if 3 ≤ #{i : Fin n | x i = 0} then {0} else ∅
def oneArray (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) : ℤ :=
  let G : ℤ := 3 * W + 1
  if u % 4 = 1 then X (u / 4) + G else if u % 4 = 2 then Y (u / 4) + 3 * G
  else if u % 4 = 3 then Z (u / 4) + 4 * G else 10 * G
def Node.oneArray (ν : Node) (U : ℕ) : ℕ → ℤ :=
  ChanHe.oneArray (2 * U + 1) (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)
def allNodes (n U : ℕ) (x : Fin n → ℤ) : List Node :=
  ((List.range (Lam (2 * U))).flatMap fun β => (List.range (Lam (2 * U))).flatMap fun β' =>
    [false, true].flatMap fun v =>
      reduction n (2 * U) (splitA (2 * U) β v (univ.image x))
        (splitB (2 * U) β β' v false (univ.image x))
        (splitB (2 * U) β β' v true (univ.image x))) ++
  (reduction n (2 * U) (twiceSet x) {0} (univ.image x) ++ reduction n (2 * U) (zeroSet x) {0} {0})
def instances (n U : ℕ) (x : Fin n → ℤ) : List (ℕ → ℤ) :=
  (allNodes n U x).map fun ν => ν.oneArray (2 * U)
def scanPairs (n U : ℕ) (x : Fin n → ℤ) : ℕ :=
  ((allNodes n U x).map fun ν => 2 * #(Nat.primesLE (mPar n (2 * U))) * (#ν.S₁ + #ν.S₂ + #ν.S₃)).sum
def lenOf (κ n : ℕ) : ℕ := 8 * mPar n (2 * n ^ κ) ^ 2
def numBound (κ n : ℕ) : ℕ := 128 * (κ + 2) ^ 2 * (Nat.log 2 n + 1) ^ 7
def workBound (κ n : ℕ) : ℕ := numBound κ n * (2 * mPar n (2 * n ^ κ) * (3 * n))
end ChanHe
end ThreeSumApsp
end ChanHeDefinitions
section Sec3Statements
namespace PaperStatements
open ThreeSumApsp
def Theorem_17_hashing_sum_sq_le : Prop :=
  ∀ D : ℕ, 16 ≤ D →
    ((∑ p ∈ primesInRange D, p ^ 2 : ℕ) : ℝ) ≤ (D : ℝ) ^ (3 / 2 : ℝ)
def Theorem_17_write_cost : Prop :=
  ∀ {n D g p : ℕ}, 16 ≤ D → D ≤ n → 1 ≤ g →
  ∀ T : TriangleInstance ℤ n, p ∈ primesInRange D →
    ((T.instanceIndices D g p).card : ℝ) * (2 * (n : ℝ) * (D : ℝ))
      ≤ 8 * ((n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ))
def Theorem_17_scanOrder_exists : Prop :=
  ∀ {n D g p : ℕ} (T : TriangleInstance ℤ n)
    (ans : InstanceIndex p → Fin n × Fin n → Bool), ∃ L, T.IsScanOrder D g p ans L
def Theorem_17 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {n D g : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ g → (g : ℝ) ≤ Real.sqrt D → 1 ≤ κ →
  ∀ T : TriangleInstance ℤ n, T.WeightsPolyBounded κ →
  (∃ p, T.IsSelectedPrime D p) ∧
  ∀ p, T.IsSelectedPrime D p →
    ((T.instanceIndices D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) ∧
    (∀ ι ∈ T.instanceIndices D g p, (T.lopInstance D g p ι).MiddleAtMost D ∧
      ((T.lopInstance D g p ι).W.card : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D) ∧
    ∀ ans : InstanceIndex p → Fin n × Fin n → Bool,
      (∀ ι ∈ T.instanceIndices D g p, (T.lopInstance D g p ι).IsDetectionAnswer (ans ι)) →
      ∀ L : List (InstanceIndex p × (Fin n × Fin n)), T.IsScanOrder D g p ans L →
        T.IsSearchAnswer (T.runScans D g L).1 ∧
        ((T.runScans D g L).2 : ℝ) * (pieceSize D g : ℝ)
          ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ))
def Remark_18_block : Prop :=
  ∀ {n D g p : ℕ} (T : TriangleInstance ℤ n) (ϱ : Fin p) (i k : ℕ)
    (c : {c : Fin n // c ∈ piece n D g k}) (σ : Fin p) (j : ℤ),
  ((σ : ℕ) : ℤ) ≡ -j [ZMOD (p : ℤ)] →
    (∀ a, (T.lopInstance D g p (ϱ, i, k)).adjA a (c, σ) ↔
      T.wAC a c ≡ -((ϱ : ℕ) : ℤ) - j [ZMOD (p : ℤ)]) ∧
    (∀ b, (T.lopInstance D g p (ϱ, i, k)).adjB (c, σ) b ↔ T.wBC b c ≡ j [ZMOD (p : ℤ)]) ∧
    (∀ q ∈ (T.lopInstance D g p (ϱ, i, k)).W, T.wAB q.1 q.2 ≡ ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)])
def Remark_20_balance : Prop :=
  ∀ (γ η : ℝ),
    -(γ / 2) ≤ max (η - γ) (-η) ∧ (max (η - γ) (-η) = -(γ / 2) ↔ η = γ / 2)
def Remark_20_brute_force : Prop :=
  ∀ {n D g : ℕ}, 16 ≤ D → 1 ≤ g → (g : ℝ) ≤ Real.sqrt D →
    (n : ℝ) ^ 2 / Real.sqrt D * (pieceSize D g : ℝ) ≤ 2 * (n : ℝ) ^ 2 / (g : ℝ) ∧
    4 * (n : ℝ) * (g : ℝ) * (2 * (n : ℝ) ^ 2 / (g : ℝ)) = 8 * (n : ℝ) ^ 3
def Theorem_21b_repeated_squaring : Prop :=
  ∀ {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R),
  NoNegativeCycle w →
    IsDistanceMatrix w (minPlusSquares w (Nat.clog 2 n))
def Theorem_21b_entries_bounded : Prop :=
  ∀ {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R),
  NoNegativeCycle w →
  ∀ U : R, 0 ≤ U → EdgeWeightsBoundedBy w U →
  ∀ (t : ℕ) (i j : Fin n) (x : R), minPlusSquares w t i j = (x : WithTop R) →
    |x| ≤ n • U
def Theorem_21b_log_factors : Prop :=
  ∀ {n : ℕ} {κ c τ τ' : ℝ}, 2 ≤ n → 0 ≤ κ → 0 ≤ τ → τ' ≤ c * (τ * Real.log ((n : ℝ) ^ (κ + 1))) →
    (n : ℝ) ^ 2 * τ' * Real.log ((n : ℝ) ^ (κ + 1))
      ≤ c * ((n : ℝ) ^ 2 * τ * Real.log ((n : ℝ) ^ (κ + 1)) ^ 2) ∧
    (Nat.clog 2 n : ℝ) * ((n : ℝ) ^ 2 * τ * Real.log ((n : ℝ) ^ (κ + 1)) ^ 2)
      ≤ 3 * (κ + 1) ^ 2 * ((n : ℝ) ^ 2 * τ * Real.log n ^ 3)
def Theorem_21b_negative_to_exact : Prop :=
  ∀ U : ℕ, 1 ≤ U →
    ∃ L : List ((ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ)),
      L.length ≤ 2 * Nat.log 2 U + 6 ∧
      (∀ fAB fBC fAC, (fAB, fBC, fAC) ∈ L → ∀ x : ℤ, |x| ≤ (U : ℤ) →
        |fAB x| ≤ 6 * (U : ℤ) ∧ |fBC x| ≤ 6 * (U : ℤ) ∧ |fAC x| ≤ 6 * (U : ℤ)) ∧
      ∀ (n : ℕ) (T : TriangleInstance ℤ n), T.WeightsBoundedBy (U : ℤ) →
        (T.HasNegativeTriangle ↔ ∃ f ∈ L, (T.mapWeights f).HasZeroTriangle)
def Theorem_21a_convolution_to_exact : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∃ (t : ℕ) (L : List (TriangleTemplate t N)),
      (t : ℝ) ≤ Real.sqrt N + 1 ∧
      L.length ≤ 2 * t ∧
      ∀ (x : Fin N → ℤ) (U : ℤ), (∀ i, |x i| ≤ U) →
        (Convolution3SUM x ↔ ∃ τ ∈ L, (τ.instantiate x (2 * U + 1)).HasZeroTriangle)
def Theorem_21a_compose : Prop :=
  ∀ {E₁ Num₁ E₂ Num₂ : ℕ → ℝ} {N size₂ : ℕ → ℕ}, IsPowPolylog E₁ (3 / 2) → IsPowPolylog Num₁ 0 →
  IsPowPolylog (fun n => (N n : ℝ)) 1 → IsPowLittleO E₂ (3 / 2) → IsBigOPow Num₂ (1 / 2) →
  IsBigOPow (fun m => (size₂ m : ℝ)) (1 / 2) →
    IsPowLittleO (fun n => Num₁ n * Num₂ (N n)) (1 / 2) ∧
    IsPowLittleO (fun n => (size₂ (N n) : ℝ)) (1 / 2) ∧
    IsPowLittleO (fun n => E₁ n + Num₁ n * E₂ (N n)) (3 / 2)
section ChanHe
open Finset
def Theorem_21a_threeSum_to_convolution : Prop :=
  ∀ (κ : ℕ),
    IsPowPolylog (fun n => (ChanHe.numBound κ n : ℝ)) 0 ∧
    IsPowPolylog (fun n => (ChanHe.lenOf κ n : ℝ)) 1 ∧
    IsPowPolylog (fun n => (ChanHe.workBound κ n : ℝ)) (3 / 2) ∧
    ∀ (n : ℕ) (x : Fin n → ℤ), 2 ≤ n → (∀ i, |x i| ≤ (n : ℤ) ^ κ) →
      (ChanHe.instances n (n ^ κ) x).length ≤ ChanHe.numBound κ n ∧
      ChanHe.scanPairs n (n ^ κ) x ≤ ChanHe.workBound κ n ∧
      (∀ y ∈ ChanHe.instances n (n ^ κ) x, ∀ u < ChanHe.lenOf κ n,
        |y u| ≤ 120 * (n : ℤ) ^ κ + 40) ∧
      (ThreeSum x ↔
        ∃ y ∈ ChanHe.instances n (n ^ κ) x,
          Convolution3SUM fun i : Fin (ChanHe.lenOf κ n) => y i)
def Theorem_21a_threeSum_to_exact : Prop :=
  ∀ κ n : ℕ, 2 ≤ n →
    ∃ (t : ℕ) (L : List (TriangleTemplate t (ChanHe.lenOf κ n))),
      (t : ℝ) ≤ Real.sqrt (ChanHe.lenOf κ n) + 1 ∧
      L.length ≤ 2 * t ∧
      ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ (n : ℤ) ^ κ) →
        (ChanHe.instances n (n ^ κ) x).length ≤ ChanHe.numBound κ n ∧
        (∀ y ∈ ChanHe.instances n (n ^ κ) x, ∀ τ ∈ L,
          (τ.instantiate (fun i : Fin (ChanHe.lenOf κ n) => y i)
            (240 * (n : ℤ) ^ κ + 81)).WeightsBoundedBy (240 * (n : ℤ) ^ κ + 81)) ∧
        (ThreeSum x ↔ ∃ y ∈ ChanHe.instances n (n ^ κ) x, ∃ τ ∈ L,
          (τ.instantiate (fun i : Fin (ChanHe.lenOf κ n) => y i)
            (240 * (n : ℤ) ^ κ + 81)).HasZeroTriangle)
end ChanHe
end PaperStatements
end Sec3Statements
section Sec4Definitions
open Finset
namespace ThreeSumApsp
def productAt {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ := Phi τ a * Psi τ b
inductive CubeSymbol : Type
  | term (lam : Term)
  | star
  deriving DecidableEq, Fintype
abbrev Cube (L : ℕ) : Type := Fin L → CubeSymbol
def Cube.HasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) : Prop :=
  ∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)
instance Cube.instDecidableHasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) :
    Decidable (Cube.HasLeaf π τ) :=
  inferInstanceAs (Decidable (∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)))
def Cube.leaves {L : ℕ} (π : Cube L) : Finset (Leaf L) := univ.filter fun τ => Cube.HasLeaf π τ
def Cube.starLevels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.star
def Cube.P0Levels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.term Term.P0
def Cube.val {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L) : ℤ :=
  ∑ τ ∈ Cube.leaves π, productAt a b τ
def IsBox {L : ℕ} (m t : ℕ) (π : Cube L) : Prop :=
  (Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'
instance IsBox.instDecidable {L : ℕ} (m t : ℕ) (π : Cube L) : Decidable (IsBox m t π) :=
  inferInstanceAs (Decidable ((Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'))
def lowest {L : ℕ} (k : ℕ) (S : Finset (Fin L)) : Finset (Fin L) :=
  S.filter fun ℓ => (S.filter fun ℓ' => ℓ' < ℓ).card < k
def Cube.starsToP0 {L : ℕ} (π : Cube L) : Leaf L :=
  fun ℓ =>
    match π ℓ with
    | .term lam => lam
    | .star => Term.P0
def Vof {L : ℕ} (m t : ℕ) (Q Z : Finset (Fin L)) : Finset (Fin L) :=
  Z ∪ lowest (m - t - Z.card) (Q \ Z)
def FV {L : ℕ} (Q V : Finset (Fin L)) : Finset (Fin L) := Q.filter fun ℓ => ∀ ℓ' ∈ Q \ V, ℓ < ℓ'
def BV {L : ℕ} (η : OutStr L) (V : Finset (Fin L)) : Finset (Cube L) :=
  univ.filter fun π => ∀ ℓ,
    (ℓ ∈ FV (innerSetO η) V → π ℓ = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → π ℓ = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, π ℓ = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → π ℓ = CubeSymbol.term (privateLeaf η ℓ))
def Vsets {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Finset (Fin L)) :=
  (innerSetO η).powersetCard (m - t)
def lowLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ < (t : ℤ)
def querySum {L : ℕ} (m t : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, productAt a b τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, Cube.val a b π
def boxes (L m t : ℕ) : Finset (Cube L) := univ.filter fun π => IsBox m t π
def boxesWithStars (L m t e : ℕ) : Finset (Cube L) :=
  (boxes L m t).filter fun π => (Cube.starLevels π).card = e
def Cube.replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) : Cube L :=
  Function.update π ℓ (CubeSymbol.term lam)
def dpValue {L : ℕ} (encA encB : Leaf L → ℤ) : ℕ → Cube L → ℤ
  | 0, π => encA (Cube.starsToP0 π) * encB (Cube.starsToP0 π)
  | e + 1, π =>
    if h : (Cube.starLevels π).Nonempty then
      ∑ lam : Term, dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)
    else 0
noncomputable def rho (L m : ℕ) : ℝ := 9 * (m : ℝ) / ((L : ℝ) - (m : ℝ) + 1)
noncomputable def cost8 (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2
    + (N : ℝ) * (10 : ℝ) ^ L / (Real.sqrt (K L m : ℝ) * (N0 L m : ℝ))
noncomputable def costQuery (L m t : ℕ) : ℝ := (L : ℝ) * ∑ d ∈ range (t + 1), (alpha m d : ℝ)
noncomputable def cost9 (L m t N W : ℕ) : ℝ :=
  (L : ℝ) * (W : ℝ) * ∑ d ∈ range (t + 1), (alpha m d : ℝ) + cost8 L m t N
def padInnerCols {N D₀ : ℕ} (D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) : Matrix (Fin N) (Fin D') ℤ :=
  fun I k => if h : (k : ℕ) < D₀ then X I ⟨k, h⟩ else 0
def padInnerRows {N D₀ : ℕ} (D' : ℕ) (Y : Matrix (Fin D₀) (Fin N) ℤ) : Matrix (Fin D') (Fin N) ℤ :=
  fun k J => if h : (k : ℕ) < D₀ then Y ⟨k, h⟩ J else 0
noncomputable def entropy (θ : ℝ) : ℝ := -θ * Real.log θ - (1 - θ) * Real.log (1 - θ)
noncomputable def lnΛ (c γ : ℝ) : ℝ :=
  c * Real.log 10 - (1 / 2) * c * entropy (1 / c) - (c - 1) * Real.log 3 + γ * Real.log 4
noncomputable def Rc (c γ : ℝ) : ℝ := Real.log 4 / lnΛ c γ
noncomputable def epsStar : ℝ := Real.log 4 / (5 * Real.log 10)
noncomputable def rhoC (c : ℝ) : ℝ := 9 / (c - 1)
noncomputable def gammaOf (c θ : ℝ) : ℝ := θ * Real.log (1 / rhoC c) / Real.log 4
noncomputable def qOf (θ : ℝ) : ℝ := (entropy θ + θ * Real.log 9) / Real.log 4
noncomputable def levelsOf (c : ℝ) (m : ℕ) : ℕ := ⌈c * (m : ℝ)⌉₊
def ValidQueryEntry (c ε q γ₀ : ℝ) : Prop :=
  10 < c ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ ε < Rc c (gammaOf c θ) ∧ qOf θ ≤ q ∧ γ₀ ≤ gammaOf c θ
def ValidDensityEntry (c ε κ γ₀ : ℝ) : Prop :=
  10 < c ∧ 0 < κ ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ ε < Rc c (gammaOf c θ) ∧
    γ₀ ≤ min (gammaOf c θ) (κ - qOf θ)
def Table2Query (c ε q γ₀ : ℝ) : Prop :=
  10 < c ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ qOf θ = q ∧
    γ₀ ≤ gammaOf c θ ∧ gammaOf c θ < γ₀ + 0.0001 ∧ ε < Rc c (gammaOf c θ)
def Table2Ninth (c ε γ₀ : ℝ) : Prop :=
  10 < c ∧ γ₀ ≤ gammaOf c (1 / 9) ∧ gammaOf c (1 / 9) < γ₀ + 0.0001 ∧ ε < Rc c (gammaOf c (1 / 9))
def Table2Density (c ε κ γ₀ : ℝ) : Prop :=
  10 < c ∧ 0 < κ ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ gammaOf c θ = κ - qOf θ ∧
    γ₀ ≤ gammaOf c θ ∧ gammaOf c θ < γ₀ + 0.0001 ∧ ε < Rc c (gammaOf c θ)
structure Table2Row (c ε γq010 γq025 γq043 γq050 γq075 γq090 γk010 γk025 γk050 γk075 γk100 : ℝ) :
    Prop where
  q010 : Table2Query c ε 0.10 γq010
  q025 : Table2Query c ε 0.25 γq025
  /-- The entry of the column `q = 0.43`, which uses `θ = 1/9`. -/
  q043 : Table2Ninth c ε γq043
  q050 : Table2Query c ε 0.50 γq050
  q075 : Table2Query c ε 0.75 γq075
  q090 : Table2Query c ε 0.90 γq090
  k010 : Table2Density c ε 0.10 γk010
  k025 : Table2Density c ε 0.25 γk025
  k050 : Table2Density c ε 0.50 γk050
  k075 : Table2Density c ε 0.75 γk075
  k100 : Table2Density c ε 1.00 γk100
  /-- Section 4.4: "The ε of a row of the table is the smallest R_c(γ) over its entries." The
  caption: "We round all values down". The fields above give `ε < R_c(γ)` at every entry; this field
  gives the other half, that the smallest `R_c(γ)` of the row is below `ε + 0.001`, by exhibiting
  the entry of the column `q = 0.90` (which need not be the smallest: in the rows `c = 15, 12, 10.5`
  the smallest is in the column `κ = 1.00`). -/
  eps : ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ qOf θ = 0.90 ∧ Rc c (gammaOf c θ) < ε + 0.001
end ThreeSumApsp
end Sec4Definitions
section Sec4Statements
open Finset
namespace PaperStatements
open ThreeSumApsp
def Lemma_27 : Prop :=
  ∀ {L : ℕ} (m t : ℕ), t ≤ m →
  ∀ Q Z : Finset (Fin L), Q.card = m → Z ⊆ Q → Z.card ≤ m - t →
  ∀ V : Finset (Fin L),
    (V ⊆ Q ∧ V.card = m - t ∧ V \ FV Q V ⊆ Z ∧ Z ⊆ V) ↔ V = Vof m t Q Z
def Lemma_28_leaves : Prop :=
  ∀ {L : ℕ} (m t : ℕ), t ≤ m →
  ∀ η : OutStr L, (innerSetO η).card = m →
  ∀ τ : Leaf L,
    (Leaf.Contributes τ η ∧ (t : ℤ) ≤ order m τ) ↔
      ∃ π ∈ (Vsets m t η).biUnion (BV η), τ ∈ Cube.leaves π
def Lemma_28_unique : Prop :=
  ∀ {L : ℕ} (m t : ℕ), t ≤ m →
  ∀ η : OutStr L, (innerSetO η).card = m →
  ∀ τ : Leaf L, Leaf.Contributes τ η → (t : ℤ) ≤ order m τ →
    ∃! π : Cube L, π ∈ (Vsets m t η).biUnion (BV η) ∧ τ ∈ Cube.leaves π
def Lemma_28 : Prop :=
  ∀ {L : ℕ} (m t : ℕ), t ≤ m →
  ∀ (X : Finset (Fin L) → LeftMat L m) (Y : Finset (Fin L) → RightMat L m) (η : OutStr L)
    (hη : (innerSetO η).card = m),
    (X (innerSetO η) * Y (innerSetO η)) (rowO η hη) (colO η hη) =
      querySum m t (arrayL m X) (arrayR m Y) η
def Lemma_28_counts : Prop :=
  ∀ {L : ℕ} (m t : ℕ), t ≤ m →
  ∀ η : OutStr L, (innerSetO η).card = m →
    (lowLeaves m t η).card = ∑ d ∈ range t, alpha m d ∧
      ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t ∧
      ((Vsets m t η).biUnion (BV η)).card = alpha m t
def Lemma_28_boxes : Prop :=
  ∀ {L : ℕ} (m t : ℕ) (η : OutStr L) (V : Finset (Fin L)), V ∈ Vsets m t η →
  ∀ π : Cube L, π ∈ BV η V →
    π ∈ boxesWithStars L m t (FV (innerSetO η) V).card
def Figure_10_counts : Prop :=
  6 * 81 = 486 ∧ alpha 4 2 = 486 ∧ alpha 4 2 + alpha 4 3 + alpha 4 4 = 9963
def Figure_10_rows : Prop :=
  FV (univ : Finset (Fin 4)) {0, 1} = {0, 1} ∧
    FV (univ : Finset (Fin 4)) {0, 2} = {0} ∧
    FV (univ : Finset (Fin 4)) {0, 3} = {0} ∧
    FV (univ : Finset (Fin 4)) {1, 2} = ∅ ∧
    FV (univ : Finset (Fin 4)) {1, 3} = ∅ ∧
    FV (univ : Finset (Fin 4)) {2, 3} = ∅ ∧
    81 * (10 ^ 2 + 10 + 10 + 1 + 1 + 1) = 9963
def Figure_10_Vof : Prop :=
  Vof 4 2 (univ : Finset (Fin 4)) ∅ = {0, 1} ∧
    Vof 4 2 (univ : Finset (Fin 4)) {0} = {0, 1} ∧
    Vof 4 2 (univ : Finset (Fin 4)) {1} = {0, 1} ∧
    Vof 4 2 (univ : Finset (Fin 4)) {2} = {0, 2} ∧
    Vof 4 2 (univ : Finset (Fin 4)) {3} = {0, 3}
def Lemma_29_count : Prop :=
  ∀ L m t : ℕ, 10 * m ≤ L → t ≤ m →
    (boxes L m t).card ≤ (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d
def Lemma_29_values : Prop :=
  ∀ (L m t e : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L),
  π ∈ boxesWithStars L m t e →
    dpValue (encodingL a) (encodingR b) e π = Cube.val a b π
def Lemma_29_split : Prop :=
  ∀ {L m t e : ℕ} {π : Cube L}, π ∈ boxesWithStars L m t (e + 1) →
  ∀ (hne : (Cube.starLevels π).Nonempty) (lam : Term),
    Cube.replace π ((Cube.starLevels π).max' hne) lam ∈ boxesWithStars L m t e
def Sec4_rho_lt_one : Prop :=
  ∀ L m : ℕ, 10 * m ≤ L → rho L m < 1
def Eq_7_ratio : Prop :=
  ∀ L m d : ℕ, 10 * m ≤ L → 1 ≤ d → d ≤ m →
    (beta L m d : ℝ) / (beta L m (d - 1) : ℝ)
        = 9 * ((m : ℝ) - (d : ℝ) + 1) / ((L : ℝ) - (m : ℝ) + (d : ℝ)) ∧
      9 * ((m : ℝ) - (d : ℝ) + 1) / ((L : ℝ) - (m : ℝ) + (d : ℝ)) ≤ rho L m
def Eq_7 : Prop :=
  ∀ L m d : ℕ, 10 * m ≤ L → d ≤ m →
    (beta L m d : ℝ) ≤ rho L m ^ d * (M L m : ℝ)
def Eq_10_corollary_26 : Prop :=
  ∀ m N : ℕ, 60 ≤ m → 4 ^ (18 * (m - 1)) ≤ N →
    (D m : ℝ) ^ (Real.log (20 / 9) / (9 * Real.log 4)) * (10 : ℝ) ^ (21 * m)
        / (Real.sqrt (K (21 * m) m) * (N0 (21 * m) m : ℝ))
      ≤ (N : ℝ)
def Eq_10 : Prop :=
  ∀ c θ ε : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → D₀ ≤ D m → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
        (D m : ℝ) ^ gammaOf c θ * (10 : ℝ) ^ levelsOf c m
            / (Real.sqrt (K (levelsOf c m) m) * (N0 (levelsOf c m) m : ℝ))
          ≤ (N : ℝ)
def Eq_11_iff : Prop :=
  ∀ c γ ε : ℝ, 10 ≤ c → 0 ≤ γ → 0 < ε →
    (Real.exp (lnΛ c γ) < (4 : ℝ) ^ (1 / ε) ↔ ε < Rc c γ)
def Corollary_31_gamma_pos : Prop :=
  ∀ c θ : ℝ, 10 < c → 0 < θ → 0 < gammaOf c θ
def Sec4_Rc_strictAntiOn : Prop :=
  ∀ γ : ℝ, 0 ≤ γ →
    StrictAntiOn (fun c : ℝ => Rc c γ) (Set.Ici 10)
def Sec4_Rc_zero_tendsto : Prop :=
  Filter.Tendsto (fun c : ℝ => Rc c 0) (nhdsWithin 10 (Set.Ioi 10)) (nhds epsStar)
def Sec4_epsStar_numeric : Prop :=
  0.1204 < epsStar ∧ epsStar < 0.1205
def Sec4_Rc_lt_epsStar : Prop :=
  ∀ c γ : ℝ, 10 < c → 0 ≤ γ → Rc c γ < epsStar
def Corollary_32_saving : Prop :=
  ∀ (D₀ : ℕ) (γ q κ : ℝ), 2 ≤ D₀ →
    (D₀ : ℝ) ^ (-(min γ (κ - q))) ≤ (D₀ : ℝ) ^ (-γ) + (D₀ : ℝ) ^ (q - κ) ∧
      (D₀ : ℝ) ^ (-γ) + (D₀ : ℝ) ^ (q - κ) ≤ 2 * (D₀ : ℝ) ^ (-(min γ (κ - q)))
def Table_2_query_valid : Prop :=
  ∀ c ε q γ₀ : ℝ, Table2Query c ε q γ₀ →
    ValidQueryEntry c ε q γ₀
def Table_2_ninth_valid : Prop :=
  ∀ c ε γ₀ : ℝ, Table2Ninth c ε γ₀ →
    ValidQueryEntry c ε 0.43 γ₀
def Table_2_density_valid : Prop :=
  ∀ c ε κ γ₀ : ℝ, Table2Density c ε κ γ₀ →
    ValidDensityEntry c ε κ γ₀
def Table_2_c40 : Prop :=
  Table2Row 40 0.029 0.0205 0.0608 0.1175 0.1429 0.2417 0.3095
    0.0166 0.0473 0.1060 0.1720 0.2442
def Table_2_c21 : Prop :=
  Table2Row 21 0.056 0.0112 0.0331 0.0640 0.0778 0.1316 0.1685
    0.0099 0.0286 0.0653 0.1074 0.1546
def Table_2_c19 : Prop :=
  Table2Row 19 0.062 0.0097 0.0287 0.0555 0.0675 0.1142 0.1463
    0.0087 0.0253 0.0578 0.0954 0.1379
def Table_2_c15 : Prop :=
  Table2Row 15 0.079 0.0061 0.0183 0.0354 0.0430 0.0728 0.0932
    0.0057 0.0168 0.0389 0.0646 0.0941
def Table_2_c12 : Prop :=
  Table2Row 12 0.099 0.0028 0.0083 0.0160 0.0195 0.0330 0.0423
    0.0027 0.0080 0.0186 0.0312 0.0459
def Table_2_c10_5 : Prop :=
  Table2Row 10.5 0.114 0.0007 0.0022 0.0043 0.0052 0.0089 0.0114
    0.0007 0.0022 0.0052 0.0087 0.0129
def Table_2_larger_c : Prop :=
  ∀ θ : ℝ, 0 < θ →
    StrictMonoOn (fun c : ℝ => gammaOf c θ) (Set.Ioi 10) ∧
      StrictAntiOn (fun c : ℝ => Rc c (gammaOf c θ)) (Set.Ioi 10)
def Table_1_section_2_column : Prop :=
  (∀ m : ℕ, rho (19 * m) m < 1 / 2) ∧
    gammaOf 19 (1 / 9) = 1 / 18 ∧
    1 / 18 < Rc 19 (1 / 18) ∧
    min (gammaOf 19 (1 / 9)) (1 / 2 - qOf (1 / 9)) = 1 / 18
def Corollary_26_W : Prop :=
  ∀ N D₀ W : ℕ, 1 ≤ D₀ → (W : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (D₀ : ℝ) →
    (W : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ) + (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)
      ≤ 2 * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ))
end PaperStatements
end Sec4Statements
section Sec5Definitions
open Finset
namespace ThreeSumApsp
def blockOfRows {R : Type} {b m l : ℕ} (A : Matrix (Fin (b * m)) (Fin l) R) (p : Fin b) :
    Matrix (Fin m) (Fin l) R :=
  fun i k => A (finProdFinEquiv (p, i)) k
def blockOfCols {R : Type} {b m l : ℕ} (B : Matrix (Fin l) (Fin (b * m)) R) (q : Fin b) :
    Matrix (Fin l) (Fin m) R :=
  fun k j => B k (finProdFinEquiv (q, j))
namespace ComparisonCounts
inductive Cmp : Type
  | lt
  | le
def Cmp.Holds : Cmp → ℝ → ℝ → Prop
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
structure Lists (n d : ℕ) : Type where
  /-- the row lists R_r -/
  row : Fin n → List (ℝ × Fin d)
  /-- the column lists C_c -/
  col : Fin n → List (ℝ × Fin d)
def Lists.Valid {n d : ℕ} (Ls : Lists n d) : Prop :=
  (∀ r, (Ls.row r).length ≤ d) ∧ (∀ c, (Ls.col c).length ≤ d)
abbrev RowItem {n d : ℕ} (Ls : Lists n d) : Type := Σ r : Fin n, Fin (Ls.row r).length
abbrev ColItem {n d : ℕ} (Ls : Lists n d) : Type := Σ c : Fin n, Fin (Ls.col c).length
abbrev Item {n d : ℕ} (Ls : Lists n d) : Type := RowItem Ls ⊕ ColItem Ls
def Item.val {n d : ℕ} {Ls : Lists n d} : Item Ls → ℝ
  | .inl x => ((Ls.row x.1).get x.2).1
  | .inr y => ((Ls.col y.1).get y.2).1
def Item.color {n d : ℕ} {Ls : Lists n d} : Item Ls → Fin d
  | .inl x => ((Ls.row x.1).get x.2).2
  | .inr y => ((Ls.col y.1).get y.2).2
def Item.ofRow {n d : ℕ} {Ls : Lists n d} (x : RowItem Ls) : Item Ls := .inl x
def Item.ofCol {n d : ℕ} {Ls : Lists n d} (y : ColItem Ls) : Item Ls := .inr y
def rowItem {n d : ℕ} {Ls : Lists n d} (r : Fin n) (i : Fin (Ls.row r).length) : Item Ls :=
  Item.ofRow ⟨r, i⟩
def colItem {n d : ℕ} {Ls : Lists n d} (c : Fin n) (i : Fin (Ls.col c).length) : Item Ls :=
  Item.ofCol ⟨c, i⟩
open Classical in
/-- Section 5.2: "γ(r,c) := |{(x,y) : x ∈ R_r, y ∈ C_c, χ(x) = χ(y), x < y}|" (with `≤` for
`Cmp.le`). The pairs are pairs of places in the two lists. -/
noncomputable def comparisonCount {n d : ℕ} (cmp : Cmp) (Ls : Lists n d) (r c : Fin n) : ℕ :=
  (univ.filter fun p : Fin (Ls.row r).length × Fin (Ls.col c).length =>
    (rowItem r p.1).color = (colItem c p.2).color ∧
      cmp.Holds ((rowItem r p.1).val) ((colItem c p.2).val)).card
def IsPredecessor {d : ℕ} (sums : Fin d → ℝ) (c v : ℝ) : Prop :=
  (∃ k, sums k = v) ∧ v ≤ c ∧ ∀ k, sums k ≤ c → sums k ≤ v
def IsSuccessor {d : ℕ} (sums : Fin d → ℝ) (c v : ℝ) : Prop :=
  (∃ k, sums k = v) ∧ c < v ∧ ∀ k, c < sums k → v ≤ sums k
def listOf {d : ℕ} (S : Finset (Fin d)) : List (Fin d) :=
  (List.finRange d).filter fun k => k ∈ S
open Classical in
/-- Proof of Lemma 36, the counting problem [CVX22, Problem 4.1]: "we are given a pivot k_ij ∈ [d]
for every (i,j) ∈ [n]² and a subset S ⊆ [d], and we must count, for every (i,j), the indices k' ∈ S
with A'[i,k'] + B'[k',j] < A'[i,k_ij] + B'[k_ij,j]; a call of the problem may also have ≤ in place
of <." -/
noncomputable def count41 {n d : ℕ} (cmp : Cmp) (A' : Matrix (Fin n) (Fin d) ℝ)
    (B' : Matrix (Fin d) (Fin n) ℝ) (pivot : Fin n → Fin n → Fin d) (S : Finset (Fin d))
    (i j : Fin n) : ℕ :=
  (S.filter fun k' => cmp.Holds (A' i k' + B' k' j) (A' i (pivot i j) + B' (pivot i j) j)).card
def pairs41 {n d : ℕ} (pivot : Fin n → Fin n → Fin d) (k : Fin d) : Finset (Fin n × Fin n) :=
  univ.filter fun ij => pivot ij.1 ij.2 = k
def lists41 {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin d)) (k : Fin d) : Lists n d where
  row i := (listOf S).map fun k' => (A' i k' - A' i k, k')
  col j := (listOf S).map fun k' => (B' k j - B' k' j, k')
open Classical in
/-- Proof of Lemma 36, the counting problem [CVX22, Problem 4.5]: "we must count, for every
(i,j,k,ℓ) ∈ Q, the pairs (k',ℓ') ∈ [d]² with A_i[k'] + B_j[ℓ'] < A_i[k] + B_j[ℓ]; again, a call may
have ≤ in place of <, and it may restrict k' and ℓ' to subsets of [d]."  Here `A i k` is A_i[k], the
k-th number of block A_i, and `K'`, `L'` are the subsets to which k' and ℓ' are restricted
(`Finset.univ` for no restriction), one pair of subsets for the whole call. -/
noncomputable def count45 {b d : ℕ} (cmp : Cmp) (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d))
    (i j : Fin b) (k l : Fin d) : ℕ :=
  ((K' ×ˢ L').filter fun kl => cmp.Holds (A i kl.1 + B j kl.2) (A i k + B j l)).card
def lists45 {b d : ℕ} (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d)) (χ₀ : Fin d) :
    Lists (b * d) d where
  row r := (listOf K').map fun k' =>
    (A (finProdFinEquiv.symm r).1 k' - A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2, χ₀)
  col c := (listOf L').map fun l' =>
    (B (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2 - B (finProdFinEquiv.symm c).1 l', χ₀)
def D'' (n d s : ℕ) : ℕ := ⌈(2 * n * d : ℚ) / s⌉₊ + d
def numOfColor {n d : ℕ} (Ls : Lists n d) (k : Fin d) : ℕ :=
  (univ.filter fun x : Item Ls => x.color = k).card
structure SortedOrder {n d : ℕ} (cmp : Cmp) (Ls : Lists n d) : Type where
  /-- pos(x), the position of x among the numbers of its color -/
  pos : Item Ls → ℕ
  /-- two numbers of the same color have different positions -/
  pos_injective : ∀ x y : Item Ls, x.color = y.color → pos x = pos y → x = y
  /-- the positions of the numbers of color k are 0, 1, ..., (number of numbers of color k) - 1 -/
  pos_lt : ∀ x : Item Ls, pos x < numOfColor Ls x.color
  /-- the order is sorted -/
  sorted : ∀ x y : Item Ls, x.color = y.color → x.val < y.val → pos x < pos y
  /-- the tie-breaking rule for `<`: a number y of a column list precedes an equal number x of a row
  list -/
  ties_lt : cmp = Cmp.lt → ∀ (x : RowItem Ls) (y : ColItem Ls),
    (Item.ofRow x).color = (Item.ofCol y).color →
    (Item.ofRow x).val = (Item.ofCol y).val → pos (Item.ofCol y) < pos (Item.ofRow x)
  /-- the reversed tie-breaking rule for `≤`: a number x of a row list precedes an equal number y of
  a column list -/
  ties_le : cmp = Cmp.le → ∀ (x : RowItem Ls) (y : ColItem Ls),
    (Item.ofRow x).color = (Item.ofCol y).color →
    (Item.ofRow x).val = (Item.ofCol y).val → pos (Item.ofRow x) < pos (Item.ofCol y)
def blk {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ) (x : Item Ls) : ℕ :=
  o.pos x / s
def blockPairs {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ) :
    Finset (Fin d × ℕ) :=
  univ.image fun x : Item Ls => (x.color, blk o s x)
def xCount {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (r : Fin n) (k : Fin d) (β : ℕ) : ℕ :=
  (univ.filter fun i : Fin (Ls.row r).length =>
    (rowItem r i).color = k ∧ blk o s (rowItem r i) = β).card
def yCount {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (k : Fin d) (β : ℕ) (c : Fin n) : ℕ :=
  (univ.filter fun i : Fin (Ls.col c).length =>
    (colItem c i).color = k ∧ β < blk o s (colItem c i)).card
def matX {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (idx : Fin d × ℕ → Fin (D'' n d s)) :
    Matrix (Fin n) (Fin (D'' n d s)) ℤ :=
  fun r j => ∑ kβ ∈ (blockPairs o s).filter (fun kβ => idx kβ = j), (xCount o s r kβ.1 kβ.2 : ℤ)
def matY {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (idx : Fin d × ℕ → Fin (D'' n d s)) :
    Matrix (Fin (D'' n d s)) (Fin n) ℤ :=
  fun j c => ∑ kβ ∈ (blockPairs o s).filter (fun kβ => idx kβ = j), (yCount o s kβ.1 kβ.2 c : ℤ)
def blockRowItems {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (kβ : Fin d × ℕ) : Finset (RowItem Ls) :=
  univ.filter fun x => (Item.ofRow x).color = kβ.1 ∧ blk o s (Item.ofRow x) = kβ.2
def blockColItems {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (kβ : Fin d × ℕ) : Finset (ColItem Ls) :=
  univ.filter fun y => (Item.ofCol y).color = kβ.1 ∧ blk o s (Item.ofCol y) = kβ.2
def sameBlockCount {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ)
    (P : Finset (Fin n × Fin n)) (r c : Fin n) : ℤ :=
  ∑ kβ ∈ blockPairs o s,
    (((blockRowItems o s kβ ×ˢ blockColItems o s kβ).filter fun xy =>
      o.pos (Item.ofRow xy.1) < o.pos (Item.ofCol xy.2) ∧ (xy.1.1, xy.2.1) ∈ P ∧ xy.1.1 = r ∧
        xy.2.1 = c).card : ℤ)
def enumeratedPairs {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (o : SortedOrder cmp Ls) (s : ℕ) : ℕ :=
  ∑ kβ ∈ blockPairs o s, (blockRowItems o s kβ).card * (blockColItems o s kβ).card
noncomputable def blockLen (n d : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 - 1 / 440 : ℝ) / d⌉₊
noncomputable def Dstar (n d : ℕ) : ℕ := ⌈3 * (d : ℝ) ^ 2 * (n : ℝ) ^ (1 / 440 : ℝ)⌉₊
noncomputable def listLen (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 40 : ℝ)⌋₊
end ComparisonCounts
namespace HintedMv
def boolMul {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (V : Matrix (Fin m) (Fin r) Bool) :
    Matrix (Fin l) (Fin r) Bool :=
  fun i j => decide (∃ k, M i k = true ∧ V k j = true)
def toInt {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) : Matrix (Fin l) (Fin m) ℤ :=
  fun i j => if M i j = true then 1 else 0
def vHintedOutput {n t : ℕ} (M : Matrix (Fin n) (Fin t) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (i : Fin n) : Fin n → Bool :=
  fun r => boolMul M V r i
def MvHintedOutput {n t : ℕ} (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (I : Fin t → Fin n) (j : Fin n) : Fin n → Bool :=
  fun r => boolMul (N.submatrix id I) V r j
def uMvHintedOutput {n t₁ t₂ : ℕ} (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (i j : Fin n) : Bool :=
  boolMul (boolMul U (N.submatrix I J)) V i j
def Conjecture52 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)
def Conjecture57 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)
def Conjecture512 (Achieves : ℝ → ℝ → ℝ → Prop) (ω₂ ω₃ τ₁ τ₂ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω₂ - ε) (ω₃ - ε) (τ₁ + τ₂ - ε)
end HintedMv
end ThreeSumApsp
end Sec5Definitions
section Sec5Statements
open Finset Asymptotics Filter
namespace PaperStatements
open ThreeSumApsp
def Theorem_34_blocks : Prop :=
  ∀ {b m : ℕ} (A : Matrix (Fin (b * m)) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin (b * m)) ℤ) (C : Matrix (Fin (b * m)) (Fin (b * m)) ℤ),
    IsMinPlusProduct A B C ↔
      ∀ p q : Fin b,
        IsMinPlusProduct (blockOfRows A p) (blockOfCols B q)
          (fun i j => C (finProdFinEquiv (p, i)) (finProdFinEquiv (q, j)))
def Theorem_34_entries : Prop :=
  ∀ n μ : ℝ, 1 ≤ n → 1 / 2 ≤ μ → n ^ (1 - μ) ≤ n ^ μ
def Theorem_34_total : Prop :=
  ∀ n μ : ℝ, 0 < n →
    n ^ (2 - 2 * μ) * (n ^ μ) ^ (3 - 0.00175 / 3 : ℝ) = n ^ (2 + μ - μ * 0.00175 / 3)
def Theorem_34_absorb : Prop :=
  ∀ μ ε₁ : ℝ, ε₁ < μ * 0.00175 / 3 →
  ∀ c : ℕ,
    (fun n : ℕ => (n : ℝ) ^ (2 + μ - μ * 0.00175 / 3) * Real.log n ^ c) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 + μ - ε₁))
section ComparisonCounts
open ComparisonCounts
def Lemma_36a_exact_triangle : Prop :=
  ∀ {b d : ℕ} (T : TriangleInstance ℝ (b * d)),
    T.HasZeroTriangle ↔
      ∃ (p : Fin b) (i j : Fin (b * d)),
        IsPredecessor
          (fun k : Fin d =>
            blockOfCols (fun i k => T.wAB i k) p i k + blockOfRows (fun k j => T.wBC k j) p k j)
          (-T.wAC i j) (-T.wAC i j)
def Lemma_36a_min_plus_below : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (rowMin colMin : Fin n → ℝ),
  (∀ i, IsLeast (Set.range fun k => A i k) (rowMin i)) →
  (∀ j, IsLeast (Set.range fun k => B k j) (colMin j)) →
  ∀ i j k : Fin n,
    rowMin i + colMin j - 1 < A i k + B k j
def Lemma_36a_min_plus_successor : Prop :=
  ∀ {d : ℕ} (sums : Fin d → ℝ) (c : ℝ), (∀ k, c < sums k) →
  ∀ v : ℝ,
    IsSuccessor sums c v ↔ IsLeast (Set.range sums) v
def Lemma_36a_min_plus_blocks : Prop :=
  ∀ {b d : ℕ} (A B C : Matrix (Fin (b * d)) (Fin (b * d)) ℝ)
    (M : Fin b → Matrix (Fin (b * d)) (Fin (b * d)) ℝ),
  (∀ p, IsMinPlusProduct (blockOfCols A p) (blockOfRows B p) (M p)) →
    (IsMinPlusProduct A B C ↔ ∀ i j, IsLeast (Set.range fun p => M p i j) (C i j))
def Lemma_36a_count : Prop :=
  ∀ {n d : ℕ} (cmp : Cmp) (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (pivot : Fin n → Fin n → Fin d) (S : Finset (Fin d)) (k : Fin d) (i j : Fin n),
  (i, j) ∈ pairs41 pivot k →
    count41 cmp A' B' pivot S i j = comparisonCount cmp (lists41 A' B' S k) i j
def Lemma_36a_valid : Prop :=
  ∀ {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin d)) (k : Fin d), (lists41 A' B' S k).Valid
def Lemma_36a_colors : Prop :=
  ∀ {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin d)) (k : Fin d),
    (∀ i, (((lists41 A' B' S k).row i).map Prod.snd).Nodup) ∧
      (∀ j, (((lists41 A' B' S k).col j).map Prod.snd).Nodup)
def Lemma_36a_pairs : Prop :=
  ∀ {n d : ℕ} (pivot : Fin n → Fin n → Fin d),
    ∑ k : Fin d, (pairs41 pivot k).card = n ^ 2
def Lemma_36a_subtractions : Prop :=
  ∀ {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ)
    (B' : Matrix (Fin d) (Fin n) ℝ) (S : Finset (Fin d)),
    (∀ k,
        ∑ i, ((lists41 A' B' S k).row i).length + ∑ j, ((lists41 A' B' S k).col j).length
          ≤ 2 * n * d) ∧
      ∑ k : Fin d,
          (∑ i, ((lists41 A' B' S k).row i).length + ∑ j, ((lists41 A' B' S k).col j).length)
        ≤ 2 * n * d ^ 2
def Lemma_36b_count : Prop :=
  ∀ {b d : ℕ} (cmp : Cmp) (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d))
    (χ₀ : Fin d) (i j : Fin b) (k l : Fin d),
    count45 cmp A B K' L' i j k l =
      comparisonCount cmp (lists45 A B K' L' χ₀)
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l))
def Lemma_36b_lists : Prop :=
  ∀ {b d : ℕ} (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d)) (χ₀ : Fin d),
    (lists45 A B K' L' χ₀).Valid ∧
      (∀ r, ((lists45 A B K' L' χ₀).row r).length = K'.card) ∧
      (∀ c, ((lists45 A B K' L' χ₀).col c).length = L'.card) ∧
      (∀ r, ∀ x ∈ (lists45 A B K' L' χ₀).row r, x.2 = χ₀) ∧
      (∀ c, ∀ y ∈ (lists45 A B K' L' χ₀).col c, y.2 = χ₀)
def Lemma_36b_subtractions : Prop :=
  ∀ {b d : ℕ} (A B : Fin b → Fin d → ℝ) (K' L' : Finset (Fin d))
    (χ₀ : Fin d),
    ∑ r, ((lists45 A B K' L' χ₀).row r).length + ∑ c, ((lists45 A B K' L' χ₀).col c).length
      ≤ 2 * (b * d) * d
def Lemma_37_order_exists : Prop :=
  ∀ {n d : ℕ} (cmp : Cmp) (Ls : Lists n d),
    Nonempty (SortedOrder cmp Ls)
def Lemma_37_index_exists : Prop :=
  ∀ {n d : ℕ} {cmp : Cmp} {Ls : Lists n d}, Ls.Valid →
  ∀ (o : SortedOrder cmp Ls) (s : ℕ), 1 ≤ s →
    ∃ idx : Fin d × ℕ → Fin (D'' n d s), Set.InjOn idx (blockPairs o s)
def Lemma_37 : Prop :=
  ∀ {n d : ℕ} (cmp : Cmp) (Ls : Lists n d), Ls.Valid →
  ∀ s : ℕ, 1 ≤ s →
  ∀ (P : Finset (Fin n × Fin n)) (o : SortedOrder cmp Ls) (idx : Fin d × ℕ → Fin (D'' n d s)),
  Set.InjOn idx (blockPairs o s) →
    (∀ r j, 0 ≤ matX o s idx r j ∧ matX o s idx r j ≤ d) ∧
      (∀ j c, 0 ≤ matY o s idx j c ∧ matY o s idx j c ≤ d) ∧
      ∀ r c, (r, c) ∈ P →
        (comparisonCount cmp Ls r c : ℤ) =
          (matX o s idx * matY o s idx) r c + sameBlockCount o s P r c
def Lemma_37_enumerated : Prop :=
  ∀ {n d : ℕ} {cmp : Cmp} {Ls : Lists n d}, Ls.Valid →
  ∀ (o : SortedOrder cmp Ls) (s : ℕ), 1 ≤ s →
    (∀ kβ, ((blockRowItems o s kβ).card * (blockColItems o s kβ).card : ℚ) ≤ (s : ℚ) ^ 2 / 4) ∧
      (enumeratedPairs o s : ℚ) ≤ ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 ∧
      ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 ≤ (n * d * s + d * s ^ 2 : ℚ)
def Corollary_38_bound : Prop :=
  ∃ (K : ℝ) (n₀ : ℕ), ∀ n d p : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
    ((p : ℝ) * (Dstar n d : ℝ) ^ (0.437 : ℝ) + (n : ℝ) ^ 2 / (Dstar n d : ℝ) ^ (0.063 : ℝ)) +
        ((n : ℝ) * Dstar n d +
          ((n : ℝ) * d * blockLen n d + (d : ℝ) * (blockLen n d : ℝ) ^ 2 + (p : ℝ)) *
            (Real.log n + 1))
      ≤ K * ((p : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ) +
        (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
def Corollary_38_correct : Prop :=
  ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
    ∀ (cmp : Cmp) (Ls : Lists n d), Ls.Valid →
    ∀ (P : Finset (Fin n × Fin n)) (o : SortedOrder cmp Ls)
      (idx : Fin d × ℕ → Fin (D'' n d (blockLen n d))),
    Set.InjOn idx (blockPairs o (blockLen n d)) →
      D'' n d (blockLen n d) ≤ Dstar n d ∧
      (Dstar n d) ^ 18 ≤ n ∧
      (∀ r j, |(padInnerCols (Dstar n d) (matX o (blockLen n d) idx)) r j| ≤ n) ∧
      (∀ j c, |(padInnerRows (Dstar n d) (matY o (blockLen n d) idx)) j c| ≤ n) ∧
      ∀ r c, (r, c) ∈ P →
        (comparisonCount cmp Ls r c : ℤ) =
          ((padInnerCols (Dstar n d) (matX o (blockLen n d) idx)) *
            (padInnerRows (Dstar n d) (matY o (blockLen n d) idx))) r c
          + sameBlockCount o (blockLen n d) P r c
def Theorem_35_d : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    1 ≤ listLen n ∧ listLen n ≤ n ∧ (listLen n : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ)
def Theorem_35_counting_call : Prop :=
  ∃ (K : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → ∀ p : Fin (listLen n) → ℕ, ∑ k, p k = n ^ 2 →
    ∑ k, ((p k : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ)
        + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
      ≤ K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n)
def Theorem_35_forming_lists : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * (listLen n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1.05 : ℝ)
def Theorem_35_min_plus_total : Prop :=
  ∀ (c : ℕ),
    ((fun n : ℕ => (n : ℝ) / listLen n * (n : ℝ) ^ (2.0229 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (3 - 1 / 40 + 0.0229 : ℝ) * Real.log n ^ c)) ∧
      ((fun n : ℕ => (n : ℝ) ^ (3 - 1 / 40 + 0.0229 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.998 : ℝ)))
def Theorem_35_further_time : Prop :=
  ∀ (c : ℕ),
    ((fun n : ℕ => (n : ℝ) ^ 3 / listLen n * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.975 : ℝ) * Real.log n ^ c)) ∧
      ((fun n : ℕ => (n : ℝ) ^ (2.975 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.998 : ℝ)))
def Theorem_35_three_sum_count : Prop :=
  ((fun n : ℕ => (n : ℝ) ^ 2 / listLen n * (n : ℝ) ^ (0.0229 : ℝ) +
        (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ) + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (2 - 1 / 40 + 0.0229 : ℝ) * Real.log n)) ∧
    (2 - 1 / 40 + 0.0229 : ℝ) = 1.9979
def Theorem_35_three_sum_total : Prop :=
  ∀ (c : ℕ),
    ((fun n : ℕ => (n : ℝ) ^ (1.9979 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1.998 : ℝ))) ∧
      ((fun n : ℕ => (n : ℝ) ^ 2 / listLen n * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1.998 : ℝ)))
def Theorem_35_one_run : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure Pr] (T : Ω → ℝ),
  MeasureTheory.Integrable T Pr → (∀ ω, 0 ≤ T ω) →
  ∀ B : ℝ, 0 < B → (∫ ω, T ω ∂Pr ≤ B) →
    Pr {ω | 2 * B < T ω} ≤ 1 / 2
def Theorem_35_restarts : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure Pr] (m : ℕ) (T : Fin m → Ω → ℝ),
  ProbabilityTheory.iIndepFun T Pr →
  ∀ B : ℝ, (∀ i, Pr {ω | 2 * B < T i ω} ≤ 1 / 2) →
  ∀ n : ℕ, 2 ≤ n →
  ∀ c : ℝ, c * Real.logb 2 n ≤ m →
    Pr {ω | ∀ i, 2 * B < T i ω} ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))
end ComparisonCounts
end PaperStatements
end Sec5Statements
section WordRamProblems
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
def Admissible (b : Nat) (params : List Nat) (W : Nat) : Prop :=
  b * ((params.map Nat.log2).sum + 1) ≤ W
def output {W : Nat} (c : Int → BitVec W) (len : Nat) (i : Nat) : Int :=
  (c ((len : Int) + (i : Int))).toInt
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The parameters of an instance on which the word size depends: its sizes. -/
  params : Inst → List ℕ
  /-- The input: the numbers written into the cells 0, 1, 2, … -/
  input : Inst → List ℤ
  /-- `IsAnswer x verdict out`: the verdict, and the numbers `out 0, out 1, …` in the cells right
  after the input, are a correct answer to the instance `x`. -/
  IsAnswer : Inst → Bool → (ℕ → ℤ) → Prop
def Solves (prob : Problem) (P : List Instr) (b : ℕ) (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) :
    Prop :=
  ∀ x : prob.Inst, dom x → ∀ bits : ℕ, Admissible b (prob.params x) bits →
    ∃ (t : ℕ) (verdict : Bool) (c : ℤ → BitVec bits), (t : ℝ) ≤ T x ∧
      exec P t 0 (loadWords bits (prob.input x)) = some (verdict, c) ∧
      prob.IsAnswer x verdict (output c (prob.input x).length)
def SolvesWithin (Q : EndStatement.Problem) (κ : ℕ) (P : List Instr) (b : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
    ∃ t : ℕ, (t : ℝ) ≤ T n ∧ Q.SolvedBy x P W t
def SolvedInTimeAt (Q : EndStatement.Problem) (κ : ℕ) (a : ℝ) (e : ℕ) : Prop :=
  ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ a * Real.log n ^ e + 1)
def SolvedInTime (Q : EndStatement.Problem) (a : ℝ) (e : ℕ) : Prop :=
  ∀ κ : ℕ, SolvedInTimeAt Q κ a e
def SolvedInPolylogTime (Q : EndStatement.Problem) (a : ℝ) : Prop :=
  ∀ κ : ℕ, ∃ e : ℕ, SolvedInTimeAt Q κ a e
def SolvedInLittleOTime (Q : EndStatement.Problem) (a : ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ) (o : ℕ → ℝ), Filter.Tendsto o Filter.atTop (nhds 0) ∧
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ (a + o n) + 1)
def withQuery {bits : ℕ} (c : ℤ → BitVec bits) (qI qJ : ℤ) (I J : ℕ) : ℤ → BitVec bits :=
  fun a => if a = qI then BitVec.ofInt bits I else if a = qJ then BitVec.ofInt bits J else c a
def Serves {bits : ℕ} (Q : List Instr) (qI qJ qOut : ℤ) (tq : ℕ) (entry : ℕ → ℕ → ℤ) :
    (ℤ → BitVec bits) → List (ℕ × ℕ) → Prop
  | _, [] => True
  | c, q :: rest =>
    ∃ c' : ℤ → BitVec bits, exec Q tq 0 (withQuery c qI qJ q.1 q.2) = some (true, c') ∧
      (c' qOut).toInt = entry q.1 q.2 ∧ Serves Q qI qJ qOut tq entry c' rest
def withInput {bits : ℕ} (c : ℤ → BitVec bits) (off : ℕ) (ws : List ℤ) : ℤ → BitVec bits :=
  fun a =>
    if (off : ℤ) ≤ a ∧ a < (off : ℤ) + (ws.length : ℤ) then
      BitVec.ofInt bits (ws.getD (a - (off : ℤ)).toNat 0)
    else c a
def RunsPhases {bits : ℕ} (good : (ℤ → BitVec bits) → ℕ → Prop) :
    (ℤ → BitVec bits) → ℕ → List (List Instr × List ℤ × ℕ) → Prop
  | c, off, [] => good c off
  | c, off, (P, ws, s) :: rest =>
    ∃ c' : ℤ → BitVec bits, exec P s 0 (withInput c off ws) = some (true, c') ∧
      RunsPhases good c' (off + ws.length) rest
def Within (s : ℕ) (C : ℝ) (n : ℕ) (a : ℝ) : Prop := (s : ℝ) ≤ C * ((n : ℝ) ^ a + 1)
def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j
def bit (p : Bool) : ℤ := if p then 1 else 0
structure ThinPair where
  /-- The long side. -/
  N : ℕ
  /-- The short side. -/
  D : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The first matrix. -/
  X : Matrix (Fin N) (Fin D) ℤ
  /-- The second matrix. -/
  Y : Matrix (Fin D) (Fin N) ℤ
  /-- The entries of `X` are bounded. -/
  boundX : ∀ i j, |X i j| ≤ (U : ℤ)
  /-- The entries of `Y` are bounded. -/
  boundY : ∀ i j, |Y i j| ≤ (U : ℤ)
structure ThinInstance extends ThinPair where
  /-- The wanted positions. -/
  W : List (Fin N × Fin N)
  /-- No position is listed twice. -/
  nodup : W.Nodup
def ThinInstance.input (x : ThinInstance) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y ++
    x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map (fun q => (q.2.val : ℤ))
def thinProduct (extra : List ℤ) : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input extra
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length), out i = (x.X * x.Y) x.W[i].1 x.W[i].2
def ThinPair.input (x : ThinPair) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y
def IsDataStructure (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (extra : List ℤ)
    (dom : ThinPair → Prop) (Tp Sp Tq : ThinPair → ℝ) : Prop :=
  ∀ x : ThinPair, dom x → ∀ bits : ℕ, Admissible b [x.N, x.D] bits →
    ∃ (tp tq : ℕ) (c : ℤ → BitVec bits), (tp : ℝ) ≤ Tp x ∧ (tq : ℝ) ≤ Tq x ∧
      exec P tp 0 (loadWords bits (x.input extra)) = some (true, c) ∧
      (∀ a : ℤ, ((a : ℝ) < -Sp x ∨ ((x.input extra).length : ℝ) + Sp x < (a : ℝ)) →
        c a = loadWords bits (x.input extra) a) ∧
      ∀ queries : List (ℕ × ℕ), (∀ q ∈ queries, q.1 < x.N ∧ q.2 < x.N) →
        Serves Q qI qJ qOut tq
          (fun I J => if h : I < x.N ∧ J < x.N then (x.X * x.Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0) c queries
def ThinInstance.ZeroOne (x : ThinInstance) : Prop :=
  (∀ i j, x.X i j = 0 ∨ x.X i j = 1) ∧ (∀ i j, x.Y i j = 0 ∨ x.Y i j = 1)
def ThinInstance.lop (x : ThinInstance) : LopInstance x.N :=
  LopInstance.ofMatrices x.X x.Y x.W.toFinset
def lopCount : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length),
      out i = (x.lop.numTriangles x.W[i].1 x.W[i].2 : ℤ)
def lopDetect : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length),
      (x.lop.InTriangle x.W[i].1 x.W[i].2 → out i = 1) ∧
        (¬ x.lop.InTriangle x.W[i].1 x.W[i].2 → out i = 0)
structure WeightedGraph (n : ℕ) where
  /-- The graph. -/
  G : SimpleGraph (Fin n)
  /-- The weight of the edge `{u, v}`. -/
  w : Fin n → Fin n → ℤ
  /-- The graph is undirected. -/
  symm : ∀ u v, w u v = w v u
open Classical in
/-- **Exact Triangle on `n`-vertex graphs**, stated as the problems of `EndStatement.lean` are: the
input is the adjacency matrix (1 for an edge, 0 for none), then the matrix of the weights (0 where
there is no edge); accept exactly if three pairwise adjacent vertices have edge weights that sum to
zero. -/
noncomputable def GraphExactTriangle : EndStatement.Problem where
  Instance := WeightedGraph
  input x := rowMajor (fun u v => if x.G.Adj u v then 1 else 0) ++
    rowMajor (fun u v => if x.G.Adj u v then x.w u v else 0)
  yes x := GraphHasZeroTriangle x.G x.w
def cliqueWeight {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ) (v : Fin k → Fin n) : ℤ :=
  ∑ p : Fin k, ∑ q ∈ Finset.univ.filter (fun q : Fin k => p < q), w p q (v p) (v q)
def MinKClique (k : ℕ) : EndStatement.Problem where
  Instance n := {_w : Fin k → Fin k → Fin n → Fin n → ℤ // 1 ≤ n}
  input w := (EndStatement.ZeroWeightKClique k).input w.1
  output {n} w out := ∃ v : Fin k → Fin n, (∀ p : Fin k, out p.val = ((v p).val : ℤ)) ∧
    ∀ v', cliqueWeight w.1 v ≤ cliqueWeight w.1 v'
def MaxKClique (k : ℕ) : EndStatement.Problem where
  Instance n := {_w : Fin k → Fin k → Fin n → Fin n → ℤ // 1 ≤ n}
  input w := (EndStatement.ZeroWeightKClique k).input w.1
  output {n} w out := ∃ v : Fin k → Fin n, (∀ p : Fin k, out p.val = ((v p).val : ℤ)) ∧
    ∀ v', cliqueWeight w.1 v' ≤ cliqueWeight w.1 v
noncomputable def hintSize (τ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ τ⌋₊
open HintedMv in
/-- **v-hinted Mv** (Section 5.4; Definition 5.1 of [vdBNS19]) with `t = n^τ` is solved with
polynomial time in Phase 1, `O(n^{a₂})` time in Phase 2 and `O(n^{a₃})` time in Phase 3.  Phase 1
receives `n`, `t` and the `n × t` matrix `M`; Phase 2 the `t × n` matrix `V`; Phase 3 the index `i`;
the output is the `n` entries of the Boolean product of `M` and column `i` of `V`. -/
def AchievesVHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (M : Matrix (Fin n) (Fin (hintSize τ n)) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (i : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (vHintedOutput M V i r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt M), s₁),
            (P₂, rowMajor (toInt V), s₂), (P₃, [(i.val : ℤ)], s₃)]
open HintedMv in
/-- **Mv-hinted Mv** (Section 5.4; Definition 5.6 of [vdBNS19]) with `t = n^τ`, in the same sense.
Phase 1 receives `n`, `t`, the `n × n` matrix `N` and the `t × n` matrix `V`; Phase 2 the `t` column
indices `I`; Phase 3 the index `j`; the output is the `n` entries of `N_{[n],I} V_{[t],j}`. -/
def AchievesMvHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (I : Fin (hintSize τ n) → Fin n) (j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (MvHintedOutput N V I j r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂), (P₃, [(j.val : ℤ)], s₃)]
open HintedMv in
/-- **uMv-hinted uMv** (Section 5.4; Definition 5.11 of [vdBNS19]) with `t₁ = n^{τ₁}` and `t₂ =
n^{τ₂}` is solved with polynomial time in Phase 1 and `O(n^{a₂})`, `O(n^{a₃})`, `O(n^{a₄})` time in
Phases 2, 3, 4.  Phase 1 receives `n`, `t₁`, `t₂` and the matrices `U` (`n × t₁`), `N` (`n × n`),
`V` (`t₂ × n`); Phase 2 the `t₁` row indices `I`; Phase 3 the `t₂` column indices `J`; Phase 4 the
indices `i` and `j`; the output is the one entry `(U N_{I,J} V)_{i,j}`. -/
def AchievesUMvHinted (τ₁ τ₂ a₂ a₃ a₄ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ P₄ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (U : Matrix (Fin n) (Fin (hintSize τ₁ n)) Bool) (N : Matrix (Fin n) (Fin n) Bool)
      (V : Matrix (Fin (hintSize τ₂ n)) (Fin n) Bool) (I : Fin (hintSize τ₁ n) → Fin n)
      (J : Fin (hintSize τ₂ n) → Fin n)
      (i j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ s₄ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧ Within s₄ C n a₄ ∧
        RunsPhases (fun c off => output c off 0 = bit (uMvHintedOutput U N V I J i j))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ₁ n : ℤ), (hintSize τ₂ n : ℤ)] ++ rowMajor (toInt U) ++
              rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂),
            (P₃, List.ofFn fun k => ((J k).val : ℤ), s₃),
            (P₄, [(i.val : ℤ), (j.val : ℤ)], s₄)]
end ThreeSumApsp.WordRam
end WordRamProblems
section AgreementStatements
open ThreeSumApsp.WordRam
namespace PaperStatements
open ThreeSumApsp
def Agreement_exactTriangle : Prop :=
  ∀ {n : ℕ} (T : TriangleInstance ℤ n),
    EndStatement.ExactTriangle.yes (T.wAB, T.wBC, T.wAC) ↔ T.HasZeroTriangle
def Agreement_minPlusProduct : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) (out : ℕ → ℤ),
    EndStatement.MinPlusProduct.output (A, B) out ↔
      IsMinPlusProduct A B (Matrix.of fun i j => out (i.val * n + j.val))
def Agreement_apsp_noNegativeCycle : Prop :=
  ∀ {n : ℕ} (w : Fin n → Fin n → Option ℤ),
    (∀ i d, EndStatement.Path w i i d → 0 ≤ d) ↔
      NoNegativeCycle fun i j => (w i j).elim ⊤ fun z => (z : WithTop ℤ)
def Agreement_apsp_output : Prop :=
  ∀ {n : ℕ} (x : EndStatement.APSP.Instance n) (out : ℕ → ℤ),
    EndStatement.APSP.output x out ↔
      (∀ i j : Fin n, out (2 * (i.val * n + j.val)) = 0 ∨ out (2 * (i.val * n + j.val)) = 1) ∧
      IsDistanceMatrix (fun i j => (x.1 i j).elim ⊤ fun z => (z : WithTop ℤ)) fun i j =>
        if out (2 * (i.val * n + j.val)) = 1 then (out (2 * (i.val * n + j.val) + 1) : WithTop ℤ)
        else ⊤
def Agreement_rowByRow : Prop :=
  ∀ {n : ℕ} (w : Fin n → Fin n → ℤ),
    EndStatement.rowByRow w = rowMajor w
def Agreement_cliqueWeight : Prop :=
  ∀ {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ),
    (∀ v : Fin k → Fin n,
      (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum =
        cliqueWeight w v) ∧
    ((EndStatement.ZeroWeightKClique k).yes w ↔ ∃ v, cliqueWeight w v = 0)
def Agreement_solves : Prop :=
  ∀ (Q : EndStatement.Problem) (κ : ℕ) (P : List EndStatement.Instr) (b : ℕ)
    (T : ℕ → ℝ),
    SolvesWithin Q κ P b T ↔
      Solves
        ⟨Σ n, {x : Q.Instance n // ∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ},
          fun ⟨n, _⟩ => [n],
          fun ⟨n, x, _⟩ => (n : ℤ) :: Q.input x,
          fun ⟨_, x, _⟩ verdict out => (verdict = true ↔ Q.yes x) ∧ Q.output x out⟩
        P b (fun _ => True) fun ⟨n, _⟩ => T n
def Agreement_bigO : Prop :=
  ∀ (T : ℕ → ℕ) (r : ℚ), 0 ≤ r →
    (EndStatement.BigO T r ↔ IsBigOPow (fun n => (T n : ℝ)) (r : ℝ))
def Agreement_solvedInTime : Prop :=
  ∀ (Q : EndStatement.Problem) (r : ℚ), 0 ≤ r →
    (Q.SolvedInTime r ↔ SolvedInTime Q (r : ℝ) 0)
end PaperStatements
end AgreementStatements
section WordRamItems
namespace ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace Items
def Theorem_5 : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b
      (fun x => (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧
        (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / Real.sqrt x.D ∧ x.U = x.N ^ c)
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ (1 / 18 : ℝ)))
def Corollary_15 : Prop :=
  ∃ (Pc Pd : List Instr) (b : ℕ) (C : ℝ),
    Solves lopCount Pc b
      (fun x => x.ZeroOne ∧ x.U = 1 ∧ (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * (((x.N : ℝ) ^ 2 + (x.W.length : ℝ) * Real.sqrt x.D) * Real.log x.D ^ 2 /
        (x.D : ℝ) ^ (1 / 18 : ℝ))) ∧
    Solves lopDetect Pd b
      (fun x => x.ZeroOne ∧ x.U = 1 ∧ (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * (((x.N : ℝ) ^ 2 + (x.W.length : ℝ) * Real.sqrt x.D) * Real.log x.D ^ 2 /
        (x.D : ℝ) ^ (1 / 18 : ℝ)))
def Corollary_16 : Prop :=
  ∃ (Pc Pd : List Instr) (b : ℕ) (C : ℝ),
    Solves lopCount Pc b (fun x => x.ZeroOne ∧ x.U = 1 ∧ 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ))) ∧
    Solves lopDetect Pd b (fun x => x.ZeroOne ∧ x.U = 1 ∧ 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
def Theorem_19 : Prop :=
  SolvedInTime EndStatement.ExactTriangle (3 - 1 / 648) 2 ∧
  SolvedInTime EndStatement.ExactTriangle (3 - 0.00175) 1 ∧
  SolvedInTime EndStatement.ExactTriangle (3 - 0.0017) 0
def Theorem_22_first : Prop :=
  SolvedInTime EndStatement.ThreeSum 1.99923 0 ∧
  SolvedInPolylogTime EndStatement.MinPlusProduct (3 - 1 / 1944) ∧
  SolvedInPolylogTime EndStatement.APSP (3 - 1 / 1944) ∧
  SolvedInTime EndStatement.MinPlusProduct 2.99949 0 ∧
  SolvedInTime EndStatement.APSP 2.99949 0
def Theorem_22_second : Prop :=
  SolvedInTime EndStatement.ThreeSum 1.9992 0 ∧
  SolvedInPolylogTime EndStatement.MinPlusProduct (3 - 0.00175 / 3) ∧
  SolvedInPolylogTime EndStatement.APSP (3 - 0.00175 / 3) ∧
  SolvedInTime EndStatement.MinPlusProduct 2.99942 0 ∧
  SolvedInTime EndStatement.APSP 2.99942 0
def Theorem_22_threeSum : Prop :=
  SolvedInLittleOTime EndStatement.ThreeSum (2 - 1 / 1296) ∧
  SolvedInLittleOTime EndStatement.ThreeSum (2 - 0.00175 / 2)
def thinDom (lo : ℕ) (ε : ℝ) (c₀ : ℕ) (x : ThinPair) : Prop :=
  1 ≤ x.N ∧ lo ≤ x.D ∧ (x.D : ℝ) ≤ (x.N : ℝ) ^ ε ∧ x.U = x.N ^ c₀
def HasDataStructure (ε γ q : ℝ) : Prop :=
  ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (thinDom 2 ε c₀)
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.D : ℝ) ^ q * Real.log x.D))
def Theorem_24 : Prop :=
  ∀ ε q : ℝ, ε < epsStar → 0 < q → ∃ γ : ℝ, 0 < γ ∧ HasDataStructure ε γ q
def Theorem_25 : Prop :=
  ∀ ε κ : ℝ, ε < epsStar → 0 < κ → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 2 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
def Corollary_26 : Prop :=
  ∀ c : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ x.U = x.N ^ c)
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * (x.D : ℝ) ^ (0.437 : ℝ))
def Corollary_26_wanted : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ x.U = x.N ^ c)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
def theorem30Dom (c m L t : ℕ) (x : ThinPair) : Prop :=
  1 ≤ m ∧ x.D = 4 ^ m ∧ 10 * m ≤ L ∧ t ≤ m ∧ Real.sqrt (K L m) * (N0 L m : ℝ) ≤ (x.N : ℝ) ∧
    x.U = x.N ^ c
def Theorem_30 : Prop :=
  ∀ c : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), ∀ m L t : ℕ,
    IsDataStructure P Q qI qJ qOut b [(m : ℤ), (L : ℤ), (t : ℤ)] (theorem30Dom c m L t)
      (fun x => C * cost8 L m t x.N) (fun x => C * cost8 L m t x.N) (fun _ => C * costQuery L m t)
def Theorem_30_wanted : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ), ∀ m L t : ℕ,
    Solves (thinProduct [(m : ℤ), (L : ℤ), (t : ℤ)]) P b
      (fun x => theorem30Dom c m L t x.toThinPair)
      (fun x => C * cost9 L m t x.N x.W.length)
def Corollary_31 : Prop :=
  ∀ c θ ε : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) →
    HasDataStructure ε (gammaOf c θ) (qOf θ)
def DataStructureBelow (ε₀ : ℝ) : Prop :=
  ∀ ε q : ℝ, ε < ε₀ → 0 < q → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
      IsDataStructure P Q qI qJ qOut b [] (thinDom 1 ε c₀)
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * (x.D : ℝ) ^ q)
def Corollary_32 : Prop :=
  ∀ c θ ε κ : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) → 0 < κ →
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 2 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 *
          ((x.D : ℝ) ^ (-gammaOf c θ) + (x.D : ℝ) ^ (qOf θ - κ))))
def WantedBelow (ε₀ : ℝ) : Prop :=
  ∀ ε κ : ℝ, ε < ε₀ → 0 < κ → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 1 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
def Corollary_39_zero : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    SolvedInTime (EndStatement.ZeroWeightKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0
def Corollary_39_min_max : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    SolvedInTime (MinKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0 ∧
    SolvedInTime (MaxKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0
def Corollary_40_times : Prop :=
  (∀ τ : ℝ, 0 < τ → τ < 1 / 18 →
    AchievesVHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ) ∧
      AchievesMvHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ)) ∧
  ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < τ₂ / 18 → τ₂ < 1 →
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - 0.063 * τ₁) (τ₂ + 0.437 * τ₁)
def Corollary_40_general_times : Prop :=
  (∀ τ : ℝ, 0 < τ → τ < epsStar → ∃ γ : ℝ, 0 < γ ∧
    AchievesVHinted τ (2 - γ * τ) (1 + τ / 2) ∧ AchievesMvHinted τ (2 - γ * τ) (1 + τ / 2)) ∧
  ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < epsStar * τ₂ → τ₂ < 1 → ∃ γ : ℝ, 0 < γ ∧
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - γ * τ₁) (τ₂ + τ₁ / 2)
def Corollary_40_fail (τ₀ : ℝ) : Prop :=
  (∀ τ ω : ℝ, 0 < τ → τ < τ₀ → 2 ≤ ω →
    ¬ HintedMv.Conjecture52 (AchievesVHinted τ) ω τ ∧
      ¬ HintedMv.Conjecture57 (AchievesMvHinted τ) ω τ) ∧
  ∀ τ₁ τ₂ ω₂ ω₃ : ℝ, 0 < τ₁ → τ₁ < τ₀ * τ₂ → τ₂ < 1 → 2 ≤ ω₂ → 1 + τ₂ ≤ ω₃ →
    ¬ HintedMv.Conjecture512 (AchievesUMvHinted τ₁ τ₂) ω₂ ω₃ τ₁ τ₂
def Theorem_1 : Prop :=
  (∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b
      (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / Real.sqrt x.D ∧
        x.U = x.N ^ c₀)
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))) ∧
  WantedBelow 0.1204
def Theorem_2 : Prop :=
  SolvedInTime EndStatement.ExactTriangle 2.9983 0 ∧
  SolvedInTime EndStatement.APSP 2.9995 0 ∧
  SolvedInTime EndStatement.MinPlusProduct 2.9995 0 ∧
  SolvedInTime EndStatement.ThreeSum 1.9992 0
def Theorem_2_graphs : Prop :=
  SolvedInTime GraphExactTriangle 2.9983 0
def Theorem_3 : Prop :=
  Corollary_26 ∧ DataStructureBelow 0.1204
def Theorem_4 : Prop :=
  Corollary_40_times ∧ Corollary_40_fail (1 / 18) ∧ Corollary_40_fail 0.1204
end Items
end ThreeSumApsp.WordRam
end WordRamItems


