-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P60
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P60
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:27:14.071892+00:00
-- url     : https://prove2.me/theorems/8988df59-b80d-435b-b9ad-c7a597827922
-- title:
--   Definitions for Framed bicategories and monoidal fibrations
-- statement:
--   The objects the formalized statements of *Framed bicategories and monoidal fibrations* (arXiv:0706.1286) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DoubleData`: The operations of a pseudo double category (Definition 2.1, PDF pp. 5–6). The vertical category and both horizontal dimensions have independent universes. The laws are specified separately by `DoubleCoherence`. The right frame of a composite is that of its second factor, as in the typed diagram on PDF p. 6; the displayed R(M odot N)=RM on PDF p. 5 is an apparent typographical error.
--   - `DoubleData.seq`: Composition of globular cells, transporting identity frames (PDF p. 6).
--   - `DoubleCoherence`: All pseudo double category axioms: vertical category laws, the two functors, interchange, invertible globular constraints natural for ALL squares, pentagon, and triangle (Definition 2.1 and conventions, PDF pp. 5–6).
--   - `IsCartesian`: The universal lifting property for the JOINT frame functor, not a single frame projection (Definition 3.1, PDF pp. 9–10; explicit square form pp. 13–14).
--   - `IsOpcartesian`: Dual universal lifting property for the joint frame functor (PDF pp. 12–14).
--   - `IsFrameFibration`: Existence of every joint cartesian lift (Definition 3.1 and §4, PDF pp. 10, 13).
--   - `IsFrameOpfibration`: Existence of every joint opcartesian lift (PDF pp. 12–13).
--   - `Companion`: Companion with both identities, including unitors in the horizontal zigzag (4.2)–(4.4), PDF p. 15; Definition A.1, PDF pp. 71–72.
--   - `Conjoint`: Conjoint with both identities, dual to the companion (PDF pp. 15, 71–72).
--   - `HasCompanions`: Every vertical arrow admits a companion (PDF p. 72).
--   - `HasConjoints`: Every vertical arrow admits a conjoint (PDF p. 72).
--   - `IsFramed`: Nonalgebraic framing; the chosen characterization is (L,R) a fibration (Definition 4.8, PDF p. 17). Coherence is separately required in the theorem binders.
--   - `PseudoConnectionPair`: Arbitrary chosen companions on a possibly non-strict double category, called a pseudo connection pair in Appendix A (PDF p. 72).
--   - `PseudoOpConnectionPair`: Arbitrary chosen conjoints, called a pseudo op-connection pair in Appendix A (PDF p. 72); no strict horizontal composition is imposed.
--   - `IsDualPair`: Both triangle identities for specified evaluation and coevaluation cells (Definition 5.2, PDF p. 20).
--   - `baseCoevaluation`: Canonical coevaluation from the two base-change unit cells (Proposition 5.3, diagram across PDF pp. 20–21).
--   - `baseEvaluation`: Canonical evaluation from the two base-change counit cells (Proposition 5.3, PDF p. 21).
--   - `thinDoubleData`: A thin test double category over any vertical category; all horizontal arrows and all squares are unique. Used only to check the local interfaces.
--   - `thinDoubleCoherence`: Sanity check: the complete coherence package is satisfiable, including for empty vertical categories (the source imposes no nonemptiness).
-- source:
--   Framed bicategories and monoidal fibrations, arXiv:0706.1286v2, https://arxiv.org/abs/0706.1286v2

import Mathlib

/-!
Statements from Shulman, arXiv:0706.1286v2. PDF page numbers are used throughout.
The local square presentation retains weak horizontal composition and strict vertical
composition. HEq in the laws only suppresses transports along category identity and
associativity equalities; it does not identify horizontal composites as objects.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P60

open CategoryTheory

universe u v w x

/-- The operations of a pseudo double category (Definition 2.1, PDF pp. 5–6).
The vertical category and both horizontal dimensions have independent universes.
The laws are specified separately by `DoubleCoherence`. The right frame of a
composite is that of its second factor, as in the typed diagram on PDF p. 6;
the displayed R(M odot N)=RM on PDF p. 5 is an apparent typographical error. -/
structure DoubleData (V : Type u) [Category.{v} V] where
  H : V → V → Type w
  Cell : {A B C D : V} → (A ⟶ C) → (B ⟶ D) → H A B → H C D → Type x
  unit : (A : V) → H A A
  mul : {A B C : V} → H A B → H B C → H A C
  idCell : {A B : V} → (M : H A B) → Cell (𝟙 A) (𝟙 B) M M
  vcomp : {A B C D E F : V} → {f : A ⟶ C} → {g : B ⟶ D} →
    {h : C ⟶ E} → {k : D ⟶ F} → {M : H A B} → {N : H C D} →
    {P : H E F} → Cell f g M N → Cell h k N P → Cell (f ≫ h) (g ≫ k) M P
  unitCell : {A B : V} → (f : A ⟶ B) → Cell f f (unit A) (unit B)
  hcomp : {A B C D E F : V} → {f : A ⟶ D} → {g : B ⟶ E} →
    {h : C ⟶ F} → {M : H A B} → {N : H B C} → {P : H D E} →
    {Q : H E F} → Cell f g M P → Cell g h N Q → Cell f h (mul M N) (mul P Q)
  assoc : {A B C D : V} → (M : H A B) → (N : H B C) → (P : H C D) →
    Cell (𝟙 A) (𝟙 D) (mul (mul M N) P) (mul M (mul N P))
  assocInv : {A B C D : V} → (M : H A B) → (N : H B C) → (P : H C D) →
    Cell (𝟙 A) (𝟙 D) (mul M (mul N P)) (mul (mul M N) P)
  left : {A B : V} → (M : H A B) → Cell (𝟙 A) (𝟙 B) (mul (unit A) M) M
  leftInv : {A B : V} → (M : H A B) → Cell (𝟙 A) (𝟙 B) M (mul (unit A) M)
  right : {A B : V} → (M : H A B) → Cell (𝟙 A) (𝟙 B) (mul M (unit B)) M
  rightInv : {A B : V} → (M : H A B) → Cell (𝟙 A) (𝟙 B) M (mul M (unit B))

/-- Composition of globular cells, transporting identity frames (PDF p. 6). -/
def DoubleData.seq {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} {M N P : D.H A B}
    (a : D.Cell (𝟙 A) (𝟙 B) M N) (b : D.Cell (𝟙 A) (𝟙 B) N P) :
    D.Cell (𝟙 A) (𝟙 B) M P := by
  simpa only [Category.id_comp] using D.vcomp a b

/-- All pseudo double category axioms: vertical category laws, the two functors,
interchange, invertible globular constraints natural for ALL squares, pentagon,
and triangle (Definition 2.1 and conventions, PDF pp. 5–6). -/
structure DoubleCoherence {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop where
  vassoc : ∀ {A B C E F G I J : V} {f : A ⟶ C} {g : B ⟶ E}
    {h : C ⟶ F} {k : E ⟶ G} {l : F ⟶ I} {m : G ⟶ J}
    {M : D.H A B} {N : D.H C E} {P : D.H F G} {Q : D.H I J}
    (a : D.Cell f g M N) (b : D.Cell h k N P) (c : D.Cell l m P Q),
    HEq (D.vcomp (D.vcomp a b) c) (D.vcomp a (D.vcomp b c))
  vidLeft : ∀ {A B C E : V} {f : A ⟶ C} {g : B ⟶ E}
    {M : D.H A B} {N : D.H C E} (a : D.Cell f g M N),
    HEq (D.vcomp (D.idCell M) a) a
  vidRight : ∀ {A B C E : V} {f : A ⟶ C} {g : B ⟶ E}
    {M : D.H A B} {N : D.H C E} (a : D.Cell f g M N),
    HEq (D.vcomp a (D.idCell N)) a
  unitId : ∀ A, D.unitCell (𝟙 A) = D.idCell (D.unit A)
  unitComp : ∀ {A B C : V} (f : A ⟶ B) (g : B ⟶ C),
    D.unitCell (f ≫ g) = D.vcomp (D.unitCell f) (D.unitCell g)
  hid : ∀ {A B C : V} (M : D.H A B) (N : D.H B C),
    D.hcomp (D.idCell M) (D.idCell N) = D.idCell (D.mul M N)
  interchange : ∀ {A B C E F G I J K : V}
    {f : A ⟶ E} {g : B ⟶ F} {h : C ⟶ G}
    {i : E ⟶ I} {j : F ⟶ J} {k : G ⟶ K}
    {M : D.H A B} {N : D.H B C} {P : D.H E F} {Q : D.H F G}
    {R : D.H I J} {S : D.H J K}
    (a : D.Cell f g M P) (b : D.Cell g h N Q)
    (c : D.Cell i j P R) (d : D.Cell j k Q S),
    D.vcomp (D.hcomp a b) (D.hcomp c d) = D.hcomp (D.vcomp a c) (D.vcomp b d)
  assocIsoLeft : ∀ {A B C E : V} (M : D.H A B) (N : D.H B C) (P : D.H C E),
    D.seq (D.assoc M N P) (D.assocInv M N P) = D.idCell (D.mul (D.mul M N) P)
  assocIsoRight : ∀ {A B C E : V} (M : D.H A B) (N : D.H B C) (P : D.H C E),
    D.seq (D.assocInv M N P) (D.assoc M N P) = D.idCell (D.mul M (D.mul N P))
  leftIsoLeft : ∀ {A B : V} (M : D.H A B),
    D.seq (D.left M) (D.leftInv M) = D.idCell (D.mul (D.unit A) M)
  leftIsoRight : ∀ {A B : V} (M : D.H A B),
    D.seq (D.leftInv M) (D.left M) = D.idCell M
  rightIsoLeft : ∀ {A B : V} (M : D.H A B),
    D.seq (D.right M) (D.rightInv M) = D.idCell (D.mul M (D.unit B))
  rightIsoRight : ∀ {A B : V} (M : D.H A B),
    D.seq (D.rightInv M) (D.right M) = D.idCell M
  assocNatural : ∀ {A B C E F G I J : V}
    {f : A ⟶ F} {g : B ⟶ G} {h : C ⟶ I} {k : E ⟶ J}
    {M : D.H A B} {N : D.H B C} {P : D.H C E}
    {Q : D.H F G} {R : D.H G I} {S : D.H I J}
    (a : D.Cell f g M Q) (b : D.Cell g h N R) (c : D.Cell h k P S),
    HEq (D.vcomp (D.hcomp (D.hcomp a b) c) (D.assoc Q R S))
      (D.vcomp (D.assoc M N P) (D.hcomp a (D.hcomp b c)))
  leftNatural : ∀ {A B C E : V} {f : A ⟶ C} {g : B ⟶ E}
    {M : D.H A B} {N : D.H C E} (a : D.Cell f g M N),
    HEq (D.vcomp (D.hcomp (D.unitCell f) a) (D.left N)) (D.vcomp (D.left M) a)
  rightNatural : ∀ {A B C E : V} {f : A ⟶ C} {g : B ⟶ E}
    {M : D.H A B} {N : D.H C E} (a : D.Cell f g M N),
    HEq (D.vcomp (D.hcomp a (D.unitCell g)) (D.right N)) (D.vcomp (D.right M) a)
  pentagon : ∀ {A B C E F : V} (M : D.H A B) (N : D.H B C)
    (P : D.H C E) (Q : D.H E F),
    D.seq (D.seq (D.hcomp (D.assoc M N P) (D.idCell Q)) (D.assoc M (D.mul N P) Q))
      (D.hcomp (D.idCell M) (D.assoc N P Q)) =
    D.seq (D.assoc (D.mul M N) P Q) (D.assoc M N (D.mul P Q))
  triangle : ∀ {A B C : V} (M : D.H A B) (N : D.H B C),
    D.seq (D.assoc M (D.unit B) N) (D.hcomp (D.idCell M) (D.left N)) =
      D.hcomp (D.right M) (D.idCell N)

/-- The universal lifting property for the JOINT frame functor, not a single
frame projection (Definition 3.1, PDF pp. 9–10; explicit square form pp. 13–14). -/
def IsCartesian {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B C E : V} {f : A ⟶ C} {g : B ⟶ E} {M : D.H A B} {N : D.H C E}
    (a : D.Cell f g M N) : Prop :=
  ∀ (P Q : V) (h : P ⟶ A) (k : Q ⟶ B) (T : D.H P Q)
    (b : D.Cell (h ≫ f) (k ≫ g) T N),
    ∃! c : D.Cell h k T M, D.vcomp c a = b

/-- Dual universal lifting property for the joint frame functor (PDF pp. 12–14). -/
def IsOpcartesian {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B C E : V} {f : A ⟶ C} {g : B ⟶ E} {M : D.H A B} {N : D.H C E}
    (a : D.Cell f g M N) : Prop :=
  ∀ (P Q : V) (h : C ⟶ P) (k : E ⟶ Q) (T : D.H P Q)
    (b : D.Cell (f ≫ h) (g ≫ k) M T),
    ∃! c : D.Cell h k N T, D.vcomp a c = b

/-- Existence of every joint cartesian lift (Definition 3.1 and §4, PDF pp. 10, 13). -/
def IsFrameFibration {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop :=
  ∀ (A B C E : V) (f : A ⟶ C) (g : B ⟶ E) (N : D.H C E),
    ∃ (M : D.H A B) (a : D.Cell f g M N), IsCartesian D a

/-- Existence of every joint opcartesian lift (PDF pp. 12–13). -/
def IsFrameOpfibration {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop :=
  ∀ (A B C E : V) (f : A ⟶ C) (g : B ⟶ E) (M : D.H A B),
    ∃ (N : D.H C E) (a : D.Cell f g M N), IsOpcartesian D a

/-- Companion with both identities, including unitors in the horizontal zigzag
(4.2)–(4.4), PDF p. 15; Definition A.1, PDF pp. 71–72. -/
structure Companion {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} (f : A ⟶ B) (M : D.H A B) where
  counit : D.Cell f (𝟙 B) M (D.unit B)
  unit : D.Cell (𝟙 A) f (D.unit A) M
  vertical : HEq (D.vcomp unit counit) (D.unitCell f)
  horizontal : D.seq (D.seq (D.leftInv M) (D.hcomp unit counit)) (D.right M) = D.idCell M

/-- Conjoint with both identities, dual to the companion (PDF pp. 15, 71–72). -/
structure Conjoint {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} (f : A ⟶ B) (N : D.H B A) where
  counit : D.Cell (𝟙 B) f N (D.unit B)
  unit : D.Cell f (𝟙 A) (D.unit A) N
  vertical : HEq (D.vcomp unit counit) (D.unitCell f)
  horizontal : D.seq (D.seq (D.rightInv N) (D.hcomp counit unit)) (D.left N) = D.idCell N

/-- Every vertical arrow admits a companion (PDF p. 72). -/
def HasCompanions {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop :=
  ∀ (A B : V) (f : A ⟶ B), ∃ M : D.H A B, Nonempty (Companion D f M)

/-- Every vertical arrow admits a conjoint (PDF p. 72). -/
def HasConjoints {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop :=
  ∀ (A B : V) (f : A ⟶ B), ∃ N : D.H B A, Nonempty (Conjoint D f N)

/-- Nonalgebraic framing; the chosen characterization is (L,R) a fibration
(Definition 4.8, PDF p. 17). Coherence is separately required in the theorem binders. -/
def IsFramed {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) : Prop :=
  IsFrameFibration D

/-- Arbitrary chosen companions on a possibly non-strict double category,
called a pseudo connection pair in Appendix A (PDF p. 72). -/
structure PseudoConnectionPair {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) where
  arrow : {A B : V} → (A ⟶ B) → D.H A B
  comparison : {A B : V} → (f : A ⟶ B) → Companion D f (arrow f)

/-- Arbitrary chosen conjoints, called a pseudo op-connection pair in
Appendix A (PDF p. 72); no strict horizontal composition is imposed. -/
structure PseudoOpConnectionPair {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V) where
  arrow : {A B : V} → (A ⟶ B) → D.H B A
  comparison : {A B : V} → (f : A ⟶ B) → Conjoint D f (arrow f)

/-- Both triangle identities for specified evaluation and coevaluation cells
(Definition 5.2, PDF p. 20). -/
def IsDualPair {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} (M : D.H A B) (N : D.H B A)
    (eta : D.Cell (𝟙 A) (𝟙 A) (D.unit A) (D.mul M N))
    (eps : D.Cell (𝟙 B) (𝟙 B) (D.mul N M) (D.unit B)) : Prop :=
  D.seq (D.seq (D.seq (D.seq (D.leftInv M) (D.hcomp eta (D.idCell M)))
    (D.assoc M N M)) (D.hcomp (D.idCell M) eps)) (D.right M) = D.idCell M ∧
  D.seq (D.seq (D.seq (D.seq (D.rightInv N) (D.hcomp (D.idCell N) eta))
    (D.assocInv N M N)) (D.hcomp eps (D.idCell N))) (D.left N) = D.idCell N

/-- Canonical coevaluation from the two base-change unit cells
(Proposition 5.3, diagram across PDF pp. 20–21). -/
def baseCoevaluation {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} {f : A ⟶ B} {M : D.H A B} {N : D.H B A}
    (c : Companion D f M) (j : Conjoint D f N) :
    D.Cell (𝟙 A) (𝟙 A) (D.unit A) (D.mul M N) :=
  D.seq (D.leftInv (D.unit A)) (D.hcomp c.unit j.unit)

/-- Canonical evaluation from the two base-change counit cells
(Proposition 5.3, PDF p. 21). -/
def baseEvaluation {V : Type u} [Category.{v} V] (D : DoubleData.{u,v,w,x} V)
    {A B : V} {f : A ⟶ B} {M : D.H A B} {N : D.H B A}
    (c : Companion D f M) (j : Conjoint D f N) :
    D.Cell (𝟙 B) (𝟙 B) (D.mul N M) (D.unit B) :=
  D.seq (D.hcomp j.counit c.counit) (D.left (D.unit B))

/-- A thin test double category over any vertical category; all horizontal
arrows and all squares are unique. Used only to check the local interfaces. -/
def thinDoubleData (V : Type u) [Category.{v} V] : DoubleData.{u,v,0,0} V where
  H := fun _ _ => PUnit
  Cell := fun {A B C E} _ _ _ _ => PUnit
  unit := fun _ => PUnit.unit
  mul := fun _ _ => PUnit.unit
  idCell := fun _ => PUnit.unit
  vcomp := fun _ _ => PUnit.unit
  unitCell := fun _ => PUnit.unit
  hcomp := fun _ _ => PUnit.unit
  assoc := fun _ _ _ => PUnit.unit
  assocInv := fun _ _ _ => PUnit.unit
  left := fun _ => PUnit.unit
  leftInv := fun _ => PUnit.unit
  right := fun _ => PUnit.unit
  rightInv := fun _ => PUnit.unit

/-- Sanity check: the complete coherence package is satisfiable, including
for empty vertical categories (the source imposes no nonemptiness). -/
def thinDoubleCoherence (V : Type u) [Category.{v} V] : DoubleCoherence (thinDoubleData V) := by
  constructor <;> intros <;> dsimp only [thinDoubleData, DoubleData.seq] <;> first
  | exact Subsingleton.elim _ _
  | exact heq_of_eq (Subsingleton.elim _ _)

example (V : Type u) [Category.{v} V] (A B : V) :
    (thinDoubleData V).mul (A := A) (B := B) (C := B)
      (PUnit.unit : (thinDoubleData V).H A B)
      ((thinDoubleData V).unit B) = PUnit.unit := rfl

example (V : Type u) [Category.{v} V] (A B : V) (f : A ⟶ B) :
    Companion (thinDoubleData V) f PUnit.unit :=
  ⟨PUnit.unit, PUnit.unit, HEq.rfl, rfl⟩

example (V : Type u) [Category.{v} V] (A B : V) (f : A ⟶ B) :
    Conjoint (thinDoubleData V) f PUnit.unit :=
  ⟨PUnit.unit, PUnit.unit, HEq.rfl, rfl⟩

example (V : Type u) [Category.{v} V] (A B : V) :
    IsDualPair (thinDoubleData V) (A := A) (B := B)
      (PUnit.unit : (thinDoubleData V).H A B)
      PUnit.unit PUnit.unit PUnit.unit := ⟨rfl, rfl⟩

example (V : Type u) [Category.{v} V] : IsFrameFibration (thinDoubleData V) := by
  intro A B C E f g N
  refine ⟨PUnit.unit, PUnit.unit, ?_⟩
  intro P Q h k T b
  refine ⟨PUnit.unit, ?_, ?_⟩
  · dsimp only [thinDoubleData]
    exact Subsingleton.elim _ _
  · intro c hc
    dsimp only [thinDoubleData]
    exact Subsingleton.elim _ _

example (V : Type u) [Category.{v} V] : IsFrameOpfibration (thinDoubleData V) := by
  intro A B C E f g M
  refine ⟨PUnit.unit, PUnit.unit, ?_⟩
  intro P Q h k T b
  refine ⟨PUnit.unit, ?_, ?_⟩
  · dsimp only [thinDoubleData]
    exact Subsingleton.elim _ _
  · intro c hc
    dsimp only [thinDoubleData]
    exact Subsingleton.elim _ _

end QAlgorithms.Papers.Independent.Intakethird100.P60


