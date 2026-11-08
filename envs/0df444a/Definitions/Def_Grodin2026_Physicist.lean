-- Prove2me | Definitions.Def_Grodin2026_Physicist
-- name    : Grodin2026_Physicist
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T17:17:16.141326+00:00
-- url     : https://prove2.me/theorems/06ef4c7d-aa0d-4cf6-bf59-6cc8bf2b83a5
-- title:
--   Sections 2 & 3: Modalities, Fracture and Gluing of Value and Computation Types, Cost Algebras, Potential, and the Sealing Monad
-- statement:
--   Formalizes Sections 2 and 3 of Grodin, Chu, Li, Hoffmann & Harper (2026): the synthetic abstract modality `OpenModal` ($\bigcirc X \coloneqq \mathsf{abs} \to X$, Definition 2.1), concrete pushout modality `ClosedModal` ($\bullet X$, Definition 2.2), specification types `SpecType` (Definition 3.1), the two-world Kripke universe of phased value types `ValType` ($\mathcal{V}$) with pullbacks and gluing `GlueVal` (Theorem 2.3, Definition 2.5), batched queue value abstraction `BatchedQueueVal` (Example 2.8), preordered cost algebras `CostAlg` and homomorphisms `CostHom` (Definitions 2.11-2.12), phased computation types `CompType` ($\mathcal{C}$) with computation modalities `OpenComp` and `ClosedComp` (Definitions 2.9-2.10), pullback gluing `GlueComp` (Theorem 2.15), `AbstractionComp` (Definition 2.17), `PotentialType` ($\mathsf{Potential}(\Phi : X \to \mathbb{N})$, Definition 2.21), cost-aware batched queues `BatchedQueueComp` (Examples 2.20 & 3.3), the sealing monad `SealComp` ($\mathsf{S}A$), and lax homomorphisms `LaxCompHom` ($A \mathrel{\multimap\!\!\!\!+} B$, §3.2).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Sections 2-3, pp. 5-13.

import Mathlib.Logic.Equiv.Defs

/-!
# The Physicist's View & Loss of Energy Due to Abstraction (Grodin et al., 2026, §§2–3)

Constructive Lean 4 formalization of Sections 2 and 3 of:
Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper (2026),
*Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost*
(`arXiv:2607.08547v2`).

This module formalizes:
- **§2.1:** The synthetic abstract ($\bigcirc X := \mathsf{abs} \to X$, Definition 2.1) and
  concrete ($\bullet X$, Definition 2.2) modalities, the two-world Kripke universe of phased
  value types $\mathcal{V}$ over $\{\mathsf{abs} \vdash \top\}$, pullbacks and gluing
  $\mathsf{Glue}(X_\bullet, X_\circ, \chi_\bullet)$ (Theorem 2.3, Corollary 2.4),
  $\mathsf{Abstraction}(\chi : X_\top \to X_{\mathsf{abs}})$ (Definition 2.5, Corollary 2.6,
  Lemma 2.7), and the batched queue value abstraction (Example 2.8).
- **§2.2:** Preordered cost algebras (Definition 2.11), cost algebra homomorphisms
  $A \multimap B$ (Definition 2.12), computation modalities $\bigcirc A$ and $\bullet A$
  (Definitions 2.9–2.10, Lemmas 2.13–2.14), the universe of phased computation types
  $\mathcal{C}$, fracture and gluing $\mathsf{Glue}(A_\bullet, A_\circ, \alpha_\bullet)$
  (Theorem 2.15, Corollary 2.16), $\mathsf{Abstraction}(\alpha : A_\top \multimap A_{\mathsf{abs}})$
  (Definition 2.17, Corollary 2.18, Lemma 2.19), and the cost-aware ephemeral batched queue
  (Example 2.20).
- **§2.3:** $\mathsf{Potential}(\Phi : X \to \mathbb{C}) := \mathsf{Abstraction}(\varphi(\Phi) : FX \multimap FX)$
  (Definition 2.21, Lemma 2.22, Corollary 2.23, Example 2.24).
- **§3.1–3.2:** Specification types $\{X \mid \P \hookrightarrow x_\circ\}$ (Definition 3.1),
  behavioral and amortized queue interfaces (Examples 3.2–3.3), the sealing monad
  $\mathsf{S}A = \bullet A \times^{\le}_{\bullet \bigcirc A} \bigcirc A$, and lax homomorphisms
  $A \mathrel{\multimap\!\!\!\!+} B := A \multimap \mathsf{S}B$ (Lemma 3.5).
-/

namespace Grodin2026

universe u v

/-! ## §2.1 Synthetic Phase Modalities and Specification Types -/

/-- **Definition 2.1 (Abstract Modality, synthetic form):**
For a phase proposition `abs : Prop`, the abstract (open) modality is
$\bigcirc X := \mathsf{abs} \to X$. -/
def OpenModal (abs : Prop) (X : Type u) : Type u :=
  abs → X

/-- Unit $\eta^\circ_X : X \to \bigcirc X$ of the synthetic abstract modality (Definition 2.1). -/
def etaOpen (abs : Prop) {X : Type u} (x : X) : OpenModal abs X :=
  fun _ => x

/-- Relation identifying all elements of `X ⊕ PLift abs` whenever `abs` holds,
used to construct the pushout $\bullet X$ (Definition 2.2). -/
inductive ClosedRel (abs : Prop) (X : Type u) : Sum X (PLift abs) → Sum X (PLift abs) → Prop where
  | refl (s : Sum X (PLift abs)) : ClosedRel abs X s s
  | glue (x : X) (h : abs) : ClosedRel abs X (Sum.inl x) (Sum.inr ⟨h⟩)
  | symm {s₁ s₂ : Sum X (PLift abs)} : ClosedRel abs X s₁ s₂ → ClosedRel abs X s₂ s₁
  | trans {s₁ s₂ s₃ : Sum X (PLift abs)} :
      ClosedRel abs X s₁ s₂ → ClosedRel abs X s₂ s₃ → ClosedRel abs X s₁ s₃

/-- **Definition 2.2 (Concrete Modality, synthetic pushout):**
$\bullet X$ is the pushout of $X \leftarrow \mathsf{abs} \times X \to \mathsf{abs}$, collapsing $X$
to a point under the phase assumption `abs`. -/
def ClosedModal (abs : Prop) (X : Type u) : Type u :=
  Quot (ClosedRel abs X)

/-- Unit $\eta^\bullet_X : X \to \bullet X$ of the concrete modality (Definition 2.2). -/
def etaClosed (abs : Prop) {X : Type u} (x : X) : ClosedModal abs X :=
  Quot.mk (ClosedRel abs X) (Sum.inl x)

/-- Phase collapse point $* : \mathsf{abs} \to \bullet X$ of the concrete modality (Definition 2.2). -/
def starClosed (abs : Prop) {X : Type u} (h : abs) : ClosedModal abs X :=
  Quot.mk (ClosedRel abs X) (Sum.inr ⟨h⟩)

/-- Path constructor $\eta^\bullet_X(x) = *(\mathsf{abs})$ in $\bullet X$ (Definition 2.2). -/
theorem closed_glue (abs : Prop) {X : Type u} (x : X) (h : abs) :
    etaClosed abs x = starClosed abs (X := X) h :=
  Quot.sound (ClosedRel.glue x h)

/-- **Definition 3.1 (Specification Type):**
For a phase proposition `P : Prop` and phase-indexed specification `x_circ : P → X`,
$\{ X \mid P \hookrightarrow x_\circ \} := \sum_{x : X} ((h : P) \to x = x_\circ(h))$. -/
def SpecType (P : Prop) {X : Type u} (x_circ : P → X) : Type u :=
  { x : X // ∀ h : P, x = x_circ h }

/-! ## §2.1 Phased Value Types $\mathcal{V}$, Modalities, Fracture, and Gluing -/

/-- A phased value type $X : \mathcal{V}$ in the Kripke presheaf semantics over the two worlds
$\{\mathsf{abs} \vdash \top\}$ (§2.1, p. 7), consisting of a concrete type $\llbracket X \rrbracket_\top$,
an abstract type $\llbracket X \rrbracket_{\mathsf{abs}}$, and a transition/abstraction function
$\llbracket X \rrbracket_\vdash : \llbracket X \rrbracket_\top \to \llbracket X \rrbracket_{\mathsf{abs}}$. -/
structure ValType where
  top : Type
  abs : Type
  chi : top → abs

/-- A morphism $f : X \to Y$ of phased value types (§2.1, p. 7 & Corollary 2.4):
a pair of maps $(f_\top, f_{\mathsf{abs}})$ commuting with the transition maps
($\chi_Y \circ f_\top = f_{\mathsf{abs}} \circ \chi_X$). -/
@[ext]
structure ValHom (X Y : ValType) where
  f_top : X.top → Y.top
  f_abs : X.abs → Y.abs
  comm : ∀ x : X.top, Y.chi (f_top x) = f_abs (X.chi x)

/-- Identity morphism on $X : \mathcal{V}$. -/
def ValHom.id (X : ValType) : ValHom X X where
  f_top := _root_.id
  f_abs := _root_.id
  comm := fun _ => rfl

/-- Composition of morphisms in $\mathcal{V}$. -/
def ValHom.comp {X Y Z : ValType} (g : ValHom Y Z) (f : ValHom X Y) : ValHom X Z where
  f_top := g.f_top ∘ f.f_top
  f_abs := g.f_abs ∘ f.f_abs
  comm := fun x => by
     calc Z.chi (g.f_top (f.f_top x))
      _ = g.f_abs (Y.chi (f.f_top x)) := g.comm (f.f_top x)
      _ = g.f_abs (f.f_abs (X.chi x)) := congrArg g.f_abs (f.comm x)

/-- Equivalence of phased value types $X \simeq Y$ in $\mathcal{V}$. -/
structure ValEquiv (X Y : ValType) where
  toHom : ValHom X Y
  invHom : ValHom Y X
  left_inv : invHom.comp toHom = ValHom.id X
  right_inv : toHom.comp invHom = ValHom.id Y

/-- Reflexivity of `ValEquiv`. -/
def ValEquiv.refl (X : ValType) : ValEquiv X X where
  toHom := ValHom.id X
  invHom := ValHom.id X
  left_inv := rfl
  right_inv := rfl

/-- Symmetry of `ValEquiv`. -/
def ValEquiv.symm {X Y : ValType} (e : ValEquiv X Y) : ValEquiv Y X where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- **Definition 2.1 (Abstract Modality on $\mathcal{V}$):**
$\bigcirc X$ isolates the client-facing abstract component $X_{\mathsf{abs}}$ at both worlds,
with identity transition. -/
def OpenVal (X : ValType) : ValType where
  top := X.abs
  abs := X.abs
  chi := _root_.id

/-- Modal unit $\eta^\circ_X : X \to \bigcirc X$ (Definition 2.1). -/
def etaOpenVal (X : ValType) : ValHom X (OpenVal X) where
  f_top := X.chi
  f_abs := _root_.id
  comm := fun _ => rfl

/-- Functorial action of $\bigcirc$ on value morphisms. -/
def OpenVal.map {X Y : ValType} (f : ValHom X Y) : ValHom (OpenVal X) (OpenVal Y) where
  f_top := f.f_abs
  f_abs := f.f_abs
  comm := fun _ => rfl

/-- **Definition 2.2 (Concrete Modality on $\mathcal{V}$):**
$\bullet X$ isolates the private concrete component $X_\top$ at the $\top$-world and collapses the
$\mathsf{abs}$-world to the terminal unit type `PUnit`. -/
def ClosedVal (X : ValType) : ValType where
  top := X.top
  abs := PUnit
  chi := fun _ => PUnit.unit

/-- Modal unit $\eta^\bullet_X : X \to \bullet X$ (Definition 2.2). -/
def etaClosedVal (X : ValType) : ValHom X (ClosedVal X) where
  f_top := _root_.id
  f_abs := fun _ => PUnit.unit
  comm := fun _ => rfl

/-- Functorial action of $\bullet$ on value morphisms. -/
def ClosedVal.map {X Y : ValType} (f : ValHom X Y) : ValHom (ClosedVal X) (ClosedVal Y) where
  f_top := f.f_top
  f_abs := fun _ => PUnit.unit
  comm := fun _ => rfl

/-- Pullback $A \times_C B$ of $f : A \to C$ and $g : B \to C$ in $\mathcal{V}$. -/
def ValPullback {A B C : ValType} (f : ValHom A C) (g : ValHom B C) : ValType where
  top := { p : A.top × B.top // f.f_top p.1 = g.f_top p.2 }
  abs := { p : A.abs × B.abs // f.f_abs p.1 = g.f_abs p.2 }
  chi := fun ⟨(a, b), h⟩ =>
    ⟨(A.chi a, B.chi b), by
      calc f.f_abs (A.chi a)
        _ = C.chi (f.f_top a) := (f.comm a).symm
        _ = C.chi (g.f_top b) := congrArg C.chi h
        _ = g.f_abs (B.chi b) := g.comm b⟩

/-- **Theorem 2.3 (Gluing in $\mathcal{V}$):**
Given $X_\bullet, X_\circ : \mathcal{V}$ and an abstraction morphism
$\chi_\bullet : X_\bullet \to \bullet X_\circ$, the glued value type is the pullback
$\mathsf{Glue}(X_\bullet, X_\circ, \chi_\bullet) := X_\bullet \times_{\bullet X_\circ} X_\circ$. -/
def GlueVal (X_cl X_op : ValType) (chi_cl : ValHom X_cl (ClosedVal X_op)) : ValType :=
  ValPullback chi_cl (etaClosedVal X_op)

/-- Canonical fracture of a phased value type $X : \mathcal{V}$ into the pullback gluing
$\mathsf{Glue}(\bullet X, \bigcirc X, \bullet \eta^\circ_X)$ (Theorem 2.3). -/
def FractureGlueVal (X : ValType) : ValType :=
  GlueVal (ClosedVal X) (OpenVal X) (ClosedVal.map (etaOpenVal X))

/-- Constant embedding of a single-world type `T : Type` into $\mathcal{V}$. -/
def ConstVal (T : Type) : ValType where
  top := T
  abs := T
  chi := _root_.id

/-- **Definition 2.5 ($\mathsf{Abstraction}$ on Value Types):**
Given a function $\chi : X_\top \to X_{\mathsf{abs}}$,
$\mathsf{Abstraction}(\chi) := \mathsf{Glue}(\bullet X_\top, \bigcirc X_{\mathsf{abs}}, \bullet(\eta^\circ \circ \chi))$. -/
def GlueAbstractionVal (X_top X_abs : Type) (chi : X_top → X_abs) : ValType :=
  GlueVal
    (ClosedVal (ConstVal X_top))
    (OpenVal (ConstVal X_abs))
    (ClosedVal.map ⟨chi, chi, fun _ => rfl⟩)

/-- Direct representation of $\mathsf{Abstraction}(\chi : X_\top \to X_{\mathsf{abs}})$ in $\mathcal{V}$. -/
def AbstractionVal (X_top X_abs : Type) (chi : X_top → X_abs) : ValType where
  top := X_top
  abs := X_abs
  chi := chi

/-- **Example 2.8 (Batched Queue Representation and Value Abstraction):**
A batched queue represents a queue of elements of type `α` as a pair of lists $(l_1, l_2)$,
where $l_1$ is the front list and $l_2$ is the reversed back list. -/
abbrev BatchedQueueRep (α : Type) : Type :=
  List α × List α

/-- Abstraction function $\chi(l_1, l_2) := l_1 \mathbin{+\!+} \mathrm{reverse}\,l_2$ (Example 2.8). -/
def queueChi {α : Type} (q : BatchedQueueRep α) : List α :=
  q.1 ++ q.2.reverse

/-- Value type $X := \mathsf{Abstraction}(\chi : \mathsf{List}\,\alpha \times \mathsf{List}\,\alpha \to \mathsf{List}\,\alpha)$
for batched queues (Example 2.8). -/
def BatchedQueueVal (α : Type) : ValType :=
  AbstractionVal (BatchedQueueRep α) (List α) queueChi

/-- Concrete enqueue operation $\mathsf{enqueue}_\top\,n\,(l_1, l_2) := (l_1, n :: l_2)$ (Example 2.8). -/
def enqueueValTop {α : Type} (n : α) (q : BatchedQueueRep α) : BatchedQueueRep α :=
  (q.1, n :: q.2)

/-- Abstract enqueue specification $\mathsf{enqueue}_{\mathsf{abs}}\,n\,l := l \mathbin{+\!+} [n]$ (Example 2.8). -/
def enqueueValAbs {α : Type} (n : α) (l : List α) : List α :=
  l ++ [n]

/-! ## §2.2 Computation Types as Cost Algebras, Modalities, Fracture, and Gluing -/

/-- **Definition 2.11 (Cost Algebra):**
A cost algebra $A$ consists of a preordered carrier type $(UA, \le_A)$ together with a cost-charging
action $\mathsf{charge}_A\langle - \rangle : \mathbb{N} \to UA \to UA$ satisfying the monoid action
laws $\mathsf{charge}_A\langle 0 \rangle(a) = a$ and
$\mathsf{charge}_A\langle c_1 + c_2 \rangle(a) = \mathsf{charge}_A\langle c_1 \rangle(\mathsf{charge}_A\langle c_2 \rangle(a))$,
monotone in both the cost and the carrier element. -/
structure CostAlg where
  carrier : Type
  le : carrier → carrier → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  charge : Nat → carrier → carrier
  charge_zero : ∀ a, charge 0 a = a
  charge_add : ∀ c₁ c₂ a, charge (c₁ + c₂) a = charge c₁ (charge c₂ a)
  charge_mono_cost : ∀ {c₁ c₂} (a : carrier), c₁ ≤ c₂ → le (charge c₁ a) (charge c₂ a)
  charge_mono_val : ∀ (c : Nat) {a₁ a₂ : carrier}, le a₁ a₂ → le (charge c a₁) (charge c a₂)

/-- **Definition 2.12 (Cost Algebra Homomorphism):**
A homomorphism $f : A \multimap B$ of cost algebras is a monotone map $Uf : UA \to UB$ that
strictly preserves the cost effect:
$\forall c\,a,\; Uf(\mathsf{charge}_A\langle c \rangle(a)) = \mathsf{charge}_B\langle c \rangle(Uf(a))$. -/
@[ext]
structure CostHom (A B : CostAlg) where
  fn : A.carrier → B.carrier
  map_charge : ∀ (c : Nat) (a : A.carrier), fn (A.charge c a) = B.charge c (fn a)
  mono : ∀ {a₁ a₂ : A.carrier}, A.le a₁ a₂ → B.le (fn a₁) (fn a₂)

/-- Identity cost algebra homomorphism $\mathrm{id}_A : A \multimap A$. -/
def CostHom.id (A : CostAlg) : CostHom A A where
  fn := _root_.id
  map_charge := fun _ _ => rfl
  mono := fun h => h

/-- Composition of cost algebra homomorphisms $(g \circ f) : A \multimap C$. -/
def CostHom.comp {A B C : CostAlg} (g : CostHom B C) (f : CostHom A B) : CostHom A C where
  fn := g.fn ∘ f.fn
  map_charge := fun c a => by
    calc g.fn (f.fn (A.charge c a))
      _ = g.fn (B.charge c (f.fn a)) := congrArg g.fn (f.map_charge c a)
      _ = C.charge c (g.fn (f.fn a)) := g.map_charge c (f.fn a)
  mono := fun h => g.mono (f.mono h)

/-- Cost-charging action $\mathsf{charge}_A\langle c \rangle : A \multimap A$ as a cost algebra
homomorphism, using commutativity of $(\mathbb{N}, 0, +)$ (Remark 4.2). -/
def chargeCostHom (A : CostAlg) (c : Nat) : CostHom A A where
  fn := A.charge c
  map_charge := fun c' a => by
    calc A.charge c (A.charge c' a)
      _ = A.charge (c + c') a := (A.charge_add c c' a).symm
      _ = A.charge (c' + c) a := by rw [Nat.add_comm]
      _ = A.charge c' (A.charge c a) := A.charge_add c' c a
  mono := fun h => A.charge_mono_val c h

/-- Free cost algebra $FX$ on a value type $X$ (§2, p. 4):
elements are pairs $(c, x) : \mathbb{N} \times X$ representing $\mathsf{charge}\langle c \rangle(\mathsf{ret}\,x)$,
ordered by $(c_1, x_1) \le_{FX} (c_2, x_2) \iff c_1 \le c_2 \wedge x_1 = x_2$. -/
def FreeCostAlg (X : Type) : CostAlg where
  carrier := Nat × X
  le := fun p q => p.1 ≤ q.1 ∧ p.2 = q.2
  le_refl := fun p => ⟨Nat.le_refl p.1, rfl⟩
  le_trans := fun ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ => ⟨Nat.le_trans h₁ h₂, Eq.trans e₁ e₂⟩
  charge := fun c p => (c + p.1, p.2)
  charge_zero := fun ⟨c, x⟩ => by simp
  charge_add := fun c₁ c₂ ⟨c, x⟩ => by simp [Nat.add_assoc]
  charge_mono_cost := fun ⟨c, _⟩ h => ⟨Nat.add_le_add_right h c, rfl⟩
  charge_mono_val := fun c {_ _} ⟨h, e⟩ => ⟨Nat.add_le_add_left h c, e⟩

/-- Return $\mathsf{ret}\,x := (0, x) : U(FX)$. -/
def retFree {X : Type} (x : X) : (FreeCostAlg X).carrier :=
  (0, x)

/-- Terminal computation type $1_{\mathcal{C}}$ (`UnitCostAlg`), where all costs are trivial. -/
def UnitCostAlg : CostAlg where
  carrier := PUnit
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ => trivial
  charge := fun _ _ => PUnit.unit
  charge_zero := fun _ => rfl
  charge_add := fun _ _ _ => rfl
  charge_mono_cost := fun _ _ => trivial
  charge_mono_val := fun _ {_ _} _ => trivial

/-- Monoidal unit $\top := F(1)$ of the LNL layer (§2, p. 4), whose carrier is $\mathbb{N} \times 1$
tracking pure accumulated cost. -/
def TopCostAlg : CostAlg :=
  FreeCostAlg PUnit

/-- Pullback $A \times_C B$ of cost algebras along homomorphisms $f : A \multimap C$ and
$g : B \multimap C$. -/
def PullbackCostAlg {A B C : CostAlg} (f : CostHom A C) (g : CostHom B C) : CostAlg where
  carrier := { p : A.carrier × B.carrier // f.fn p.1 = g.fn p.2 }
  le := fun p q => A.le p.1.1 q.1.1 ∧ B.le p.1.2 q.1.2
  le_refl := fun p => ⟨A.le_refl p.1.1, B.le_refl p.1.2⟩
  le_trans := fun ⟨ha₁, hb₁⟩ ⟨ha₂, hb₂⟩ => ⟨A.le_trans ha₁ ha₂, B.le_trans hb₁ hb₂⟩
  charge := fun c ⟨(a, b), h⟩ =>
    ⟨(A.charge c a, B.charge c b), by
      calc f.fn (A.charge c a)
        _ = C.charge c (f.fn a) := f.map_charge c a
        _ = C.charge c (g.fn b) := congrArg (C.charge c) h
        _ = g.fn (B.charge c b) := (g.map_charge c b).symm⟩
  charge_zero := fun ⟨(a, b), _⟩ => Subtype.ext (Prod.ext (A.charge_zero a) (B.charge_zero b))
  charge_add := fun c₁ c₂ ⟨(a, b), _⟩ =>
    Subtype.ext (Prod.ext (A.charge_add c₁ c₂ a) (B.charge_add c₁ c₂ b))
  charge_mono_cost := fun ⟨(a, b), _⟩ h => ⟨A.charge_mono_cost a h, B.charge_mono_cost b h⟩
  charge_mono_val := fun c {p₁ p₂} ⟨ha, hb⟩ => by
    rcases p₁ with ⟨⟨a₁, b₁⟩, _⟩
    rcases p₂ with ⟨⟨a₂, b₂⟩, _⟩
    exact ⟨A.charge_mono_val c ha, B.charge_mono_val c hb⟩

/-- Comma cost algebra $A \times^{\le}_C B$ along $f : A \multimap C$ and $g : B \multimap C$ (§3.2, p. 13):
elements are pairs $(a, b) : UA \times UB$ satisfying the inequality $f(a) \le_C g(b)$. -/
def CommaCostAlg {A B C : CostAlg} (f : CostHom A C) (g : CostHom B C) : CostAlg where
  carrier := { p : A.carrier × B.carrier // C.le (f.fn p.1) (g.fn p.2) }
  le := fun p q => A.le p.1.1 q.1.1 ∧ B.le p.1.2 q.1.2
  le_refl := fun p => ⟨A.le_refl p.1.1, B.le_refl p.1.2⟩
  le_trans := fun ⟨ha₁, hb₁⟩ ⟨ha₂, hb₂⟩ => ⟨A.le_trans ha₁ ha₂, B.le_trans hb₁ hb₂⟩
  charge := fun c ⟨(a, b), h⟩ =>
    ⟨(A.charge c a, B.charge c b), by
      rw [f.map_charge c a, g.map_charge c b]
      exact C.charge_mono_val c h⟩
  charge_zero := fun ⟨(a, b), _⟩ => Subtype.ext (Prod.ext (A.charge_zero a) (B.charge_zero b))
  charge_add := fun c₁ c₂ ⟨(a, b), _⟩ =>
    Subtype.ext (Prod.ext (A.charge_add c₁ c₂ a) (B.charge_add c₁ c₂ b))
  charge_mono_cost := fun ⟨(a, b), _⟩ h => ⟨A.charge_mono_cost a h, B.charge_mono_cost b h⟩
  charge_mono_val := fun c {p₁ p₂} ⟨ha, hb⟩ => by
    rcases p₁ with ⟨⟨a₁, b₁⟩, _⟩
    rcases p₂ with ⟨⟨a₂, b₂⟩, _⟩
    exact ⟨A.charge_mono_val c ha, B.charge_mono_val c hb⟩

/-- A phased computation type $A : \mathcal{C}$ in the two-world Kripke model over
$\{\mathsf{abs} \vdash \top\}$ (§2.2, Theorem 2.15 & §4.1, p. 14):
consists of a concrete cost algebra $A_\top$, an abstract cost algebra $A_{\mathsf{abs}}$,
and an abstraction homomorphism $\alpha_A : A_\top \multimap A_{\mathsf{abs}}$ that may emit potential. -/
structure CompType where
  top : CostAlg
  abs : CostAlg
  alpha : CostHom top abs

/-- Underlying phased value type $UA : \mathcal{V}$ of a computation type $A : \mathcal{C}$
(Definition 2.11 & Lemma 2.13). -/
def ForgetComp (A : CompType) : ValType where
  top := A.top.carrier
  abs := A.abs.carrier
  chi := A.alpha.fn

/-- **Definition 2.12 & Corollary 2.16 (Computation Homomorphism in $\mathcal{C}$):**
A homomorphism $f : A \multimap B$ between phased computation types consists of a concrete
homomorphism $f_\top : A_\top \multimap B_\top$ and an abstract homomorphism
$f_{\mathsf{abs}} : A_{\mathsf{abs}} \multimap B_{\mathsf{abs}}$ commuting strictly with the
abstraction homomorphisms ($\alpha_B \circ f_\top = f_{\mathsf{abs}} \circ \alpha_A$). -/
@[ext]
structure CompHom (A B : CompType) where
  hom_top : CostHom A.top B.top
  hom_abs : CostHom A.abs B.abs
  comm : ∀ a : A.top.carrier, B.alpha.fn (hom_top.fn a) = hom_abs.fn (A.alpha.fn a)

/-- Underlying value morphism $Uf : UA \to UB$ of a computation homomorphism $f : A \multimap B$. -/
def ForgetCompHom {A B : CompType} (f : CompHom A B) : ValHom (ForgetComp A) (ForgetComp B) where
  f_top := f.hom_top.fn
  f_abs := f.hom_abs.fn
  comm := f.comm

/-- Identity computation homomorphism $\mathrm{id}_A : A \multimap A$. -/
def CompHom.id (A : CompType) : CompHom A A where
  hom_top := CostHom.id A.top
  hom_abs := CostHom.id A.abs
  comm := fun _ => rfl

/-- Composition of computation homomorphisms $(g \circ f) : A \multimap C$. -/
def CompHom.comp {A B C : CompType} (g : CompHom B C) (f : CompHom A B) : CompHom A C where
  hom_top := g.hom_top.comp f.hom_top
  hom_abs := g.hom_abs.comp f.hom_abs
  comm := fun a => by
    calc C.alpha.fn (g.hom_top.fn (f.hom_top.fn a))
      _ = g.hom_abs.fn (B.alpha.fn (f.hom_top.fn a)) := g.comm (f.hom_top.fn a)
      _ = g.hom_abs.fn (f.hom_abs.fn (A.alpha.fn a)) := congrArg g.hom_abs.fn (f.comm a)

/-- Equivalence of computation types $A \simeq B$ in $\mathcal{C}$. -/
structure CompEquiv (A B : CompType) where
  toHom : CompHom A B
  invHom : CompHom B A
  left_inv : invHom.comp toHom = CompHom.id A
  right_inv : toHom.comp invHom = CompHom.id B

/-- Reflexivity of `CompEquiv`. -/
def CompEquiv.refl (A : CompType) : CompEquiv A A where
  toHom := CompHom.id A
  invHom := CompHom.id A
  left_inv := rfl
  right_inv := rfl

/-- Symmetry of `CompEquiv`. -/
def CompEquiv.symm {A B : CompType} (e : CompEquiv A B) : CompEquiv B A where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

theorem CompHom.comp_assoc {A B C D : CompType}
    (h : CompHom C D) (g : CompHom B C) (f : CompHom A B) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem CompHom.id_comp {A B : CompType} (f : CompHom A B) :
    (CompHom.id B).comp f = f := rfl

theorem CompHom.comp_id {A B : CompType} (f : CompHom A B) :
    f.comp (CompHom.id A) = f := rfl

/-- Transitivity of `CompEquiv`. -/
def CompEquiv.trans {A B C : CompType} (e₁ : CompEquiv A B) (e₂ : CompEquiv B C) : CompEquiv A C where
  toHom := e₂.toHom.comp e₁.toHom
  invHom := e₁.invHom.comp e₂.invHom
  left_inv := by
    calc (e₁.invHom.comp e₂.invHom).comp (e₂.toHom.comp e₁.toHom)
      _ = e₁.invHom.comp ((e₂.invHom.comp e₂.toHom).comp e₁.toHom) := rfl
      _ = e₁.invHom.comp ((CompHom.id B).comp e₁.toHom) := by rw [e₂.left_inv]
      _ = e₁.invHom.comp e₁.toHom := rfl
      _ = CompHom.id A := e₁.left_inv
  right_inv := by
    calc (e₂.toHom.comp e₁.toHom).comp (e₁.invHom.comp e₂.invHom)
      _ = e₂.toHom.comp ((e₁.toHom.comp e₁.invHom).comp e₂.invHom) := rfl
      _ = e₂.toHom.comp ((CompHom.id B).comp e₂.invHom) := by rw [e₁.right_inv]
      _ = e₂.toHom.comp e₂.invHom := rfl
      _ = CompHom.id C := e₂.right_inv

/-- **Definition 2.9 (Abstract Modality on Computation Types):**
$\bigcirc A$ isolates the abstract cost algebra $A_{\mathsf{abs}}$ at both worlds. -/
def OpenComp (A : CompType) : CompType where
  top := A.abs
  abs := A.abs
  alpha := CostHom.id A.abs

/-- Modal unit $\eta^\circ_A : A \multimap \bigcirc A$ (Definition 2.9). -/
def etaOpenComp (A : CompType) : CompHom A (OpenComp A) where
  hom_top := A.alpha
  hom_abs := CostHom.id A.abs
  comm := fun _ => rfl

/-- Functorial action of $\bigcirc$ on computation homomorphisms. -/
def OpenComp.map {A B : CompType} (f : CompHom A B) : CompHom (OpenComp A) (OpenComp B) where
  hom_top := f.hom_abs
  hom_abs := f.hom_abs
  comm := fun _ => rfl

/-- Unique homomorphism into `UnitCostAlg`. -/
def toUnitCostHom (A : CostAlg) : CostHom A UnitCostAlg where
  fn := fun _ => PUnit.unit
  map_charge := fun _ _ => rfl
  mono := fun _ => trivial

/-- **Definition 2.10 (Concrete Modality on Computation Types):**
$\bullet A$ retains $A_\top$ in the concrete world and collapses the abstract world to $1_{\mathcal{C}}$. -/
def ClosedComp (A : CompType) : CompType where
  top := A.top
  abs := UnitCostAlg
  alpha := toUnitCostHom A.top

/-- Modal unit $\eta^\bullet_A : A \multimap \bullet A$ (Definition 2.10). -/
def etaClosedComp (A : CompType) : CompHom A (ClosedComp A) where
  hom_top := CostHom.id A.top
  hom_abs := toUnitCostHom A.abs
  comm := fun _ => rfl

/-- Functorial action of $\bullet$ on computation homomorphisms. -/
def ClosedComp.map {A B : CompType} (f : CompHom A B) : CompHom (ClosedComp A) (ClosedComp B) where
  hom_top := f.hom_top
  hom_abs := toUnitCostHom UnitCostAlg
  comm := fun _ => rfl

/-- Pullback $A \times_C B$ of computation types along $f : A \multimap C$ and $g : B \multimap C$
(Lemma 2.14 & Theorem 2.15). -/
def CompPullback {A B C : CompType} (f : CompHom A C) (g : CompHom B C) : CompType where
  top := PullbackCostAlg f.hom_top g.hom_top
  abs := PullbackCostAlg f.hom_abs g.hom_abs
  alpha := {
    fn := fun ⟨(a, b), h⟩ =>
      ⟨(A.alpha.fn a, B.alpha.fn b), by
        calc f.hom_abs.fn (A.alpha.fn a)
          _ = C.alpha.fn (f.hom_top.fn a) := (f.comm a).symm
          _ = C.alpha.fn (g.hom_top.fn b) := congrArg C.alpha.fn h
          _ = g.hom_abs.fn (B.alpha.fn b) := g.comm b⟩
    map_charge := fun c ⟨(a, b), _⟩ =>
      Subtype.ext (Prod.ext (A.alpha.map_charge c a) (B.alpha.map_charge c b))
    mono := fun ⟨ha, hb⟩ => ⟨A.alpha.mono ha, B.alpha.mono hb⟩
  }

/-- **Theorem 2.15 (Gluing of Computation Types):**
$\mathsf{Glue}(A_\bullet, A_\circ, \alpha_\bullet) := A_\bullet \times_{\bullet A_\circ} A_\circ$. -/
def GlueComp (A_cl A_op : CompType) (alpha_cl : CompHom A_cl (ClosedComp A_op)) : CompType :=
  CompPullback alpha_cl (etaClosedComp A_op)

/-- Canonical fracture and gluing $\mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)$ of a
computation type $A : \mathcal{C}$ (Theorem 2.15). -/
def FractureGlueComp (A : CompType) : CompType :=
  GlueComp (ClosedComp A) (OpenComp A) (ClosedComp.map (etaOpenComp A))

/-- Constant embedding of a single-world cost algebra $A$ into $\mathcal{C}$. -/
def ConstComp (A : CostAlg) : CompType where
  top := A
  abs := A
  alpha := CostHom.id A

/-- Free phased computation type $FX : \mathcal{C}$ on a single-world value type $X$. -/
def FreeComp (X : Type) : CompType :=
  ConstComp (FreeCostAlg X)

/-- **Definition 2.17 ($\mathsf{Abstraction}$ on Computation Types, Pullback Gluing Form):**
$\mathsf{Abstraction}(\alpha : A_\top \multimap A_{\mathsf{abs}}) :=
\mathsf{Glue}(\bullet A_\top, \bigcirc A_{\mathsf{abs}}, \bullet(\eta^\circ \circ \alpha))$. -/
def GlueAbstractionComp (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs) : CompType :=
  GlueComp
    (ClosedComp (ConstComp A_top))
    (OpenComp (ConstComp A_abs))
    (ClosedComp.map ⟨alpha, alpha, fun _ => rfl⟩)

/-- **Definition 2.17 ($\mathsf{Abstraction}$ on Computation Types, Direct Form):**
Assembles a cost algebra homomorphism $\alpha : A_\top \multimap A_{\mathsf{abs}}$ into a phased
computation type $(A_\top, A_{\mathsf{abs}}, \alpha) : \mathcal{C}$. -/
def AbstractionComp (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs) : CompType where
  top := A_top
  abs := A_abs
  alpha := alpha

/-- Layered $\mathsf{Abstraction}(\alpha : A_\top \multimap A_{\mathsf{abs}})$ for phased computation
types $A_\top, A_{\mathsf{abs}} : \mathcal{C}$ (used in Example 2.24 and Definition 4.1):
In the Kripke semantics, $\mathsf{Glue}(\bullet A_\top, \bigcirc A_{\mathsf{abs}}, \bullet(\eta^\circ \circ \alpha))$
has concrete part $(A_\top)_\top$, abstract part $(A_{\mathsf{abs}})_{\mathsf{abs}}$, and composite
abstraction homomorphism $\alpha_{\mathsf{abs}} \circ \alpha_{A_\top} = \alpha_{A_{\mathsf{abs}}} \circ \alpha_\top$. -/
def AbstractionCompLayered (A_top A_abs : CompType) (alpha : CompHom A_top A_abs) : CompType where
  top := A_top.top
  abs := A_abs.abs
  alpha := alpha.hom_abs.comp A_top.alpha

/-! ## §2.3 Potential Functions as Types, Independently -/

/-- The potential-charging homomorphism $\varphi(\Phi) : FX \multimap FX$ defined by
$\varphi(\Phi)(\mathsf{ret}\,x) := \mathsf{charge}\langle \Phi(x) \rangle(\mathsf{ret}\,x)$
(Definition 2.21). -/
def phiHom {X : Type} (Phi : X → Nat) : CostHom (FreeCostAlg X) (FreeCostAlg X) where
  fn := fun p => (p.1 + Phi p.2, p.2)
  map_charge := fun c ⟨c₀, x⟩ => Prod.ext (Nat.add_assoc c c₀ (Phi x)) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, e⟩

/-- **Definition 2.21 ($\mathsf{Potential}$ as a Computation Type):**
To render a potential function $\Phi : X \to \mathbb{N}$ as a type, define
$\mathsf{Potential}(\Phi : X \to \mathbb{N}) := \mathsf{Abstraction}(\varphi(\Phi) : FX \multimap FX)$. -/
def PotentialType (X : Type) (Phi : X → Nat) : CompType :=
  AbstractionComp (FreeCostAlg X) (FreeCostAlg X) (phiHom Phi)

/-- **Example 2.20 (Cost-Aware Ephemeral Batched Queue):**
Potential function $\Phi(l_1, l_2) := |l_2|$ on batched queues. -/
def queuePhi {α : Type} (q : BatchedQueueRep α) : Nat :=
  q.2.length

/-- Cost-aware abstraction homomorphism $\alpha : F(\mathsf{List}\,\alpha \times \mathsf{List}\,\alpha) \multimap F(\mathsf{List}\,\alpha)$
defined by $\alpha(\mathsf{ret}(l_1, l_2)) := \mathsf{charge}\langle |l_2| \rangle(\mathsf{ret}(l_1 \mathbin{+\!+} \mathrm{reverse}\,l_2))$
(Example 2.20). -/
def queueAlphaHom (α : Type) :
    CostHom (FreeCostAlg (BatchedQueueRep α)) (FreeCostAlg (List α)) where
  fn := fun p => (p.1 + queuePhi p.2, queueChi p.2)
  map_charge := fun c ⟨c₀, q⟩ => Prod.ext (Nat.add_assoc c c₀ (queuePhi q)) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, congrArg queueChi e⟩

/-- Cost-aware batched queue computation type
$A := \mathsf{Abstraction}(\alpha : F(\mathsf{List}\,\alpha \times \mathsf{List}\,\alpha) \multimap F(\mathsf{List}\,\alpha))$
(Example 2.20). -/
def BatchedQueueComp (α : Type) : CompType :=
  AbstractionComp (FreeCostAlg (BatchedQueueRep α)) (FreeCostAlg (List α)) (queueAlphaHom α)

/-- True (zero-cost) concrete enqueue homomorphism
$\mathsf{enqueue}_\top\,n(\mathsf{ret}(l_1, l_2)) := \mathsf{ret}(l_1, n :: l_2)$ (Example 2.20). -/
def enqueueCompTop {α : Type} (n : α) :
    CostHom (FreeCostAlg (BatchedQueueRep α)) (FreeCostAlg (BatchedQueueRep α)) where
  fn := fun p => (p.1, enqueueValTop n p.2)
  map_charge := fun _ _ => rfl
  mono := fun ⟨h, e⟩ => ⟨h, congrArg (enqueueValTop n) e⟩

/-- Amortized (unit-cost) abstract enqueue homomorphism
$\mathsf{enqueue}_{\mathsf{abs}}\,n(\mathsf{ret}\,l) := \mathsf{charge}\langle 1 \rangle(\mathsf{ret}(l \mathbin{+\!+} [n]))$
(Example 2.20). -/
def enqueueCompAbs {α : Type} (n : α) :
    CostHom (FreeCostAlg (List α)) (FreeCostAlg (List α)) where
  fn := fun p => (p.1 + 1, enqueueValAbs n p.2)
  map_charge := fun c ⟨c₀, _⟩ => Prod.ext (Nat.add_assoc c c₀ 1) rfl
  mono := fun ⟨h, e⟩ => ⟨Nat.add_le_add_right h 1, congrArg (enqueueValAbs n) e⟩

/-! ## §3.1–3.2 Queue Specification Interfaces, Sealing Monad $\mathsf{S}$, and Lax Homomorphisms -/

/-- **Examples 3.2 & 3.3 (Single-World Ephemeral PreQueue Record):**
Packages a cost algebra $A$ with `empty : UA`, `enqueue : α → (A ⊸ A)`, and
`dequeue : A ⊸ F(Option (α × UA))` (representing uncons). -/
structure SingleWorldPreQueue (α : Type) where
  alg : CostAlg
  empty : alg.carrier
  enqueue : α → CostHom alg alg

/-- Abstract projection of a phased pre-queue into a single-world pre-queue at the $\mathsf{abs}$ phase
(Example 3.3). -/
structure PhasedPreQueue (α : Type) where
  comp : CompType
  empty_top : comp.top.carrier
  empty_abs : comp.abs.carrier
  empty_comm : comp.alpha.fn empty_top = empty_abs
  enqueue : α → CompHom comp comp

/-- Abstract-phase projection of a `PhasedPreQueue` (Example 3.3). -/
def PhasedPreQueue.absView {α : Type} (Q : PhasedPreQueue α) : SingleWorldPreQueue α where
  alg := Q.comp.abs
  empty := Q.empty_abs
  enqueue := fun n => (Q.enqueue n).hom_abs

/-- Target amortized queue specification at the $\mathsf{abs}$ phase (Example 3.3):
carrier $F(\mathsf{List}\,\alpha)$, `empty := ret []` (0 cost), and
`enqueue n (ret l) := charge⟨1⟩(ret (l ++ [n]))` (1 unit of amortized cost). -/
def AmortizedQueueModel (α : Type) : SingleWorldPreQueue α where
  alg := FreeCostAlg (List α)
  empty := retFree []
  enqueue := enqueueCompAbs

/-- **Section 3.2 (Sealing Monad $\mathsf{S}A := \bullet A \times^{\le}_{\bullet \bigcirc A} \bigcirc A$):**
The comma computation type whose concrete world consists of pairs $(a_\top, a_{\mathsf{abs}})$
satisfying $\alpha_A(a_\top) \le_{A_{\mathsf{abs}}} a_{\mathsf{abs}}$ and whose abstract world is
$A_{\mathsf{abs}}$ (with second projection as abstraction homomorphism). -/
def SealComp (A : CompType) : CompType where
  top := CommaCostAlg A.alpha (CostHom.id A.abs)
  abs := A.abs
  alpha := {
    fn := fun p => p.1.2
    map_charge := fun _ _ => rfl
    mono := fun h => h.2
  }

/-- **Section 3.2 (Lax Homomorphism $A \mathrel{\multimap\!\!\!\!+} B$):**
A lax commutative square of cost algebra homomorphisms $(f_\top, f_{\mathsf{abs}})$ satisfying
$\alpha_B(f_\top(a)) \le_{B_{\mathsf{abs}}} f_{\mathsf{abs}}(\alpha_A(a))$ for all $a : UA_\top$. -/
@[ext]
structure LaxCompHom (A B : CompType) where
  hom_top : CostHom A.top B.top
  hom_abs : CostHom A.abs B.abs
  lax_comm : ∀ a : A.top.carrier, B.abs.le (B.alpha.fn (hom_top.fn a)) (hom_abs.fn (A.alpha.fn a))

/-- Every strict computation homomorphism $f : A \multimap B$ induces a lax computation homomorphism
$f : A \mathrel{\multimap\!\!\!\!+} B$. -/
def CompHom.toLax {A B : CompType} (f : CompHom A B) : LaxCompHom A B where
  hom_top := f.hom_top
  hom_abs := f.hom_abs
  lax_comm := fun a => by
    rw [f.comm a]
    exact B.abs.le_refl _

/-- Identity lax homomorphism $\mathrm{id}_A : A \mathrel{\multimap\!\!\!\!+} A$. -/
def LaxCompHom.id (A : CompType) : LaxCompHom A A :=
  (CompHom.id A).toLax

/-- Composition of lax computation homomorphisms $(g \circ f) : A \mathrel{\multimap\!\!\!\!+} C$. -/
def LaxCompHom.comp {A B C : CompType} (g : LaxCompHom B C) (f : LaxCompHom A B) : LaxCompHom A C where
  hom_top := g.hom_top.comp f.hom_top
  hom_abs := g.hom_abs.comp f.hom_abs
  lax_comm := fun a =>
    C.abs.le_trans
      (g.lax_comm (f.hom_top.fn a))
      (g.hom_abs.mono (f.lax_comm a))

end Grodin2026


