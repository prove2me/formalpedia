-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:37:20.919775+00:00
-- url     : https://prove2.me/theorems/dda5343f-87ce-4e35-aa33-5a9e7dbaae0a
-- title:
--   Boundary diagrams of two-way traversals: the diagram monoid, signed recurrent classes, rectangles and feedback relations
-- statement:
--   Fix $m\in\mathbb N$ and write $[m]=\{0,1,\dots,m-1\}$ for the state labels of a two-way automaton. A relation on $[m]$ is a subset of $[m]\times[m]$. Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$; $\mathrm{Id}$ is the identity relation, and $R^*$ is the reflexive–transitive closure ($(x,y)\in R^*$ iff $y$ is reached from $x$ by $k\ge 0$ steps of $R$).
--
--   A **boundary diagram** is a quadruple $a=(F_a,B_a,L_a,R_a)$ of relations on $[m]$, read as the possible traversals of a tape segment: $(p,q)\in F_a$ means "enter on the left in state $p$ and leave on the right in state $q$"; $B_a$ records entering on the right and leaving on the left; $L_a$ entering and leaving on the left; $R_a$ entering and leaving on the right. A sign is $\sigma\in\{+,-\}$, and a port is a pair in $\{\mathrm l,\mathrm r\}\times[m]$ consisting of a side and a label. The module defines the following.
--
--   1. **Product and identity.** For diagrams $a$ (on the left) and $b$ (on the right),
--   $$ab=\Big(F_a(L_bR_a)^*F_b,\ \ B_b(R_aL_b)^*B_a,\ \ L_a\cup F_a(L_bR_a)^*L_bB_a,\ \ R_b\cup B_bR_a(L_bR_a)^*F_b\Big),$$
--   and $1=(\mathrm{Id},\mathrm{Id},\emptyset,\emptyset)$. It is proved that $1a=a=a1$ and $(ab)c=a(bc)$, so the diagrams form a monoid, and that this monoid is finite.
--   2. **Reflection and inclusion.** $\bar a=(B_a,F_a,R_a,L_a)$ exchanges left and right, and $\overline{ab}=\bar b\,\bar a$. Inclusion $a\sqsubseteq b$ means $F_a\subseteq F_b$, $B_a\subseteq B_b$, $L_a\subseteq L_b$ and $R_a\subseteq R_b$.
--   3. **Through relations, loop closures, recurrence.** $T_+(a)=F_a$ and $T_-(a)=B_a$; $\Lambda_+(e)=(L_eR_e)^*$ and $\Lambda_-(e)=(R_eL_e)^*$; and $\mathrm{Rec}_\sigma(e)=\Lambda_\sigma(e)\,T_\sigma(e)\,\Lambda_\sigma(e)$.
--   4. **Signed recurrent classes.** $\mathcal C(e)$ is the set of pairs $(\sigma,K)$ for which there is $x\in[m]$ with $(x,x)\in\mathrm{Rec}_\sigma(e)$ and $K=\{y:\ (x,y)\in\mathrm{Rec}_\sigma(e)\text{ and }(y,x)\in\mathrm{Rec}_\sigma(e)\}$.
--   5. **Corner and nesting.** $\mathrm{Corner}(e)=\{z:\ ez=z\text{ and }ze=z\}$. Nesting $d\preceq e$ holds iff $dd=d$, $ee=e$, $de=d$ and $ed=d$; it is a different relation from inclusion.
--   6. **Surviving, missing and unprotected classes.** For diagrams $e,z$ put $U_\sigma(e,z)=\Lambda_\sigma(e)\,T_\sigma(z)\,\Lambda_\sigma(e)$. $\mathcal M(e,z)$ is the set of $(\sigma,K)\in\mathcal C(e)$ with $(x,x)\notin U_\sigma(e,z)$ for every $x\in K$. For a set $P\subseteq\{+,-\}\times[m]$ of protected signed labels, $\mathcal U(e,P)$ is the set of $(\sigma,K)\in\mathcal C(e)$ with $(\sigma,x)\notin P$ for every $x\in K$.
--   7. **Rectangles.** $\mathrm{Rect}_\sigma(e,p)=\{u:(u,p)\in T_\sigma(e)\Lambda_\sigma(e)\}\times\{v:(p,v)\in\Lambda_\sigma(e)T_\sigma(e)\}$. For a pair $C=(\sigma,K)$, the port relation $Q(e,C)$ relates $(\mathrm l,u)$ to $(\mathrm r,v)$ if $\sigma=+$, and $(\mathrm r,u)$ to $(\mathrm l,v)$ if $\sigma=-$, whenever $(u,v)\in\mathrm{Rect}_\sigma(e,p)$ for some $p\in K$; it contains no other pairs.
--   8. **Ports, bounces and feedback.** $\mathrm{Port}(e)$ is the relation on ports with $(\mathrm l,x)\to(\mathrm l,y)$ iff $(x,y)\in L_e$, $(\mathrm l,x)\to(\mathrm r,y)$ iff $(x,y)\in F_e$, $(\mathrm r,x)\to(\mathrm l,y)$ iff $(x,y)\in B_e$, and $(\mathrm r,x)\to(\mathrm r,y)$ iff $(x,y)\in R_e$. For relations $R,L$ on $[m]$, $\beta(R,L)$ relates $(\mathrm l,x)$ to $(\mathrm l,y)$ iff $(x,y)\in R$ and $(\mathrm r,x)$ to $(\mathrm r,y)$ iff $(x,y)\in L$, and never changes the side. The feedback relation is $\Phi(e;R,L)=\mathrm{Port}(e)\,\big(\beta(R,L)\,\mathrm{Port}(e)\big)^*$.
--   9. **Context traversals, class influence and transport.** For diagrams $d,u,v$: $\mathrm{In}_+$ relates $x\in[m]$ to the port $(\mathrm l,y)$ iff $(x,y)\in\Lambda_+(d)F_u$, and $\mathrm{In}_-$ relates $x$ to $(\mathrm r,y)$ iff $(x,y)\in\Lambda_-(d)B_v$; $\mathrm{Out}_+$ relates $(\mathrm r,x)$ to $y$ iff $(x,y)\in F_v\Lambda_+(d)$, and $\mathrm{Out}_-$ relates $(\mathrm l,x)$ to $y$ iff $(x,y)\in B_u\Lambda_-(d)$. With $\beta=\beta(R_u,L_v)$ and a pair $C$ as in item 7,
--   $$I_\sigma(e,d,u,v;C)=\mathrm{In}_\sigma\,\big(\mathrm{Port}(e)\,\beta\big)^*\,Q(e,C)\,\big(\beta\,\mathrm{Port}(e)\big)^*\,\mathrm{Out}_\sigma ,$$
--   and for a set $J$ of such pairs, $\mathcal T(e,d,u,v;J)$ is the set of $(\sigma,D)\in\mathcal C(d)$ such that $(x,x)\in I_\sigma(e,d,u,v;C)$ for some $C\in J$ and some $x\in D$.
--
--   The product $ab$ describes the traversals of two tape segments placed side by side: a traversal may cross the common boundary any finite number of times, which is what the starred factors record. Multiplying the diagrams of the letters of a word therefore yields the diagram of the word, so a two-way automaton induces a homomorphism from words into this finite monoid. Idempotent diagrams, their signed recurrent classes, and the classes lost when an idempotent $e$ is replaced by an element $z$ of its corner are the bookkeeping devices of the state lower bound; feedback, class influence and transport describe traversals of a product $uev$ (used with $d=uev$) through its middle factor, separated by returns through the contexts $u$ and $v$.
--
--   **Formalization Note** `Diagram m` is a structure with fields `forward`, `backward`, `left`, `right : SetRel (Fin m) (Fin m)`. The product is `Diagram.comp` (also the `Monoid` multiplication, with `Diagram.identity` as unit), and the module also defines `inclusion`, `reflect`, `through`, `loopClosure`, `recurrence`, `classes`, `corner`, `nesting`, `surviving`, `missing`, `unprotected`, `rectangle`, `portRelation`, `bounceRelation`, `feedback`, `classRectangle`, `contextEntry`, `contextExit`, `classInfluence` and `transportMarked`. Signs are booleans with `true` for $+$; port sides are booleans with `false` for left and `true` for right; a signed class is a pair in `Bool × Set (Fin m)`. The proved facts are `identity_comp`, `comp_identity`, `reflect_comp`, `comp_assoc` (via `comp_assoc_forward` and `comp_assoc_left`) and the instance `finite_diagram`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Four boundary relations; the direction distinguishes the two copies of `Fin m`. -/
@[ext]
structure Diagram (m : ℕ) where
  /-- Enter on the left and exit on the right. -/
  forward : SetRel (Fin m) (Fin m)
  /-- Enter on the right and exit on the left. -/
  backward : SetRel (Fin m) (Fin m)
  /-- Enter and exit on the left. -/
  left : SetRel (Fin m) (Fin m)
  /-- Enter and exit on the right. -/
  right : SetRel (Fin m) (Fin m)

namespace Diagram

/-- Composition of boundary diagrams in path order. -/
def comp {m : ℕ} (a b : Diagram m) : Diagram m where
  forward := a.forward ○ relStar (b.left ○ a.right) ○ b.forward
  backward := b.backward ○ relStar (a.right ○ b.left) ○ a.backward
  left := a.left ∪ (a.forward ○ relStar (b.left ○ a.right) ○ b.left ○ a.backward)
  right := b.right ∪ (b.backward ○ a.right ○ relStar (b.left ○ a.right) ○ b.forward)

/-- Identity boundary diagram. -/
def identity (m : ℕ) : Diagram m := ⟨SetRel.id, SetRel.id, ∅, ∅⟩

/-- Componentwise edge inclusion, as a relation on diagrams. -/
def inclusion (m : ℕ) : SetRel (Diagram m) (Diagram m) :=
  {pair | pair.1.forward ⊆ pair.2.forward ∧ pair.1.backward ⊆ pair.2.backward ∧
    pair.1.left ⊆ pair.2.left ∧ pair.1.right ⊆ pair.2.right}

/-- Reflection reverses the order of multiplication. -/
def reflect {m : ℕ} (a : Diagram m) : Diagram m :=
  ⟨a.backward, a.forward, a.right, a.left⟩

/-- `true` denotes the positive sign; `false` denotes the negative sign. -/
def through {m : ℕ} (a : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  if positive then a.forward else a.backward

/-- Closure of alternating returns at a boundary. -/
def loopClosure {m : ℕ} (e : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  relStar (if positive then e.left ○ e.right else e.right ○ e.left)

/-- The recurrent relation obtained by closing through traversals. -/
def recurrence {m : ℕ} (e : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  e.loopClosure positive ○ e.through positive ○ e.loopClosure positive

/-- Signed recurrent equivalence classes of an idempotent diagram. -/
def classes {m : ℕ} (e : Diagram m) : Set (Bool × Set (Fin m)) :=
  {c | ∃ x, (x, x) ∈ e.recurrence c.1 ∧
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1}}

/-- The corner membership equations for an idempotent `e`. -/
def corner {m : ℕ} (e : Diagram m) : Set (Diagram m) :=
  {z | comp e z = z ∧ comp z e = z}

/-- Nesting of idempotents; distinct from edge inclusion. -/
def nesting (m : ℕ) : SetRel (Diagram m) (Diagram m) :=
  {(d, e) | comp d d = d ∧ comp e e = e ∧ comp d e = d ∧ comp e d = d}

/-- The surviving through relation `U` relative to `e`. -/
def surviving {m : ℕ} (e z : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  e.loopClosure positive ○ z.through positive ○ e.loopClosure positive

/-- Classes whose recurrent loops are absent after replacement by `z`. -/
def missing {m : ℕ} (e z : Diagram m) : Set (Bool × Set (Fin m)) :=
  {c | c ∈ e.classes ∧ ∀ x ∈ c.2, (x, x) ∉ e.surviving z c.1}

/-- Classes containing none of a fixed set of signed protected labels. -/
def unprotected {m : ℕ} (e : Diagram m) (P : Set (Bool × Fin m)) : Set (Bool × Set (Fin m)) :=
  {c | c ∈ e.classes ∧ ∀ x ∈ c.2, (c.1, x) ∉ P}

/-- Rectangle associated with a recurrent representative. -/
def rectangle {m : ℕ} (e : Diagram m) (positive : Bool) (p : Fin m) :
    SetRel (Fin m) (Fin m) :=
  {u | (u, p) ∈ e.through positive ○ e.loopClosure positive} ×ˢ
    {v | (p, v) ∈ e.loopClosure positive ○ e.through positive}

/-- Boundary ports: `false` is left and `true` is right. -/
def portRelation {m : ℕ} (e : Diagram m) : SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | (pair.1.2, pair.2.2) ∈ match pair.1.1, pair.2.1 with
    | false, false => e.left
    | false, true => e.forward
    | true, false => e.backward
    | true, true => e.right}

/-- Returns from an exit port through the surrounding left or right context. -/
def bounceRelation {m : ℕ} (R L : SetRel (Fin m) (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | pair.1.1 = pair.2.1 ∧ (pair.1.2, pair.2.2) ∈ if pair.1.1 then L else R}

/-- A middle traversal followed by any finite number of context returns and traversals. -/
def feedback {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  e.portRelation ○ relStar (bounceRelation R L ○ e.portRelation)

/-- The rectangular port edges belonging to a signed recurrent class. -/
def classRectangle {m : ℕ} (e : Diagram m) (C : Bool × Set (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | pair.1.1 = !C.1 ∧ pair.2.1 = C.1 ∧
    ∃ p ∈ C.2, (pair.1.2, pair.2.2) ∈ e.rectangle C.1 p}

/-- Initial traversal of the outer context, including recurrence closure. -/
def contextEntry {m : ℕ} (d u v : Diagram m) (positive : Bool) :
    SetRel (Fin m) (Bool × Fin m) :=
  {pair | pair.2.1 = !positive ∧
    (pair.1, pair.2.2) ∈ d.loopClosure positive ○
      (if positive then u.forward else v.backward)}

/-- Final traversal of the outer context, including recurrence closure. -/
def contextExit {m : ℕ} (d u v : Diagram m) (positive : Bool) :
    SetRel (Bool × Fin m) (Fin m) :=
  {pair | pair.1.1 = positive ∧
    (pair.1.2, pair.2) ∈ (if positive then v.forward else u.backward) ○
      d.loopClosure positive}

/-- Traversals with one designated occurrence of a recurrent rectangle in the middle factor. -/
def classInfluence {m : ℕ} (e d u v : Diagram m) (positive : Bool)
    (C : Bool × Set (Fin m)) : SetRel (Fin m) (Fin m) :=
  contextEntry d u v positive ○ relStar (e.portRelation ○ bounceRelation u.right v.left) ○
    e.classRectangle C ○ relStar (bounceRelation u.right v.left ○ e.portRelation) ○
    contextExit d u v positive

/-- Target classes whose original traversals can use a rectangle from the fixed set `J`. -/
def transportMarked {m : ℕ} (e d u v : Diagram m) (J : Set (Bool × Set (Fin m))) :
    Set (Bool × Set (Fin m)) :=
  {D | D ∈ d.classes ∧ ∃ C ∈ J, ∃ x ∈ D.2, (x, x) ∈ e.classInfluence d u v D.1 C}

@[simp]
theorem identity_comp {m : ℕ} (a : Diagram m) : comp (identity m) a = a := by
  cases a
  simp [comp, identity]

@[simp]
theorem comp_identity {m : ℕ} (a : Diagram m) : comp a (identity m) = a := by
  cases a
  simp [comp, identity]

theorem reflect_comp {m : ℕ} (a b : Diagram m) :
    reflect (comp a b) = comp (reflect b) (reflect a) := by
  apply Diagram.ext
  · rfl
  · rfl
  · simpa only [reflect, comp, SetRel.comp_assoc] using
      congrArg (fun R => b.right ∪ (b.backward ○ R ○ b.forward))
        (comp_relStar_rotate a.right b.left)
  · simpa only [reflect, comp, SetRel.comp_assoc] using
      congrArg (fun R => a.left ∪ (a.forward ○ R ○ a.backward))
        (comp_relStar_rotate b.left a.right).symm

theorem comp_assoc_forward {m : ℕ} (a b c : Diagram m) :
    (comp (comp a b) c).forward = (comp a (comp b c)).forward := by
  simpa only [comp, relComp_union, union_relComp, SetRel.comp_assoc] using
    congrArg (fun R => a.forward ○ R ○ c.forward)
      (relStar_block_forward (b.left ○ a.right) b.forward
        (c.left ○ b.backward ○ a.right) (c.left ○ b.right)).symm

theorem comp_assoc_left {m : ℕ} (a b c : Diagram m) :
    (comp (comp a b) c).left = (comp a (comp b c)).left := by
  simpa only [comp, relComp_union, union_relComp, SetRel.comp_assoc, Set.union_assoc] using
    congrArg (fun R => a.left ∪ (a.forward ○ R ○ a.backward))
      (relStar_block_exit b.left a.right b.forward (c.left ○ b.backward)
        (c.left ○ b.right)).symm

/-- The product of boundary diagrams is associative. -/
theorem comp_assoc {m : ℕ} (a b c : Diagram m) :
    comp (comp a b) c = comp a (comp b c) := by
  apply Diagram.ext
  · exact comp_assoc_forward a b c
  · have h := comp_assoc_forward (reflect c) (reflect b) (reflect a)
    simp only [← reflect_comp] at h
    exact h.symm
  · exact comp_assoc_left a b c
  · have h := comp_assoc_left (reflect c) (reflect b) (reflect a)
    simp only [← reflect_comp] at h
    exact h.symm

instance {m : ℕ} : Monoid (Diagram m) where
  mul := comp
  one := identity m
  mul_assoc := comp_assoc
  one_mul := identity_comp
  mul_one := comp_identity

@[instance]
theorem finite_diagram {m : ℕ} : Finite (Diagram m) :=
  Finite.of_injective (fun a : Diagram m => (a.forward, a.backward, a.left, a.right)) (by
    intro a b h
    exact Diagram.ext (congrArg (·.1) h) (congrArg (·.2.1) h)
      (congrArg (·.2.2.1) h) (congrArg (·.2.2.2) h))

end Diagram

end TwoWayComplementation

end OAI


