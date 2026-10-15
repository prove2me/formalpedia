-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
-- name    : OAI_Combinatorics_TwoWayAutomata_Diagram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:13:28.52232+00:00
-- url     : https://prove2.me/theorems/2c1dc8c0-0f52-459f-9958-366c20bf3477
-- title:
--   Boundary diagrams of two-way traversals: the diagram monoid, recurrent classes, missing classes and feedback relations
-- statement:
--   Fix $m\in\mathbb{N}$ and put $[m]=\{0,1,\dots,m-1\}$; in the application $[m]$ is the state set of a two-way automaton (with one extra state). Relations on $[m]$ are subsets of $[m]\times[m]$; $RS$ is composition in path order, $(x,z)\in RS\iff\exists y:\ (x,y)\in R,\ (y,z)\in S$; $\mathrm{Id}$ is the identity relation and $R^*$ the reflexive–transitive closure. A *sign* is $+$ or $-$, a *side* is $\mathrm L$ (left) or $\mathrm R$ (right), and a *port* is a pair $(s,x)$ of a side $s$ and a point $x\in[m]$.
--
--   1. **Boundary diagrams.** A diagram is a quadruple $a=(a_{\mathrm f},a_{\mathrm b},a_{\mathrm l},a_{\mathrm r})$ of relations on $[m]$, read as the possible traversals of a block of tape cells: $a_{\mathrm f}$ (forward) relates the state on entering at the left boundary to the state on leaving at the right boundary, $a_{\mathrm b}$ (backward) goes from the right boundary to the left one, $a_{\mathrm l}$ enters and leaves on the left, and $a_{\mathrm r}$ enters and leaves on the right.
--   2. **The diagram monoid.** The product of diagrams $a$ and $c$, with $c$ placed to the right of $a$, is
--   $$\begin{aligned}(ac)_{\mathrm f}&=a_{\mathrm f}\,(c_{\mathrm l}a_{\mathrm r})^*\,c_{\mathrm f}, &\qquad (ac)_{\mathrm b}&=c_{\mathrm b}\,(a_{\mathrm r}c_{\mathrm l})^*\,a_{\mathrm b},\\ (ac)_{\mathrm l}&=a_{\mathrm l}\cup a_{\mathrm f}\,(c_{\mathrm l}a_{\mathrm r})^*\,c_{\mathrm l}\,a_{\mathrm b}, & (ac)_{\mathrm r}&=c_{\mathrm r}\cup c_{\mathrm b}\,a_{\mathrm r}\,(c_{\mathrm l}a_{\mathrm r})^*\,c_{\mathrm f},\end{aligned}$$
--   and the identity diagram is $1=(\mathrm{Id},\mathrm{Id},\emptyset,\emptyset)$. The product is associative and $1a=a=a1$, so the diagrams on $[m]$ form a monoid $\mathcal D_m$, which is finite.
--   3. **Inclusion and reflection.** $a\sqsubseteq c$ means $a_{\mathrm f}\subseteq c_{\mathrm f}$, $a_{\mathrm b}\subseteq c_{\mathrm b}$, $a_{\mathrm l}\subseteq c_{\mathrm l}$ and $a_{\mathrm r}\subseteq c_{\mathrm r}$. The reflection $\bar a=(a_{\mathrm b},a_{\mathrm f},a_{\mathrm r},a_{\mathrm l})$ exchanges the two sides and reverses products: $\overline{ac}=\bar c\,\bar a$.
--   4. **Through relations, loop closures and recurrence.** For a diagram $e$ put $e_+=e_{\mathrm f}$, $e_-=e_{\mathrm b}$ and
--   $$\Lambda^+_e=(e_{\mathrm l}e_{\mathrm r})^*,\qquad \Lambda^-_e=(e_{\mathrm r}e_{\mathrm l})^*,\qquad \Theta^\pm_e=\Lambda^\pm_e\,e_\pm\,\Lambda^\pm_e .$$
--   The loop closure $\Lambda^\pm_e$ collects the back-and-forth returns at the boundary between two adjacent copies of $e$, and $\Theta^\pm_e$ is the recurrence relation of sign $\pm$. For a second diagram $z$, the through relation of $z$ surviving relative to $e$ is $U^\pm_e(z)=\Lambda^\pm_e\,z_\pm\,\Lambda^\pm_e$; thus $\Theta^\pm_e=U^\pm_e(e)$.
--   5. **Signed recurrent classes.** $\mathrm{Cl}(e)$ is the set of pairs $(\pm,C)$, $C\subseteq[m]$, for which there is $x\in[m]$ with $(x,x)\in\Theta^\pm_e$ and
--   $$C=\{y\in[m]:\ (x,y)\in\Theta^\pm_e\ \text{and}\ (y,x)\in\Theta^\pm_e\}.$$
--   For a diagram $z$, the classes of $e$ *missing* in $z$ are the $(\pm,C)\in\mathrm{Cl}(e)$ with $(x,x)\notin U^\pm_e(z)$ for every $x\in C$; they form $\mathrm{Miss}_e(z)$. For a set $P$ of signed points $(\pm,x)$, the *unprotected* classes are the $(\pm,C)\in\mathrm{Cl}(e)$ with $(\pm,x)\notin P$ for every $x\in C$.
--   6. **Corners and nesting.** The corner of a diagram $e$ is $\{z\in\mathcal D_m:\ ez=z=ze\}$. Two diagrams are nested, $d\preceq e$, if $dd=d$, $ee=e$ and $de=d=ed$; this is the natural order on idempotents and is unrelated to $\sqsubseteq$.
--   7. **Rectangles.** For a sign and a point $p\in[m]$, the rectangle of $p$ is the product set
--   $$\mathrm{Rect}^\pm_e(p)=\{u:\ (u,p)\in e_\pm\Lambda^\pm_e\}\times\{v:\ (p,v)\in\Lambda^\pm_e\,e_\pm\}.$$
--   The class rectangle $\mathrm{Rect}_e(\pm,C)$ is the relation on ports joining $(\mathrm L,u)$ to $(\mathrm R,v)$ if the sign is $+$, and $(\mathrm R,u)$ to $(\mathrm L,v)$ if it is $-$, whenever $(u,v)\in\mathrm{Rect}^\pm_e(p)$ for some $p\in C$.
--   8. **Ports and feedback.** The port relation $\Pi_e$ joins $(\mathrm L,x)$ to $(\mathrm L,y)$ and to $(\mathrm R,y)$ according to $e_{\mathrm l}$ and $e_{\mathrm f}$, and $(\mathrm R,x)$ to $(\mathrm L,y)$ and to $(\mathrm R,y)$ according to $e_{\mathrm b}$ and $e_{\mathrm r}$. For relations $R,L$ on $[m]$, the bounce relation $\beta_{R,L}$ joins $(\mathrm L,x)$ to $(\mathrm L,y)$ if $(x,y)\in R$ and $(\mathrm R,x)$ to $(\mathrm R,y)$ if $(x,y)\in L$, and never changes side. The feedback relation
--   $$\Phi_e(R,L)=\Pi_e\,\big(\beta_{R,L}\,\Pi_e\big)^*$$
--   is a traversal of $e$ followed by finitely many rounds of a return through the surrounding context and another traversal of $e$.
--   9. **Context relations and transport.** For diagrams $d,u,v$, the entry relations from $[m]$ to ports and the exit relations from ports to $[m]$ are
--   $$\mathrm{In}^+=\{(x,(\mathrm L,y)):\ (x,y)\in\Lambda^+_d u_{\mathrm f}\},\qquad \mathrm{In}^-=\{(x,(\mathrm R,y)):\ (x,y)\in\Lambda^-_d v_{\mathrm b}\},$$
--   $$\mathrm{Out}^+=\{((\mathrm R,x),y):\ (x,y)\in v_{\mathrm f}\Lambda^+_d\},\qquad \mathrm{Out}^-=\{((\mathrm L,x),y):\ (x,y)\in u_{\mathrm b}\Lambda^-_d\}.$$
--   With $\beta=\beta_{u_{\mathrm r},v_{\mathrm l}}$, the influence of a signed class $C$ of $e$ on the sign $\pm$ is the relation on $[m]$
--   $$\mathrm{Inf}^\pm(C)=\mathrm{In}^\pm\,(\Pi_e\beta)^*\,\mathrm{Rect}_e(C)\,(\beta\,\Pi_e)^*\,\mathrm{Out}^\pm ,$$
--   that is, the traversals of $u\,e\,v$, closed up by the loops of $d$, with one designated occurrence of a rectangle of $C$ in the middle factor. For a set $J$ of signed classes, the transport-marked classes are the $(\pm,D)\in\mathrm{Cl}(d)$ for which some $C\in J$ and some $x\in D$ satisfy $(x,x)\in\mathrm{Inf}^\pm(C)$.
--
--   Diagrams are the transition behaviours of a two-way automaton on a factor of its input. Later results show that an automaton with $s$ states yields a monoid homomorphism from words into $\mathcal D_{s+1}$ from which acceptance can be read off, so that lower bounds for automata become statements about the finite monoid $\mathcal D_m$. Since $\Theta^\pm_e$ is transitive when $e$ is idempotent (shown separately), the classes of an idempotent are the equivalence classes of mutually recurrent points, tagged with a sign. Counting the classes of $e$ missing in an element $z$ of its corner is the measure of loss in the lower-bound argument; the rectangles, feedback and context relations express the surviving relation of a product $u\,e\,v$ through the traversals of the middle factor $e$, which is how missing classes are transported from one idempotent to another.
--
--   **Formalization Note** `Diagram m` is a structure with fields `forward`, `backward`, `left`, `right` of type `SetRel (Fin m) (Fin m)`. The product is `comp` (also the multiplication of the `Monoid` instance), the identity is `identity m`, and the laws are `identity_comp`, `comp_identity` and `comp_assoc`, the latter obtained from `comp_assoc_forward`, `comp_assoc_left` and `reflect_comp`; `finite_diagram` is the finiteness instance. Signs and sides are `Bool`, with `true` for $+$ and for the right side. Classes are elements of `Bool × Set (Fin m)`. The remaining objects are `inclusion`, `reflect`, `through`, `loopClosure`, `recurrence`, `surviving`, `classes`, `missing`, `unprotected`, `corner`, `nesting`, `rectangle`, `classRectangle`, `portRelation`, `bounceRelation`, `feedback`, `contextEntry`, `contextExit`, `classInfluence` and `transportMarked`; none of them assumes that a diagram is idempotent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

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


