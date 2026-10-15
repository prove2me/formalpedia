-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Relations
-- name    : OAI_Combinatorics_Automata_Relations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:03:07.353979+00:00
-- url     : https://prove2.me/theorems/3c193565-a3cc-4a65-84e9-40662008105d
-- title:
--   Partial identities, corners of the relation monoid, one-edge relations and rectangle frames
-- statement:
--   Let $H$ be a set and let $\mathcal B(H)$ be the monoid of binary relations on $H$. Its product is relational composition in diagrammatic order, $(RS)(x,z)\iff\exists y:\ R(x,y)\wedge S(y,z)$, and its identity is the equality relation. For $F\subseteq H$ write $\Delta_F=\{(x,x):x\in F\}$ for the partial identity on $F$.
--
--   1. **Partial identities.** $\Delta_F$ is idempotent. Moreover $(\Delta_F R)(x,y)\iff x\in F\wedge R(x,y)$ and $(R\,\Delta_F)(x,y)\iff R(x,y)\wedge y\in F$. Consequently, every element of the corner $\Delta_F\,\mathcal B(H)\,\Delta_F$ relates only points of $F$.
--   2. **Restriction isomorphism.** Restricting a relation to $F\times F$ gives a monoid isomorphism
--   $$
--   \Delta_F\,\mathcal B(H)\,\Delta_F\ \cong\ \mathcal B(F).
--   $$
--   Its inverse extends a relation $a$ on $F$ to the relation $\{(x,y): x,y\in F,\ a(x,y)\}$ on $H$.
--   3. **Permutation units.** For a permutation $\pi$ of $H$, the graph $\{(x,\pi(x)):x\in H\}$ is a unit of $\mathcal B(H)$, with inverse the graph of $\pi^{-1}$.
--   4. **One-edge relations.** For $x,y\in H$, the relation $\mathrm{add}(x,y)=\Delta_H\cup\{(x,y)\}$ is the identity with one extra pair.
--   5. **Unit lifts.** A monoid homomorphism $\phi:M\to N$ *has unit lifts* if every unit of $N$ is the image of a unit of $M$.
--   6. **Rectangle frames.** A rectangle frame in $H$ with index sets $I$ and $J$ consists of injective maps $\lambda:I\to H$ and $\mu:J\to H$ with disjoint images, together with a hub point $h\in H$ outside both images. Its base relation is $\Delta_{H\setminus\{h\}}$. For $E\subseteq I\times J$ its rectangle relation is
--   $$
--   R_E=\Delta_{H\setminus\{h\}}\ \cup\ \{(\lambda(i),\mu(j)):\ (i,j)\in E\}.
--   $$
--   7. **Corners of corners.** Let $q$ be an idempotent of the corner $eMe$ of a monoid $M$. Then the corner of $eMe$ at $q$ is isomorphic to the corner of $M$ at $q$, via the identity on underlying elements.
--
--   These objects drive the induction on $|H|$ in the rank-loss argument. A corner of $\mathcal B(H)$ at a partial identity is again a full relation monoid, now on a smaller set. One-edge relations are the idempotents whose lifts must lose rank. Rectangle frames supply many one-edge-type idempotents at once, which are used to amplify the loss.
--
--   **Formalization Note** Relations are the structure `BRel H` with field `holds`. The objects are `BRel.restrictedId F`, `BRel.restriction`, `BRel.extend`, `BRel.extension` and `BRel.restrictionEquiv` (a `MulEquiv`), `BRel.permGraph`, `BRel.permUnit`, `BRel.addEdge`, `HasUnitLifts`, `RectangleFrame` with fields `left`, `right` and `hub` together with `base` and `rel`, and `Corner.flattenEquiv`. No finiteness is assumed. The simp lemmas `restrictedId_holds`, `permGraph_holds`, `addEdge_holds` and `rel_holds` unfold the definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Relations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Relations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners

namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}

@[simp] lemma restrictedId_holds (F : Set H) (x y : H) :
    (restrictedId F).holds x y ↔ x = y ∧ x ∈ F := Iff.rfl
lemma restrictedId_idem (F : Set H) : restrictedId F * restrictedId F = restrictedId F := by
  ext x z; simp

lemma restrictedId_mul (F : Set H) (a : BRel H) (x y : H) :
    (restrictedId F * a).holds x y ↔ x ∈ F ∧ a.holds x y := by simp
lemma mul_restrictedId (F : Set H) (a : BRel H) (x y : H) :
    (a * restrictedId F).holds x y ↔ a.holds x y ∧ y ∈ F := by simp

lemma corner_supported {F : Set H} (z : Corner (restrictedId F) (restrictedId_idem F))
    {x y : H} (h : z.val.holds x y) : x ∈ F ∧ y ∈ F := by
  constructor
  · have h' : (restrictedId F * z.val).holds x y := by rw [z.left]; exact h
    exact ((restrictedId_mul F _ x y).mp h').1
  · have h' : (z.val * restrictedId F).holds x y := by rw [z.right]; exact h
    exact ((mul_restrictedId F _ x y).mp h').2

def restriction (F : Set H) : Corner (restrictedId F) (restrictedId_idem F) →* BRel F where
  toFun z := ⟨fun x y => z.val.holds x.val y.val⟩
  map_one' := by ext x y; change (x.val = y.val ∧ x.val ∈ F) ↔ x = y; simp [Subtype.ext_iff]
  map_mul' z w := by
    ext x y
    change (∃ k : H, z.val.holds x.val k ∧ w.val.holds k y.val) ↔
      ∃ k : F, z.val.holds x.val k.val ∧ w.val.holds k.val y.val
    constructor
    · rintro ⟨k, hz, hw⟩
      exact ⟨⟨k, (corner_supported z hz).2⟩, hz, hw⟩
    · rintro ⟨k, hz, hw⟩
      exact ⟨k.val, hz, hw⟩

def extend (F : Set H) (a : BRel F) : BRel H :=
  ⟨fun x y => ∃ hx : x ∈ F, ∃ hy : y ∈ F, a.holds ⟨x, hx⟩ ⟨y, hy⟩⟩

def extension (F : Set H) (a : BRel F) : Corner (restrictedId F) (restrictedId_idem F) :=
  ⟨extend F a, by ext x y; simp only [restrictedId_mul]; exact ⟨And.right, fun h => ⟨h.choose, h⟩⟩,
    by ext x y; simp only [mul_restrictedId]; exact ⟨And.left, fun h => ⟨h, h.choose_spec.choose⟩⟩⟩

def restrictionEquiv (F : Set H) : Corner (restrictedId F) (restrictedId_idem F) ≃* BRel F :=
  { restriction F with
    invFun := extension F
    left_inv := by
      intro z
      apply Corner.ext
      ext x y
      change (∃ hx : x ∈ F, ∃ hy : y ∈ F, z.val.holds x y) ↔ z.val.holds x y
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(corner_supported z h).1, (corner_supported z h).2, h⟩⟩
    right_inv := by
      intro a
      ext x y
      change (∃ hx : x.val ∈ F, ∃ hy : y.val ∈ F, a.holds ⟨x.val, hx⟩ ⟨y.val, hy⟩) ↔ a.holds x y
      simp }

end BRel

namespace BRel
variable {H : Type*}
def permGraph (σ : Equiv.Perm H) : BRel H := ⟨fun x y => σ x = y⟩
@[simp] lemma permGraph_holds (σ : Equiv.Perm H) (x y : H) :
    (permGraph σ).holds x y ↔ σ x = y := Iff.rfl

def permUnit (σ : Equiv.Perm H) : (BRel H)ˣ where
  val := permGraph σ
  inv := permGraph σ.symm
  val_inv := by ext x y; simp
  inv_val := by ext x y; simp

/-- The identity with one extra pair. -/
def addEdge (x y : H) : BRel H := ⟨fun u v => u = v ∨ u = x ∧ v = y⟩
@[simp] lemma addEdge_holds (x y u v : H) :
    (addEdge x y).holds u v ↔ u = v ∨ u = x ∧ v = y := Iff.rfl
end BRel

/-- Every target unit admits a unit lift (unitality included in the homomorphism). -/
def HasUnitLifts {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) : Prop :=
  ∀ u : Nˣ, ∃ v : Mˣ, f (↑v) = (↑u)

/-- Disjoint source/target points and a separate intermediate hub. -/
structure RectangleFrame (H I J : Type*) where
  left : I → H
  right : J → H
  hub : H
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  disjoint : ∀ i j, left i ≠ right j
  left_ne_hub : ∀ i, left i ≠ hub
  right_ne_hub : ∀ j, right j ≠ hub

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
def base : BRel H := BRel.restrictedId {x | x ≠ F.hub}
def rel (E : Set (I × J)) : BRel H :=
  ⟨fun x y => (x = y ∧ x ≠ F.hub) ∨ ∃ p ∈ E, x = F.left p.1 ∧ y = F.right p.2⟩

@[simp] lemma rel_holds (E : Set (I × J)) (x y : H) :
    (F.rel E).holds x y ↔ (x = y ∧ x ≠ F.hub) ∨ ∃ p ∈ E, x = F.left p.1 ∧ y = F.right p.2 := Iff.rfl
end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

def flattenEquiv (q : Corner e he) (hq : q * q = q) :
    Corner q hq ≃* Corner q.val (val_idempotent q hq) where
  toFun z := ⟨z.val.val, congrArg Corner.val z.left, congrArg Corner.val z.right⟩
  invFun z :=
    ⟨⟨z.val, by
      calc
        e * z.val = e * (q.val * z.val) := by rw [z.left]
        _ = z.val := by rw [← mul_assoc, q.left, z.left], by
      calc
        z.val * e = (z.val * q.val) * e := by rw [z.right]
        _ = z.val := by rw [mul_assoc, q.right, z.right]⟩,
      Corner.ext z.left, Corner.ext z.right⟩
  left_inv z := Corner.ext (Corner.ext rfl)
  right_inv z := Corner.ext rfl
  map_mul' _ _ := Corner.ext rfl
end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI


