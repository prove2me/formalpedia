-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Model
-- name    : OAI_Combinatorics_Automata_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:12.219974+00:00
-- url     : https://prove2.me/theorems/074731c5-0a22-40fd-b8d5-c1091b9c2557
-- title:
--   Empty relation, partial identities and finiteness of the relation monoid
-- statement:
--   For a set $H$, let $\mathcal{R}(H)$ be the monoid of binary relations on $H$ introduced in the base definitions. A relation $a\in\mathcal{R}(H)$ is a predicate $a(x,y)$ on pairs $x,y\in H$; the product is relational composition in path order (first $a$, then $b$), and the identity $1$ is equality. This file adds the following elementary structure.
--
--   1. **Membership rules.** For all $a,b\in\mathcal{R}(H)$ and $x,y,z\in H$,
--   $$1(x,y)\iff x=y,\qquad (ab)(x,z)\iff \exists\,y\in H:\ a(x,y)\ \text{and}\ b(y,z).$$
--   2. **Zero relation.** The empty relation $0\in\mathcal{R}(H)$, for which $0(x,y)$ fails for all $x,y\in H$.
--   3. **Partial identity.** For a subset $F\subseteq H$, the diagonal relation of $F$:
--   $$\mathrm{Id}_F(x,y)\iff x=y\ \text{and}\ x\in F .$$
--   4. **Finiteness.** If $H$ is finite, then $\mathcal{R}(H)$ is a finite set.
--
--   One-way liveness asks whether the ordered product of a word of relations is nonempty, that is, different from the zero relation. The partial identities are idempotents of $\mathcal{R}(H)$; they are used to cut out corners $\mathrm{Id}_F\,\mathcal{R}(H)\,\mathrm{Id}_F$ that behave like the relation monoid of the smaller set $F$. Finiteness of $\mathcal{R}(H)$ makes the standard finite-monoid arguments, such as the existence of idempotent powers, available inside it.
--
--   **Formalization Note** A relation is the structure `BRel H` with the single field `holds`. The rules of items 1 and 2 are the simp lemmas `one_holds`, `mul_holds` and `zero_holds`; the zero relation is a `Zero` instance, $\mathrm{Id}_F$ is `restrictedId F` for `F : Set H`, and item 4 is a `Finite` instance assuming `[Finite H]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness

namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}
instance : Zero (BRel H) := ⟨⟨fun _ _ => False⟩⟩
@[simp] theorem one_holds (x y : H) : (1 : BRel H).holds x y ↔ x = y := Iff.rfl
@[simp] theorem mul_holds (a b : BRel H) (x z : H) :
    (a * b).holds x z ↔ ∃ y, a.holds x y ∧ b.holds y z := Iff.rfl
@[simp] theorem zero_holds (x y : H) : ¬ (0 : BRel H).holds x y := id
def restrictedId (F : Set H) : BRel H := ⟨fun x y => x = y ∧ x ∈ F⟩
instance [Finite H] : Finite (BRel H) := Finite.of_injective BRel.holds (fun _ _ h => BRel.ext h)

end BRel

end OneWayLiveness

end OAI


