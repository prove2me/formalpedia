-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Diagram
-- name    : OAI_Combinatorics_Automata_Diagram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:57:45.544132+00:00
-- url     : https://prove2.me/theorems/36b6ff0d-30b6-4d78-b79d-96d21892c630
-- title:
--   The matching-diagram monoid, marked transversal paths and reduction at an idempotent
-- statement:
--   Let $A$ and $B$ be finite sets. Matching diagrams, their gluing composite $ab$ in path order, the gluing graph $G(v,u)$, the identity $\mathrm{id}_A$, the set $L(e)$ of left transversal endpoints and the split diagrams $\lambda_e$, $\rho_e$ are as in the preceding files.
--
--   1. **Marked indices.** For a diagram $v$ from $A$ to $B$, a diagram $u$ from $B$ to $A$ and a subset $J\subseteq B$,
--   $$\operatorname{mk}(v,u,J)=\{x\in A:\ \exists\, i\in J \text{ such that the outer left port } x \text{ is connected in } G(v,u) \text{ to the copy of } i \text{ among the right ports of } v\}.$$
--   These are the outer left ports whose path in the glued wiring passes through the interface edge of some index in $J$. The set is defined once from $v$, $u$ and $J$, independently of any diagram later inserted between $v$ and $u$.
--
--   2. **The diagram monoid.** The diagrams on $A\sqcup A$ form a monoid $\mathcal{D}(A)$ with product $ab$ and identity $\mathrm{id}_A$; this is the Brauer monoid on $A$ with closed loops discarded.
--
--   3. **Reduction and expansion.** For $e\in\mathcal{D}(A)$ with $X=L(e)$,
--   $$\operatorname{red}_e(z)=\rho_e\,z\,\lambda_e\in\mathcal{D}(X)\quad(z\in\mathcal{D}(A)),\qquad \operatorname{exp}_e(y)=\lambda_e\,y\,\rho_e\in\mathcal{D}(A)\quad(y\in\mathcal{D}(X)).$$
--
--   4. **Properties.** If $ee=e$, then $\rho_e\,e=\rho_e$ and $\operatorname{red}_e(e)=\mathrm{id}_X$. For all $e,x,y\in\mathcal{D}(A)$ with $xe=x$ (no idempotence of $e$ is needed here),
--   $$\operatorname{red}_e(xy)=\operatorname{red}_e(x)\,\operatorname{red}_e(y).$$
--
--   Consequently, for an idempotent $e$ the reduction restricts to a multiplicative map from the corner $e\,\mathcal{D}(A)\,e$, whose identity is $e$, to $\mathcal{D}(L(e))$ that sends $e$ to the identity: corners are realized on $\operatorname{rk}(e)$ ports by deleting the prescribed caps of $e$. The marked set controls supports of sandwiches: it is shown separately that if $vu=\mathrm{id}_A$ and a diagram $a$ on $B\sqcup B$ satisfies $\operatorname{supp}(a)\subseteq J$, then $\operatorname{supp}(vau)\subseteq\operatorname{mk}(v,u,J)$.
--
--   **Formalization Note** `marked v u J` filters `Finset.univ` by reachability in `glueGraph v u` from `outer (.inl x)` to the vertex `.inl (.inr i)`. The monoid instance on `Pairing (A ⊕ A)` has multiplication `compose` and unit `identity A` (simp lemmas `mul_eq_compose`, `one_eq_identity`). `reduce e z` and `expand e z` are defined for arbitrary `e` and `z`, with the reduced diagrams in `Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e})`; item 4 consists of `splitRight_absorb`, `reduce_self` and `reduce_mul`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Diagram.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Diagram.lean by skeleton subtraction
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

namespace OAI

namespace OneWayLiveness

namespace FiniteWiring
variable {V C : Type*} (G : SimpleGraph V)

end FiniteWiring

namespace Pairing
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Index the outer identity paths touched by a specified set of interface
edges. The definition is made once, independently of a replacement diagram. -/
noncomputable def marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A)) (J : Finset B) : Finset A :=
  Finset.univ.filter fun x => ∃ i ∈ J,
    (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i))

@[simp] lemma mem_marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A)) (J : Finset B) (x : A) :
    x ∈ marked v u J ↔ ∃ i ∈ J,
      (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i)) := by simp [marked]

end Pairing

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
noncomputable instance : Monoid (Pairing (A ⊕ A)) where
  mul := compose
  one := identity A
  mul_assoc := compose_assoc
  one_mul := identity_compose
  mul_one := compose_identity

@[simp] lemma mul_eq_compose (a b : Pairing (A ⊕ A)) : a * b = compose a b := rfl
@[simp] lemma one_eq_identity : (1 : Pairing (A ⊕ A)) = identity A := rfl

/-- Delete the prescribed caps of an idempotent.  Its retained left endpoints
are used as the smaller index set, avoiding an arbitrary numbering. -/
noncomputable def reduce (e z : Pairing (A ⊕ A)) :
    Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e}) :=
  compose (compose (splitRight e) z) (splitLeft e)

noncomputable def expand (e : Pairing (A ⊕ A))
    (z : Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e})) : Pairing (A ⊕ A) :=
  compose (compose (splitLeft e) z) (splitRight e)

lemma splitRight_absorb (e : Pairing (A ⊕ A)) (he : e * e = e) :
    compose (splitRight e) e = splitRight e := by
  calc
    _ = compose (splitRight e) (compose (splitLeft e) (splitRight e)) :=
      congrArg (compose (splitRight e)) (splitLeft_splitRight e).symm
    _ = _ := by rw [← compose_assoc, splitRight_splitLeft e he, identity_compose]

lemma reduce_self (e : Pairing (A ⊕ A)) (he : e * e = e) : reduce e e = 1 := by
  unfold reduce
  rw [splitRight_absorb e he, splitRight_splitLeft e he]
  rfl

lemma reduce_mul (e x y : Pairing (A ⊕ A)) (hxe : x * e = x) :
    reduce e (x * y) = reduce e x * reduce e y := by
  simp only [reduce, mul_eq_compose, compose_assoc]
  rw [← compose_assoc (splitLeft e), splitLeft_splitRight e,
    ← compose_assoc x e, ← mul_eq_compose x e, hxe]

end Pairing

end OneWayLiveness

end OAI


