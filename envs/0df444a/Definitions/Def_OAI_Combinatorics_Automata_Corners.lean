-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Corners
-- name    : OAI_Combinatorics_Automata_Corners
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:01:28.983608+00:00
-- url     : https://prove2.me/theorems/b4ee3704-365f-4c26-b556-ae952ee75856
-- title:
--   Corner monoids at idempotents, restricted homomorphisms and transfer across a split pair
-- statement:
--   Let $M$ be a monoid and let $e\in M$ be an idempotent, $e^2=e$.
--
--   1. **Corner (local monoid).** The corner of $M$ at $e$ is
--   $$
--   eMe=\{x\in M:\ ex=x=xe\}.
--   $$
--   It is a monoid under the multiplication of $M$, with identity element $e$ (not the identity of $M$), and it is finite when $M$ is finite. For any $x\in M$ the *sandwich* $exe$ lies in $eMe$.
--   2. **Restricted homomorphisms.** Let $\phi:M\to N$ be a monoid homomorphism and let $q\in N$ be an idempotent with $\phi(e)=q$. Then $x\mapsto\phi(x)$ is a monoid homomorphism $\phi_e:eMe\to qNq$. An idempotent of the corner $eMe$ is also an idempotent of $M$.
--   3. **Reduction of a diagram corner.** Let $A$ be a finite set and let $\mathcal P(A)$ be the monoid of diagrams on $A$: perfect matchings of $A\sqcup A$, multiplied by gluing. Let $\rho:M\to\mathcal P(A)$ be a monoid homomorphism. Then $\rho(e)$ is idempotent. Let $L\subseteq A$ be the set of left ports of $\rho(e)$ that are matched to right ports (its through-strands). The map
--   $$
--   \bar\rho_e:\ eMe\to\mathcal P(L),\qquad x\mapsto\operatorname{red}_{\rho(e)}\big(\rho(x)\big),
--   $$
--   is a monoid homomorphism. Here $\operatorname{red}_E(z)=S_R(E)\,z\,S_L(E)$ is the reduction from the earlier rank definitions. The diagram $S_L(E)$ keeps the left caps of $E$ and joins each $i\in L$ straight to its copy in $L$. The diagram $S_R(E)$ keeps the right caps and the through-strands of $E$. Thus $E=S_L(E)\,S_R(E)$, and $\operatorname{red}_E$ compresses a diagram onto the through-strand positions of $E$.
--   4. **Transfer across a split pair.** Let $e,f\in M$ be idempotents and let $u,v\in M$ satisfy
--   $$
--   uv=e,\qquad vu=f,\qquad uf=u,\qquad fv=v.
--   $$
--   Then $x\mapsto vxu$ is a monoid homomorphism $eMe\to fMf$. It is in fact an isomorphism $eMe\cong fMf$, with inverse $y\mapsto uyv$.
--
--   The rank-loss argument runs inside corners. One replaces a monoid by its corner at a well-chosen idempotent. Restricted homomorphisms keep track of the quotient map onto relations. The reduction $\bar\rho_e$ represents the corner by diagrams on only $\operatorname{rank}\rho(e)$ points instead of $|A|$. Item 4 is the standard fact from semigroup theory that the idempotents $uv$ and $vu$ have isomorphic local monoids.
--
--   **Formalization Note** The corner is the structure `Corner e he` (an element `val` with proofs `left : e * val = val` and `right : val * e = val`), with its `Monoid` and `Finite` instances. The other objects are `Corner.sandwich`, `Corner.mapTo`, `Pairing.reduceHom`, `Corner.transfer` and the `MulEquiv` `Corner.equivOfSplit`. The simp lemmas `val_one`, `val_mul` and `mapTo_val`, and the facts `val_idempotent` and `Pairing.image_idempotent`, are bookkeeping.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Corners.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Corners.lean by skeleton subtraction
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

namespace OAI

namespace OneWayLiveness

/-- The local monoid at an idempotent, with its genuine local identity. -/
@[ext] structure Corner {M : Type*} [Monoid M] (e : M) (he : e * e = e) where
  val : M
  left : e * val = val
  right : val * e = val

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}
instance : CoeOut (Corner e he) M := ⟨Corner.val⟩
instance : Monoid (Corner e he) where
  one := ⟨e, he, he⟩
  mul x y := ⟨x.val * y.val, by rw [← mul_assoc, x.left], by rw [mul_assoc, y.right]⟩
  mul_assoc _ _ _ := Corner.ext (mul_assoc _ _ _)
  one_mul x := Corner.ext x.left
  mul_one x := Corner.ext x.right
@[simp] lemma val_one : (1 : Corner e he).val = e := rfl
@[simp] lemma val_mul (x y : Corner e he) : (x * y).val = x.val * y.val := rfl
instance [Finite M] : Finite (Corner e he) := Finite.of_injective Corner.val (fun _ _ h => Corner.ext h)

def sandwich (x : M) : Corner e he :=
  ⟨e * x * e, by rw [← mul_assoc, ← mul_assoc, he], by rw [mul_assoc, he]⟩

end Corner

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

def mapTo (f : M →* N) (hf : f e = q) : Corner e he →* Corner q hq where
  toFun x := ⟨f x.val, by rw [← hf, ← map_mul, x.left], by rw [← hf, ← map_mul, x.right]⟩
  map_one' := Corner.ext hf
  map_mul' x y := Corner.ext (map_mul f x.val y.val)

@[simp] lemma mapTo_val (f : M →* N) (hf : f e = q) (x : Corner e he) :
    (mapTo (he := he) (hq := hq) f hf x).val = f x.val := rfl

lemma val_idempotent (x : Corner e he) (hx : x * x = x) : x.val * x.val = x.val :=
  congrArg Corner.val hx
end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

include he in
lemma image_idempotent : ρ e * ρ e = ρ e := by rw [← map_mul, he]

noncomputable def reduceHom : Corner e he →* Pairing ({i // i ∈ lefts (ρ e)} ⊕ {i // i ∈ lefts (ρ e)}) where
  toFun x := reduce (ρ e) (ρ x.val)
  map_one' := reduce_self _ (image_idempotent ρ e he)
  map_mul' x y := by
    change reduce (ρ e) (ρ (x.val * y.val)) = _
    rw [map_mul]
    apply reduce_mul
    rw [← map_mul, x.right]

end Pairing

namespace Corner
variable {M : Type*} [Monoid M] {e f : M} {he : e * e = e} {hf : f * f = f}

/-- Transport a local monoid across a split pair. -/
def transfer (u v : M) (huv : u * v = e) (hvu : v * u = f)
    (hu : u * f = u) (hv : f * v = v) : Corner e he →* Corner f hf where
  toFun x := ⟨v * x.val * u, by rw [← mul_assoc, ← mul_assoc, hv], by rw [mul_assoc, hu]⟩
  map_one' := Corner.ext (by
    change v * e * u = f
    calc
      _ = (v * u) * (v * u) := by rw [← huv]; simp only [mul_assoc]
      _ = f := by rw [hvu, hf])
  map_mul' x y := Corner.ext (by
    change v * (x.val * y.val) * u = (v * x.val * u) * (v * y.val * u)
    calc
      _ = v * (x.val * e * y.val) * u := by rw [x.right]
      _ = v * (x.val * (u * v) * y.val) * u := congrArg (fun t => v * (x.val * t * y.val) * u) huv.symm
      _ = _ := by simp only [mul_assoc])

def equivOfSplit (u v : M) (huv : u * v = e) (hvu : v * u = f)
    (hu : u * f = u) (hv : f * v = v) : Corner e he ≃* Corner f hf := by
  have heu : e * u = u := by rw [← huv, mul_assoc, hvu, hu]
  have hve : v * e = v := by rw [← huv, ← mul_assoc, hvu, hv]
  refine { transfer (he := he) (hf := hf) u v huv hvu hu hv with
    invFun := transfer (he := hf) (hf := he) v u hvu huv hve heu
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Corner.ext
    change u * (v * x.val * u) * v = x.val
    calc
      _ = (u * v) * x.val * (u * v) := by simp only [mul_assoc]
      _ = x.val := by rw [huv, x.left, x.right]
  · intro x
    apply Corner.ext
    change v * (u * x.val * v) * u = x.val
    calc
      _ = (v * u) * x.val * (v * u) := by simp only [mul_assoc]
      _ = x.val := by rw [hvu, x.left, x.right]
end Corner

end OneWayLiveness

end OAI


