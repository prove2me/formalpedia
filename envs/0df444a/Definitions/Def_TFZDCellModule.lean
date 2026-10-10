-- Prove2me | Definitions.Def_TFZDCellModule
-- name    : TFZDCellModule
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:59:51.074974+00:00
-- url     : https://prove2.me/theorems/d878f737-123f-48ba-b4de-91fd339d8c6c
-- title:
--   OpenAI's torsion-free zero-divisor construction — cellular chain modules and Fox derivatives
-- statement:
--   The algebraic notions behind the relation-module criterion for a finite two-dimensional classifying space, used in Section 5 of OpenAI's *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026, [github.com/openai/math](https://github.com/openai/math)). The code is taken from OpenAI's Lean module `lean/OAI/Algebra/GroupRing/CellModule.lean` (Apache License 2.0), in the namespace `OAI.TorsionFreeZeroDivisors.CellModule`.
--
--   1. **Cell modules.** For a group $G$ and an index type $I$, `Module G I` is the free abelian group $\mathbb Z[G\times I]$ on pairs $(g,i)$. It models the cellular chains, in one dimension, of a $G$-cover whose cells of that dimension are indexed by $I$ and permuted freely by $G$.
--
--   2. **Translation.** `translate g` is the left action of $g\in G$ on `Module G I`, given by $(g,i)\mapsto(g'g,i)$ on generators: $(\mathrm{translate}\,g\,x)(h,i)=x(g^{-1}h,i)$.
--
--   3. **Fox derivatives.** For a homomorphism $q:F(I)\to G$ from the free group on $I$, `fox q w` is the Fox derivative of the word $w$, as an element of `Module G I`. It is characterized by $\partial(i)=(1,i)$ for a generator and the cocycle rule
--   $$\partial(wu)=\partial(w)+q(w)\cdot\partial(u).$$
--   In the Lean, it is the first component of the image of $w$ under a homomorphism to the semidirect product $\mathbb Z[G\times I]\rtimes G$ (`lift`, `Crossed`, `action`).
--
--   4. **Boundary.** `boundary q` sends $(g,i)$ to $(g\,q(i))-(g)$ in $\mathbb Z[G]$: the cellular boundary from edges to vertices of the Cayley graph. The bundle proves `boundary_fox`: the boundary of $\partial(w)$ is $(q(w))-(1)$.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, Section 5 (cellular chains of the cover as free ZG-modules, Fox derivatives); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), CellModule.lean

import Mathlib

namespace OAI



section
namespace TorsionFreeZeroDivisors.CellModule
open scoped Classical BigOperators
noncomputable section
variable {G I : Type} [Group G]
abbrev Module (G I : Type) := G×I→₀ℤ
def translate (g : G) : Module G I ≃+ Module G I :=
  Finsupp.domCongr (Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl I))
@[simp] lemma translate_apply (g : G) (x : Module G I) (p : G×I) :
    translate g x p=x (g⁻¹*p.1,p.2) := rfl
@[simp] lemma translate_single (g : G) (p : G×I) (z : ℤ) :
    translate g (Finsupp.single p z)=Finsupp.single (g*p.1,p.2) z := by
  simp only [translate,Finsupp.domCongr_apply,Finsupp.equivMapDomain_single,
    Equiv.prodCongr_apply]
  rfl
@[simp] lemma translate_one (x : Module G I) : translate 1 x=x := by ext p;simp
lemma translate_mul (g h : G) (x : Module G I) : translate (g*h) x=translate g (translate h x) := by
  ext p;simp only [translate_apply,mul_inv_rev,mul_assoc]
def action : G→*MulAut (Multiplicative (Module G I)) where
  toFun g := (translate g).toMultiplicative
  map_one' := by apply MulEquiv.ext;intro x;exact translate_one x
  map_mul' g h := by apply MulEquiv.ext;intro x;exact translate_mul g h x
variable (q : FreeGroup I→*G)
abbrev Crossed := SemidirectProduct (Multiplicative (Module G I)) G (action (I:=I))
def lift : FreeGroup I→*Crossed (G:=G) (I:=I) :=
  FreeGroup.lift (fun i=>⟨Multiplicative.ofAdd (Finsupp.single (1,i) 1),q (FreeGroup.of i)⟩)
lemma lift_right (w : FreeGroup I) : (lift q w).right=q w := by
  have h : (SemidirectProduct.rightHom.comp (lift q))=q := by
    ext i;simp [lift]
  exact DFunLike.congr_fun h w
def fox (w : FreeGroup I) : Module G I := Multiplicative.toAdd (lift q w).left
@[simp] lemma fox_one : fox q 1=0 := rfl
@[simp] lemma fox_of (i : I) : fox q (FreeGroup.of i)=Finsupp.single (1,i) 1 := by
  simp [fox,lift]
lemma fox_mul (w u : FreeGroup I) : fox q (w*u)=fox q w+translate (q w) (fox q u) := by
  simp only [fox,map_mul,SemidirectProduct.mul_left,lift_right]
  rfl
lemma fox_inv (w : FreeGroup I) : fox q w⁻¹= -translate (q w)⁻¹ (fox q w) := by
  apply (translate (q w)).injective
  have h := fox_mul q w w⁻¹
  rw [mul_inv_cancel,fox_one] at h
  rw [map_neg,←translate_mul,mul_inv_cancel,translate_one]
  exact eq_neg_of_add_eq_zero_right h.symm

def boundary : Module G I→+Module G PUnit :=
  Finsupp.liftAddHom (fun p=>
    (Finsupp.singleAddHom (p.1*q (FreeGroup.of p.2),PUnit.unit))-
    (Finsupp.singleAddHom (p.1,PUnit.unit)))
@[simp] lemma boundary_single (p : G×I) (z : ℤ) :
    boundary q (Finsupp.single p z)=Finsupp.single (p.1*q (FreeGroup.of p.2),PUnit.unit) z-
      Finsupp.single (p.1,PUnit.unit) z := by
  simp only [boundary,Finsupp.liftAddHom_apply_single,AddMonoidHom.sub_apply,Finsupp.singleAddHom_apply]
lemma boundary_translate (g : G) (x : Module G I) :
    boundary q (translate g x)=translate g (boundary q x) := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb]
  | single p z=>simp only [translate_single,boundary_single,map_sub,mul_assoc]
lemma boundary_fox (w : FreeGroup I) :
    boundary q (fox q w)=Finsupp.single (q w,PUnit.unit) 1-Finsupp.single (1,PUnit.unit) 1 := by
  induction w using FreeGroup.induction_on with
  | C1=>simp
  | of i=>simp [boundary_single]
  | inv_of i _=>
    rw [fox_inv,fox_of,map_neg,boundary_translate,boundary_single]
    simp only [one_mul]
    simp only [map_sub,translate_single,inv_mul_cancel,mul_one,map_inv,neg_sub]
  | mul w u hw hu=>
    rw [fox_mul,map_add,boundary_translate,hw,hu]
    simp only [map_sub,translate_single,mul_one,map_mul]
    abel
end
end TorsionFreeZeroDivisors.CellModule

end


end OAI


