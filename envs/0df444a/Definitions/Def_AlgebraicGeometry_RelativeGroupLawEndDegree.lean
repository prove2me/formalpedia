-- Prove2me | Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
-- name    : AlgebraicGeometry_RelativeGroupLawEndDegree
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/b7219beb-8ae9-58ac-bfdf-d5907e22e177
-- title:
--   Kernels and degrees of endomorphisms for relative group laws
-- statement:
--   The setting is a scheme $A$ over $\operatorname{Spec} R$ ($R$ a commutative ring) equipped with a `RelativeGroupLaw`, i.e. a group structure on each set $\mathrm{SchemeHomOver}\,t\,f$ of sections of $f\colon A \to \operatorname{Spec} R$ over a base-change morphism $t$, natural in $t$. Two pieces of bookkeeping come first: `schemeHomOverNpow` is the $i$-fold composite of an endomorphism $\beta$ of $f$ over the base (with the identity for $i = 0$), and `pointCommGroup` records that for a commutative law the point group at $t$ is a commutative group. Using both, `endAeval` evaluates a polynomial $p \in \mathbb{Z}[X]$ at $\beta$ inside the abelian group $\mathrm{SchemeHomOver}\,f\,f$ of endomorphisms of $f$: it is the group-law product $\prod_{i=0}^{\deg p} (\beta^{\circ i})^{p_i}$, the exponentiation being the integer power for the group law and $\beta^{\circ i}$ the $i$-fold composite; `endAeval_X` checks that $X \mapsto \beta$.
--
--   Next, `endKer` is the fibre product of $\beta$ with the unit section $\operatorname{Spec} R \to A$ of the group law at the identity base morphism, with `endKerStr` its second projection to $\operatorname{Spec} R$ and `endKerι` its first projection to $A$; the two projections satisfy the pullback relation, and composing $\mathrm{endKer}\iota$ with $f$ gives back the structure morphism. For $\beta = [n]\cdot\mathrm{id}$ this kernel is, by construction, the $n$-torsion subscheme `schemeKer n`.
--
--   Finally, over a base field $K$, `endDegree` of $\beta$ is the $K$-rank of `endKerStr` at the closed point of $\operatorname{Spec} K$ when that morphism is finite, and $0$ otherwise. Accompanying lemmas unfold this case distinction, note that the kernel of the identity endomorphism has invertible structure morphism, and deduce that the identity has degree $1$.
--
--   **Relation to Mathlib.** The relative group law, its point groups, and the endomorphism kernel and degree are the project's own notions; Mathlib's `IsFinite` for morphisms of schemes and `Scheme.Hom.finrank` supply the finiteness condition and the rank used in the definition of the degree.
--
--   **Where it is used.** This is part of the scheme-theoretic group-law infrastructure supporting good reduction and Néron models for Jacobians: kernels of endomorphisms give the torsion subschemes whose points carry the Galois representations used in the modularity and level-lowering arguments, and the degree convention (zero off isogenies) makes the degree available on the whole endomorphism ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace NeronModelInfra

variable {B X : Scheme.{u}} {f : X ⟶ B}

def schemeHomOverNpow (β : SchemeHomOver f f) : ℕ → SchemeHomOver f f
  | 0 => schemeHomOverId f
  | i + 1 => schemeHomOverComp (schemeHomOverNpow β i) β

@[simp] theorem schemeHomOverNpow_zero (β : SchemeHomOver f f) :
    schemeHomOverNpow β 0 = schemeHomOverId f := rfl

@[simp] theorem schemeHomOverNpow_succ (β : SchemeHomOver f f) (i : ℕ) :
    schemeHomOverNpow β (i + 1) = schemeHomOverComp (schemeHomOverNpow β i) β := rfl

end NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

@[reducible]
def pointCommGroup (G : RelativeGroupLaw R f) (hc : G.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { G.pointGroup t with mul_comm := fun x y => hc t x y }

def endAeval (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f)
    (p : Polynomial ℤ) : SchemeHomOver f f :=
  letI := G.pointCommGroup hc f
  ∏ i ∈ Finset.range (p.natDegree + 1), NeronModelInfra.schemeHomOverNpow β i ^ p.coeff i

theorem endAeval_X (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f) :
    G.endAeval hc β Polynomial.X = β := by
  letI := G.pointCommGroup hc f
  rw [endAeval, Polynomial.natDegree_X, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, Polynomial.coeff_X_zero, Polynomial.coeff_X_one, zpow_zero, zpow_one,
    _root_.one_mul, _root_.one_mul, NeronModelInfra.schemeHomOverNpow_succ,
    NeronModelInfra.schemeHomOverNpow_zero, NeronModelInfra.schemeHomOverComp_id_left]

abbrev endKer (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : Scheme.{u} :=
  pullback β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerStr (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKer β ⟶ Spec (CommRingCat.of R) :=
  pullback.snd β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerι (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : G.endKer β ⟶ A :=
  pullback.fst β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

theorem endKer_nsmul_idPoint (G : RelativeGroupLaw R f) (n : ℕ) :
    G.endKer (G.nsmul f n idPoint) = G.schemeKer n :=
  rfl

theorem endKerι_comp (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ β.1 = G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  pullback.condition

theorem endKerι_comp_base (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ f = G.endKerStr β := by
  calc G.endKerι β ≫ f = G.endKerι β ≫ (β.1 ≫ f) := by rw [β.2]
    _ = (G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
        rw [← Category.assoc, endKerι_comp]
    _ = G.endKerStr β := by rw [Category.assoc, (G.one _).2, Category.comp_id]

end General

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

def endDegree (G : RelativeGroupLaw K f) (β : SchemeHomOver f f) : ℕ := by
  classical
  exact if IsFinite (G.endKerStr β) then (G.endKerStr β).finrank (IsLocalRing.closedPoint K) else 0

theorem endDegree_of_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [h : IsFinite (G.endKerStr β)] :
    G.endDegree β = (G.endKerStr β).finrank (IsLocalRing.closedPoint K) := by
  rw [endDegree, if_pos h]

theorem endDegree_of_not_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    (h : ¬ IsFinite (G.endKerStr β)) : G.endDegree β = 0 := by
  rw [endDegree, if_neg h]

instance isIso_endKerStr_schemeHomOverId (G : RelativeGroupLaw K f) :
    IsIso (G.endKerStr (schemeHomOverId f)) := by
  change IsIso (pullback.snd (𝟙 A) (G.one (𝟙 (Spec (CommRingCat.of K)))).1)
  infer_instance

theorem endDegree_schemeHomOverId (G : RelativeGroupLaw K f) :
    G.endDegree (schemeHomOverId f) = 1 := by
  haveI : IsFinite (G.endKerStr (schemeHomOverId f)) := inferInstance
  rw [endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Field

end RelativeGroupLaw
end GoodReductionJacobian

end


