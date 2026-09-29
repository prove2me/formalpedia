-- Prove2me | Definitions.Def_PDivisibleGroup_CompletedPoints
-- name    : PDivisibleGroup_CompletedPoints
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6fd4d738-83af-5a49-b131-af4f4e329368
-- title:
--   Completed points of a p-divisible group
-- statement:
--   Fix a commutative ring $R$, natural numbers $p,h$, a $p$-divisible group $G$ over $R$ of height $h$ in the sense of the structure [`PDivisibleGroup`](../def/PDivisibleGroup_Basic.html#L199) (a tower of finite free cocommutative Hopf $R$-algebras `G.level v` with surjective bialgebra transitions, prescribed ranks $p^{vh}$ and kernels the $p^v$-torsion ideals), and a commutative $R$-algebra $S$. For each $i$ the quotient $S/(p^i)$ is an $R$-algebra; `reduceModPow` is the induced $R$-algebra map $S/(p^{i+1}) \to S/(p^i)$, obtained from the inclusion of ideals $(p^{i+1}) \subseteq (p^i)$, and for an $R$-algebra map $\varphi : S \to S'$, `mapModPow` is the induced map $S/(p^i) \to S'/(p^i)$; the two are functorial (identity, composition) and commute with each other. Writing $G.\mathrm{Points}\,L$ for the direct limit $\varinjlim_v G.\mathrm{Point}\,L\,v$ of the groups of $L$-points of the finite levels, `CPoints` is the additive subgroup of $\prod_{i \in \mathbb{N}} G.\mathrm{Points}\,(S/(p^i))$ consisting of the families $(x_i)$ with $\mathrm{red}_i(x_{i+1}) = x_i$ for all $i$; this is the inverse limit over the $p$-power quotients, i.e. the group of completed $S$-valued points. Accompanying declarations give the membership criterion, extensionality, the projections `cpointsProj` to each $G.\mathrm{Points}\,(S/(p^i))$ together with their compatibility with the reductions, and the vanishing of the $0$th projection (since $S/(p^0)$ is the zero ring). Further, `toCPoints` is the homomorphism $G.\mathrm{Points}\,S \to$ `CPoints` reducing a point modulo every $p^i$; `cpointsMap` is the functorial map along $\varphi : S \to S'$, compatible with identities, composition, the projections and `toCPoints`; and the group $S \simeq_{\mathrm{alg}[R]} S$ of $R$-algebra automorphisms of $S$ acts distributively on `CPoints` through `cpointsMap`, compatibly with `toCPoints` and the action on $G.\mathrm{Points}\,S$.
--
--   **Relation to Mathlib.** Mathlib has no notion of $p$-divisible group or of its points; the constructions here are the project's own, built on Mathlib's quotient $R$-algebra maps (`Ideal.Quotient.factorₐ`, `Ideal.quotientMapₐ`) and additive subgroups.
--
--   **Where it is used.** These completed points are Tate's group of $S$-valued points of a $p$-divisible group, used in the local analysis at $p$ of the Galois representations arising from $p$-divisible groups, with $S$ taken to be $\mathbb{Z}_p$ or the integral closure of $\mathbb{Z}_p$ in an algebraic closure of $\mathbb{Q}_p$; the automorphism action is what makes the resulting Tate module a Galois module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PDivisibleGroup_CompletedPoints.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section Reduce

variable (p)
variable (S : Type) [CommRing S] [Algebra R S]

theorem span_pow_succ_le (i : ℕ) :
    Ideal.span {(p : S) ^ (i + 1)} ≤ Ideal.span {(p : S) ^ i} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ i))

theorem span_pow_le_comap {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ) :
    Ideal.span {(p : S) ^ i} ≤ (Ideal.span {(p : S') ^ i}).comap φ := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
    map_natCast]
  exact Ideal.mem_span_singleton_self _

variable (R)

def reduceModPow (i : ℕ) :
    (S ⧸ Ideal.span {(p : S) ^ (i + 1)}) →ₐ[R] (S ⧸ Ideal.span {(p : S) ^ i}) :=
  Ideal.Quotient.factorₐ R (span_pow_succ_le p S i)

@[simp] theorem reduceModPow_mk (i : ℕ) (s : S) :
    reduceModPow R p S i (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ s := rfl

theorem reduceModPow_comp_mkₐ (i : ℕ) :
    (reduceModPow R p S i).comp (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ (i + 1)})) =
      Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i}) := rfl

def mapModPow {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ) :
    (S ⧸ Ideal.span {(p : S) ^ i}) →ₐ[R] (S' ⧸ Ideal.span {(p : S') ^ i}) :=
  Ideal.quotientMapₐ (Ideal.span {(p : S') ^ i}) φ (span_pow_le_comap p S φ i)

@[simp] theorem mapModPow_mk {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ)
    (s : S) : mapModPow R p S φ i (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (φ s) := rfl

theorem mapModPow_id (i : ℕ) : mapModPow R p S (AlgHom.id R S) i = AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl

theorem mapModPow_comp {S' S'' : Type} [CommRing S'] [Algebra R S'] [CommRing S''] [Algebra R S'']
    (φ : S →ₐ[R] S') (ψ : S' →ₐ[R] S'') (i : ℕ) :
    mapModPow R p S (ψ.comp φ) i = (mapModPow R p S' ψ i).comp (mapModPow R p S φ i) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl

theorem reduceModPow_comp_mapModPow {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (i : ℕ) :
    (reduceModPow R p S' i).comp (mapModPow R p S φ (i + 1)) =
      (mapModPow R p S φ i).comp (reduceModPow R p S i) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl

end Reduce

variable (G : PDivisibleGroup R p h) (S : Type) [CommRing S] [Algebra R S]

def CPoints : AddSubgroup (∀ i : ℕ, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) where
  carrier := {x | ∀ i, G.pointsMap (reduceModPow R p S i) (x (i + 1)) = x i}
  add_mem' {x y} hx hy i := by rw [Pi.add_apply, Pi.add_apply, map_add, hx i, hy i]
  zero_mem' i := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  neg_mem' {x} hx i := by rw [Pi.neg_apply, Pi.neg_apply, map_neg, hx i]

theorem mem_cpoints_iff (x : ∀ i : ℕ, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) :
    x ∈ G.CPoints S ↔ ∀ i, G.pointsMap (reduceModPow R p S i) (x (i + 1)) = x i := Iff.rfl

theorem CPoints.pointsMap_reduceModPow_succ (x : G.CPoints S) (i : ℕ) :
    G.pointsMap (reduceModPow R p S i) ((x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) (i + 1)) =
      (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i :=
  x.2 i

@[ext] theorem CPoints.ext {x y : G.CPoints S}
    (hxy : ∀ i, (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i =
      (y : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i) : x = y :=
  Subtype.ext (funext hxy)

def cpointsProj (i : ℕ) : G.CPoints S →+ G.Points (S ⧸ Ideal.span {(p : S) ^ i}) where
  toFun x := (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cpointsProj_apply (i : ℕ) (x : G.CPoints S) :
    G.cpointsProj S i x = (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i := rfl

@[simp] theorem pointsMap_reduceModPow_cpointsProj_succ (i : ℕ) (x : G.CPoints S) :
    G.pointsMap (reduceModPow R p S i) (G.cpointsProj S (i + 1) x) = G.cpointsProj S i x :=
  x.2 i

theorem cpointsProj_ext {x y : G.CPoints S} (hxy : ∀ i, G.cpointsProj S i x = G.cpointsProj S i y) :
    x = y :=
  CPoints.ext G S hxy

theorem cpointsProj_zero (x : G.CPoints S) : G.cpointsProj S 0 x = 0 := by
  have h1 : Ideal.span {(p : S) ^ 0} = ⊤ := by rw [pow_zero, Ideal.span_singleton_one]
  haveI : Subsingleton (S ⧸ Ideal.span {(p : S) ^ 0}) :=
    Ideal.Quotient.subsingleton_iff.mpr h1

  have hpt : ∀ (v : ℕ) (f : G.Point (S ⧸ Ideal.span {(p : S) ^ 0}) v), f = 1 := fun v f =>
    Point.ext fun a => Subsingleton.elim _ _
  induction (G.cpointsProj S 0 x) using Points.induction_on with
  | ih v f => rw [hpt v f, ofMul_one, map_zero]

def toCPoints : G.Points S →+ G.CPoints S where
  toFun z := ⟨fun i => G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) z, fun i => by
    change G.pointsMap (reduceModPow R p S i)
        (G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ (i + 1)})) z) = _
    rw [← AddMonoidHom.comp_apply, ← pointsMap_comp, reduceModPow_comp_mkₐ]⟩
  map_zero' := Subtype.ext (funext fun i => by simp)
  map_add' x y := Subtype.ext (funext fun i => by simp)

@[simp] theorem cpointsProj_toCPoints (i : ℕ) (z : G.Points S) :
    G.cpointsProj S i (G.toCPoints S z) =
      G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) z := rfl

section Map

variable {S}
variable {S' : Type} [CommRing S'] [Algebra R S'] {S'' : Type} [CommRing S''] [Algebra R S'']

def cpointsMap (φ : S →ₐ[R] S') : G.CPoints S →+ G.CPoints S' where
  toFun x := ⟨fun i => G.pointsMap (mapModPow R p S φ i) (G.cpointsProj S i x), fun i => by
    change G.pointsMap (reduceModPow R p S' i)
        (G.pointsMap (mapModPow R p S φ (i + 1)) (G.cpointsProj S (i + 1) x)) = _
    rw [← AddMonoidHom.comp_apply, ← pointsMap_comp, reduceModPow_comp_mapModPow, pointsMap_comp,
      AddMonoidHom.comp_apply, pointsMap_reduceModPow_cpointsProj_succ]⟩
  map_zero' := Subtype.ext (funext fun i => by simp)
  map_add' x y := Subtype.ext (funext fun i => by simp)

@[simp] theorem cpointsProj_cpointsMap (φ : S →ₐ[R] S') (i : ℕ) (x : G.CPoints S) :
    G.cpointsProj S' i (G.cpointsMap φ x) = G.pointsMap (mapModPow R p S φ i) (G.cpointsProj S i x) :=
  rfl

theorem cpointsMap_id : G.cpointsMap (AlgHom.id R S) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun x => cpointsProj_ext G S fun i => ?_
  rw [cpointsProj_cpointsMap, mapModPow_id, pointsMap_id]
  rfl

theorem cpointsMap_comp (φ : S →ₐ[R] S') (ψ : S' →ₐ[R] S'') :
    G.cpointsMap (ψ.comp φ) = (G.cpointsMap ψ).comp (G.cpointsMap φ) := by
  refine AddMonoidHom.ext fun x => cpointsProj_ext G S'' fun i => ?_
  rw [cpointsProj_cpointsMap, mapModPow_comp, pointsMap_comp]
  rfl

theorem cpointsMap_toCPoints (φ : S →ₐ[R] S') (z : G.Points S) :
    G.cpointsMap φ (G.toCPoints S z) = G.toCPoints S' (G.pointsMap φ z) := by
  refine cpointsProj_ext G S' fun i => ?_
  rw [cpointsProj_cpointsMap, cpointsProj_toCPoints, cpointsProj_toCPoints, ← AddMonoidHom.comp_apply,
    ← AddMonoidHom.comp_apply, ← pointsMap_comp, ← pointsMap_comp]
  rfl

end Map

instance CPoints.instDistribMulAction : DistribMulAction (S ≃ₐ[R] S) (G.CPoints S) where
  smul σ x := G.cpointsMap (σ : S →ₐ[R] S) x
  one_smul x := by
    change G.cpointsMap ((1 : S ≃ₐ[R] S) : S →ₐ[R] S) x = x
    rw [show ((1 : S ≃ₐ[R] S) : S →ₐ[R] S) = AlgHom.id R S from rfl, cpointsMap_id]
    rfl
  mul_smul σ τ x := by
    change G.cpointsMap ((σ * τ : S ≃ₐ[R] S) : S →ₐ[R] S) x =
      G.cpointsMap (σ : S →ₐ[R] S) (G.cpointsMap (τ : S →ₐ[R] S) x)
    rw [show ((σ * τ : S ≃ₐ[R] S) : S →ₐ[R] S) = (σ : S →ₐ[R] S).comp (τ : S →ₐ[R] S) from rfl,
      cpointsMap_comp]
    rfl
  smul_zero σ := map_zero (G.cpointsMap (σ : S →ₐ[R] S))
  smul_add σ x y := map_add (G.cpointsMap (σ : S →ₐ[R] S)) x y

theorem CPoints.smul_def (σ : S ≃ₐ[R] S) (x : G.CPoints S) :
    σ • x = G.cpointsMap (σ : S →ₐ[R] S) x := rfl

theorem CPoints.smul_toCPoints (σ : S ≃ₐ[R] S) (z : G.Points S) :
    σ • G.toCPoints S z = G.toCPoints S (σ • z) := by
  rw [CPoints.smul_def, cpointsMap_toCPoints, Points.smul_def]

end PDivisibleGroup

end


