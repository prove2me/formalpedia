-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
-- name    : GoodReductionJacobian_RelativeGroupLawAlgPointsV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d69e7e94-fa0d-56b3-abe6-8e3d3748a69b
-- title:
--   Algebra-valued points of a commutative relative group law
-- statement:
--   The setting is a commutative ring $R$, a scheme $A$ with a morphism $f\colon A\to\operatorname{Spec}R$, and a relative group law $L$ on $f$ — the project's structure recording, for every $t\colon T\to\operatorname{Spec}R$, a multiplication, unit and inversion on the set $\operatorname{SchemeHomOver}\,t\,f$ of morphisms $T\to A$ over $\operatorname{Spec}R$, subject to associativity, the unit laws, left inverses and naturality of the multiplication under base change $\psi$ with $\psi\circ t'=t$ (naturality of the unit is a consequence, proved in the group-law module); `IsCommutative` asks that every such multiplication be commutative. For a commutative $R$-algebra $T$, `AlgPoints L hc T` is the set $\operatorname{SchemeHomOver}(\operatorname{Spec}(\operatorname{algebraMap} R\,T))\,f$ of $\operatorname{Spec}T$-valued points, passed through Mathlib's `Additive` so that the group law of $L$ is written additively; the commutativity witness `hc` enters as an argument of the type and supplies the additive commutative group structure, whose addition, zero and negation are $L$'s multiplication, unit and inversion. The maps `ofPoint`, `toPoint` and `equivPoint` are the identifications with the underlying point set, and the accompanying lemmas record that $n\bullet x$ corresponds to $L$'s iterated multiplication `L.nsmul`.
--
--   The torsion dictionary states that $n\bullet x=0$, that $(n:\mathbb Z)\bullet x=0$, that `toPoint x` lies in `L.torsionSubset` and that $x$ lies in `Submodule.torsionBy ℤ _ (n : ℤ)` are all equivalent to the predicate `L.IsTorsionPoint _ n (toPoint x)`, i.e. to $L.\mathrm{nsmul}\,n$ of the point being the unit point; `torsionByEquiv` is the resulting bijection, and `natCard_torsionBy` the equality of the two cardinalities as `Nat.card`. Functoriality in the algebra is given by `mapPoint`, precomposition of a point with $\operatorname{Spec}$ of an $R$-algebra homomorphism $a\colon T\to T'$ (well defined by `specMap_comp_algebraMap`), and by the additive homomorphism `map a`, compatible with identities and with composition in the covariant sense $\mathrm{map}(b\circ a)=\mathrm{map}\,b\circ\mathrm{map}\,a$, and preserving $n$-torsion. Finally $T\simeq_{\mathrm{alg}[R]}T$ acts on `AlgPoints L hc T` by $\sigma\bullet x=\mathrm{map}\,\sigma\,x$, as a `DistribMulAction`, so by additive automorphisms, and $n$-torsion is preserved by the action.
--
--   **Relation to Mathlib.** Mathlib has no functor-of-points group-law structure attached to a morphism of schemes of this shape; `RelativeGroupLaw` and the point groups built from it are the project's own. Mathlib's `Additive`, `Submodule.torsionBy` and `DistribMulAction` are used to express the additive group, the $n$-torsion submodule and the automorphism action.
--
--   **Where it is used.** These point groups provide the Galois-module formulation of the points of a commutative group scheme over the base ring: with $R$ a $p$-adic ring and $T$ a large field extension, `AlgPoints` is the module on which $R$-algebra automorphisms act, and the torsion dictionary links its $n$-torsion with the torsion points and kernel schemes of the relative group law. They serve the treatment of good reduction of Jacobians and of $p$-power torsion used in the modularity route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

def AlgPoints (L : RelativeGroupLaw R f) (_hc : L.IsCommutative) (T : Type) [CommRing T]
    [Algebra R T] : Type :=
  Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f)

namespace AlgPoints

variable {L : RelativeGroupLaw R f} {hc : L.IsCommutative}
variable {T : Type} [CommRing T] [Algebra R T]

instance instAddCommGroup : AddCommGroup (L.AlgPoints hc T) :=
  @Additive.addCommGroup _ (L.pointCommGroup hc (Spec.map (CommRingCat.ofHom (algebraMap R T))))

instance instInhabited : Inhabited (L.AlgPoints hc T) := ⟨0⟩

def ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    L.AlgPoints hc T := Additive.ofMul x

def toPoint (x : L.AlgPoints hc T) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f := Additive.toMul x

@[simp] theorem toPoint_ofPoint (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    toPoint (ofPoint x : L.AlgPoints hc T) = x := rfl

@[simp] theorem ofPoint_toPoint (x : L.AlgPoints hc T) : ofPoint (toPoint x) = x := rfl

theorem toPoint_injective : Function.Injective (toPoint : L.AlgPoints hc T → _) :=
  fun _ _ h => h

theorem ofPoint_injective :
    Function.Injective (ofPoint : _ → L.AlgPoints hc T) :=
  fun _ _ h => h

@[ext] theorem ext {x y : L.AlgPoints hc T} (h : toPoint x = toPoint y) : x = y := h

def equivPoint : L.AlgPoints hc T ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f where
  toFun := toPoint
  invFun := ofPoint
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivPoint_apply (x : L.AlgPoints hc T) : equivPoint x = toPoint x := rfl

@[simp] theorem equivPoint_symm_apply
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (equivPoint.symm x : L.AlgPoints hc T) = ofPoint x := rfl

theorem toPoint_add (x y : L.AlgPoints hc T) :
    toPoint (x + y) = L.mul _ (toPoint x) (toPoint y) := rfl

theorem toPoint_zero : toPoint (0 : L.AlgPoints hc T) = L.one _ := rfl

theorem toPoint_neg (x : L.AlgPoints hc T) : toPoint (-x) = L.inv _ (toPoint x) := rfl

theorem ofPoint_mul (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.mul _ x y) : L.AlgPoints hc T) = ofPoint x + ofPoint y := rfl

theorem ofPoint_one : (ofPoint (L.one _) : L.AlgPoints hc T) = 0 := rfl

theorem ofPoint_inv (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.inv _ x) : L.AlgPoints hc T) = -ofPoint x := rfl

theorem toPoint_nsmul (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint (n • x) = L.nsmul _ n (toPoint x) := by
  induction n with
  | zero => rw [zero_nsmul, nsmul_zero]; rfl
  | succ n ih => rw [succ_nsmul, toPoint_add, ih, nsmul_succ]

theorem ofPoint_nsmul (n : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (ofPoint (L.nsmul _ n x) : L.AlgPoints hc T) = n • ofPoint x :=
  toPoint_injective (by rw [toPoint_nsmul]; rfl)

theorem toPoint_natCast_zsmul (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint ((n : ℤ) • x) = L.nsmul _ n (toPoint x) := by
  rw [natCast_zsmul, toPoint_nsmul]

theorem nsmul_eq_zero_iff (n : ℕ) (x : L.AlgPoints hc T) :
    n • x = 0 ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [isTorsionPoint_def, ← toPoint_nsmul, ← toPoint_zero]
  exact ⟨fun h => by rw [h], fun h => toPoint_injective h⟩

theorem natCast_zsmul_eq_zero_iff (n : ℕ) (x : L.AlgPoints hc T) :
    (n : ℤ) • x = 0 ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [natCast_zsmul, nsmul_eq_zero_iff]

theorem toPoint_mem_torsionSubset_iff (n : ℕ) (x : L.AlgPoints hc T) :
    toPoint x ∈ L.torsionSubset _ n ↔ n • x = 0 := by
  rw [mem_torsionSubset, nsmul_eq_zero_iff]

theorem mem_torsionBy_iff (n : ℕ) (x : L.AlgPoints hc T) :
    x ∈ Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ) ↔ L.IsTorsionPoint _ n (toPoint x) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul_eq_zero_iff]

def torsionByEquiv (n : ℕ) :
    Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ) ≃
      L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n where
  toFun x := ⟨toPoint (x : L.AlgPoints hc T), (mem_torsionBy_iff n _).1 x.2⟩
  invFun y := ⟨ofPoint y.1, (mem_torsionBy_iff n _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem torsionByEquiv_apply_coe (n : ℕ)
    (x : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
    ((torsionByEquiv n x : L.torsionSubset _ n) : SchemeHomOver _ f) =
      toPoint (x : L.AlgPoints hc T) := rfl

@[simp] theorem torsionByEquiv_symm_apply_coe (n : ℕ)
    (y : L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n) :
    (((torsionByEquiv n).symm y : Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) :
      L.AlgPoints hc T) = ofPoint y.1 := rfl

theorem natCard_torsionBy (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc T) (n : ℤ)) =
      Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n) :=
  Nat.card_congr (torsionByEquiv n)

section Map

variable {T' : Type} [CommRing T'] [Algebra R T'] {T'' : Type} [CommRing T''] [Algebra R T'']

theorem specMap_comp_algebraMap (a : T →ₐ[R] T') :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => a.commutes r

def mapPoint (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T'))) f :=
  GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom a.toRingHom))
    (specMap_comp_algebraMap a) x

@[simp] theorem mapPoint_coe (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    (mapPoint a x).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ x.1 := rfl

theorem mapPoint_mul (a : T →ₐ[R] T')
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    mapPoint a (L.mul _ x y) = L.mul _ (mapPoint a x) (mapPoint a y) :=
  L.mul_natural _ _ _ (specMap_comp_algebraMap a) _ _

theorem mapPoint_one (a : T →ₐ[R] T') :
    mapPoint (f := f) a (L.one _) = L.one _ :=
  L.one_natural _ _ _ (specMap_comp_algebraMap a)

def map (a : T →ₐ[R] T') : L.AlgPoints hc T →+ L.AlgPoints hc T' :=
  AddMonoidHom.mk' (fun x => ofPoint (mapPoint a (toPoint x))) fun x y => by
    apply toPoint_injective
    change mapPoint a (toPoint (x + y)) = L.mul _ (mapPoint a (toPoint x)) (mapPoint a (toPoint y))
    rw [toPoint_add]
    exact mapPoint_mul a _ _

theorem toPoint_map (a : T →ₐ[R] T') (x : L.AlgPoints hc T) :
    toPoint (map a x) = mapPoint a (toPoint x) := rfl

@[simp] theorem toPoint_map_coe (a : T →ₐ[R] T') (x : L.AlgPoints hc T) :
    (toPoint (map a x)).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (toPoint x).1 := rfl

theorem map_ofPoint (a : T →ₐ[R] T')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    map a (ofPoint x : L.AlgPoints hc T) = ofPoint (mapPoint a x) := rfl

theorem map_id : map (AlgHom.id R T) = AddMonoidHom.id (L.AlgPoints hc T) := by
  refine AddMonoidHom.ext fun x => toPoint_injective (Subtype.ext ?_)
  rw [toPoint_map_coe]
  change Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ (toPoint x).1 = (toPoint x).1
  rw [CommRingCat.ofHom_id]
  erw [Spec.map_id]
  exact Category.id_comp _

theorem map_comp (a : T →ₐ[R] T') (b : T' →ₐ[R] T'') :
    map (b.comp a) = (map b).comp (map a : L.AlgPoints hc T →+ L.AlgPoints hc T') := by
  refine AddMonoidHom.ext fun x => toPoint_injective (Subtype.ext ?_)
  rw [toPoint_map_coe, AddMonoidHom.comp_apply, toPoint_map_coe, toPoint_map_coe, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem isTorsionPoint_toPoint_map (a : T →ₐ[R] T') (n : ℕ) {x : L.AlgPoints hc T}
    (hx : L.IsTorsionPoint _ n (toPoint x)) : L.IsTorsionPoint _ n (toPoint (map a x)) := by
  rw [← nsmul_eq_zero_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end Map

instance instDistribMulAction : DistribMulAction (T ≃ₐ[R] T) (L.AlgPoints hc T) where
  smul σ x := map (σ : T →ₐ[R] T) x
  one_smul x := by
    change map ((1 : T ≃ₐ[R] T) : T →ₐ[R] T) x = x
    rw [show ((1 : T ≃ₐ[R] T) : T →ₐ[R] T) = AlgHom.id R T from rfl, map_id]
    rfl
  mul_smul σ τ x := by
    change map ((σ * τ : T ≃ₐ[R] T) : T →ₐ[R] T) x = map (σ : T →ₐ[R] T) (map (τ : T →ₐ[R] T) x)
    rw [show ((σ * τ : T ≃ₐ[R] T) : T →ₐ[R] T) = (σ : T →ₐ[R] T).comp (τ : T →ₐ[R] T) from rfl,
      map_comp]
    rfl
  smul_zero σ := map_zero _
  smul_add σ x y := map_add _ x y

theorem smul_def (σ : T ≃ₐ[R] T) (x : L.AlgPoints hc T) : σ • x = map (σ : T →ₐ[R] T) x := rfl

@[simp] theorem toPoint_smul_coe (σ : T ≃ₐ[R] T) (x : L.AlgPoints hc T) :
    (toPoint (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : T →ₐ[R] T).toRingHom) ≫ (toPoint x).1 :=
  rfl

theorem smul_ofPoint (σ : T ≃ₐ[R] T)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f) :
    σ • (ofPoint x : L.AlgPoints hc T) = ofPoint (mapPoint (σ : T →ₐ[R] T) x) := rfl

theorem nsmul_smul_eq_zero (σ : T ≃ₐ[R] T) (n : ℕ) {x : L.AlgPoints hc T} (hx : n • x = 0) :
    n • (σ • x) = 0 := by
  rw [smul_def, ← map_nsmul, hx, map_zero]

end AlgPoints

end RelativeGroupLaw
end GoodReductionJacobian

end


