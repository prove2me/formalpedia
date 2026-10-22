-- Prove2me | Definitions.Def_LieTwoAlg_Equiv_Model
-- name    : LieTwoAlg_Equiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:35.352684+00:00
-- url     : https://prove2.me/theorems/69c9eccf-b665-48fd-ba13-c678871b2a97
-- title:
--   Semistrict Lie 2-algebras and 2-term L∞-algebras
-- statement:
--   A semistrict Lie $2$-algebra is a $2$-vector space with a skew bilinear bracket functor and a trilinear Jacobiator whose source is $[[x,y],z]$ and target is $[x,[y,z]]+[[x,z],y]$. The Jacobiator is natural, completely antisymmetric in arrow parts, and satisfies the full octagon of Definition 22. A homomorphism carries a linear functor and a skew bilinear bracket comparison $F_2$, satisfying its source, target, naturality, and commutative square conditions.
--
--   A $2$-term $L_\infty$-algebra has $V_1\xrightarrow{d}V_0$, brackets $l_2$, and $l_3:V_0^3\to V_1$ obeying Lemma 33(a)–(i). Its homomorphisms carry maps $(\varphi_0,\varphi_1,\varphi_2)$ obeying all three equations of Definition 34. The two homomorphism compositions and identities are the paper's formulas.
--
--   The file defines both raw categories and the concrete constructions $T(V),T(\varphi),S(L),S(F)$ used in Theorem 36. These definitions fix the common interface for the goal and its milestones.
--
--   **Formalization Note** $[h,x]=-[x,h]$ and $[h,k]=0$ encode Lemma 33(b),(c). The §4.3 standing characteristic assumption appears on theorems, while the raw data remain definable over any field.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 18–21, 28–36, Definitions 20–23; Lemma 33; Definition 34; Theorem 36 proof

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_RawCat
import Definitions.Def_LieTwoAlg_Equiv_TwoVect

set_option autoImplicit false

namespace LieTwoAlg.Equiv

universe u

variable {k : Type u} [Field k]

/-- Lemma 33: raw 2-term L-infinity operations. -/
structure LInfData (k : Type u) [Field k] where
  V0 : Type u
  V1 : Type u
  [add0 : AddCommGroup V0]
  [mod0 : Module k V0]
  [add1 : AddCommGroup V1]
  [mod1 : Module k V1]
  d : V1 →ₗ[k] V0
  l2 : V0 →ₗ[k] V0 →ₗ[k] V0
  l2m : V0 →ₗ[k] V1 →ₗ[k] V1
  l3 : V0 →ₗ[k] V0 →ₗ[k] V0 →ₗ[k] V1
attribute [instance] LInfData.add0 LInfData.mod0 LInfData.add1 LInfData.mod1

/-- Lemma 33 (a)-(i); `[h,x] = -[x,h]`, `[h,k] = 0`. -/
structure IsLInf (V : LInfData k) : Prop where
  skew2 : ∀ x y, V.l2 x y = -V.l2 y x
  skew3a : ∀ x y z, V.l3 x y z = -V.l3 y x z
  skew3b : ∀ x y z, V.l3 x y z = -V.l3 x z y
  e : ∀ x h, V.d (V.l2m x h) = V.l2 x (V.d h)
  f : ∀ h h', V.l2m (V.d h) h' = -V.l2m (V.d h') h
  g : ∀ x y z, V.d (V.l3 x y z) =
    -V.l2 (V.l2 x y) z + V.l2 (V.l2 x z) y + V.l2 x (V.l2 y z)
  h : ∀ h x y, V.l3 (V.d h) x y =
    -V.l2m (V.l2 x y) h - V.l2m y (V.l2m x h) + V.l2m x (V.l2m y h)
  i : ∀ w x y z,
    -V.l2m z (V.l3 w x y) - V.l2m x (V.l3 w y z) +
      V.l3 (V.l2 w y) x z + V.l3 (V.l2 x z) w y =
    -V.l2m y (V.l3 w x z) - V.l2m w (V.l3 x y z) +
      V.l3 (V.l2 w x) y z + V.l3 (V.l2 w z) x y +
      V.l3 (V.l2 x y) w z + V.l3 (V.l2 y z) w x

/-- Definition 34: raw L-infinity homomorphism data. -/
structure LInfHom (V W : LInfData k) where
  φ0 : V.V0 →ₗ[k] W.V0
  φ1 : V.V1 →ₗ[k] W.V1
  φ2 : V.V0 →ₗ[k] V.V0 →ₗ[k] W.V1

/-- Definition 34, including all three equations. -/
structure IsLInfHom {V W : LInfData k} (φ : LInfHom V W) : Prop where
  chain : ∀ h, W.d (φ.φ1 h) = φ.φ0 (V.d h)
  skew : ∀ x y, φ.φ2 x y = -φ.φ2 y x
  one : ∀ x y, W.d (φ.φ2 x y) = φ.φ0 (V.l2 x y) - W.l2 (φ.φ0 x) (φ.φ0 y)
  two : ∀ x h, φ.φ2 x (V.d h) = φ.φ1 (V.l2m x h) - W.l2m (φ.φ0 x) (φ.φ1 h)
  three : ∀ x y z,
    -W.l2m (φ.φ0 z) (φ.φ2 x y) + φ.φ2 (V.l2 x y) z + φ.φ1 (V.l3 x y z) =
      W.l3 (φ.φ0 x) (φ.φ0 y) (φ.φ0 z) + W.l2m (φ.φ0 x) (φ.φ2 y z) -
      W.l2m (φ.φ0 y) (φ.φ2 x z) + φ.φ2 x (V.l2 y z) + φ.φ2 (V.l2 x z) y

/-- Equation following Definition 34, in diagrammatic order. -/
def LInfHom.comp {V W X : LInfData k} (φ : LInfHom V W) (ψ : LInfHom W X) :
    LInfHom V X where
  φ0 := ψ.φ0.comp φ.φ0
  φ1 := ψ.φ1.comp φ.φ1
  φ2 := preBilin ψ.φ2 φ.φ0 φ.φ0 + postBilin ψ.φ1 φ.φ2

def LInfHom.id (V : LInfData k) : LInfHom V V :=
  ⟨LinearMap.id, LinearMap.id, 0⟩

/-- Definition 22: raw semistrict Lie 2-algebra data. -/
structure Lie2Data (k : Type u) [Field k] where
  vec : TwoVect k
  br0 : vec.V0 →ₗ[k] vec.V0 →ₗ[k] vec.V0
  br1 : vec.V1 →ₗ[k] vec.V1 →ₗ[k] vec.V1
  J : vec.V0 →ₗ[k] vec.V0 →ₗ[k] vec.V0 →ₗ[k] vec.V1

/-- Definition 22, with the Jacobiator octagon stated in morphism composition. -/
structure IsLie2 (L : Lie2Data k) : Prop where
  br_s : ∀ f g, L.vec.s (L.br1 f g) = L.br0 (L.vec.s f) (L.vec.s g)
  br_t : ∀ f g, L.vec.t (L.br1 f g) = L.br0 (L.vec.t f) (L.vec.t g)
  br_i : ∀ x y, L.br1 (L.vec.i x) (L.vec.i y) = L.vec.i (L.br0 x y)
  br_comp : ∀ f f' g g', L.vec.t f = L.vec.s f' → L.vec.t g = L.vec.s g' →
    L.br1 (L.vec.comp f f') (L.vec.comp g g') =
      L.vec.comp (L.br1 f g) (L.br1 f' g')
  skew0 : ∀ x y, L.br0 x y = -L.br0 y x
  skew1 : ∀ f g, L.br1 f g = -L.br1 g f
  J_s : ∀ x y z, L.vec.s (L.J x y z) = L.br0 (L.br0 x y) z
  J_t : ∀ x y z, L.vec.t (L.J x y z) =
    L.br0 x (L.br0 y z) + L.br0 (L.br0 x z) y
  J_nat : ∀ f g h,
    L.vec.comp (L.br1 (L.br1 f g) h) (L.J (L.vec.t f) (L.vec.t g) (L.vec.t h)) =
      L.vec.comp (L.J (L.vec.s f) (L.vec.s g) (L.vec.s h))
        (L.br1 f (L.br1 g h) + L.br1 (L.br1 f h) g)
  J_skew_a : ∀ x y z, L.vec.arrow (L.J x y z) = -L.vec.arrow (L.J y x z)
  J_skew_b : ∀ x y z, L.vec.arrow (L.J x y z) = -L.vec.arrow (L.J x z y)
  J_oct : ∀ w x y z,
    L.vec.comp
      (L.vec.comp (L.J (L.br0 w x) y z)
        (L.br1 (L.J w x z) (L.vec.i y) +
          L.vec.i (L.br0 (L.br0 w x) (L.br0 y z))))
      (L.J w (L.br0 x z) y + L.J (L.br0 w z) x y + L.J w x (L.br0 y z)) =
    L.vec.comp
      (L.vec.comp
        (L.vec.comp (L.br1 (L.J w x y) (L.vec.i z))
          (L.J (L.br0 w y) x z + L.J w (L.br0 x y) z))
        (L.br1 (L.J w y z) (L.vec.i x) +
          L.vec.i (L.br0 (L.br0 w y) (L.br0 x z) +
            L.br0 w (L.br0 (L.br0 x y) z) + L.br0 (L.br0 w z) (L.br0 x y))))
      (L.br1 (L.vec.i w) (L.J x y z) +
        L.vec.i (L.br0 (L.br0 (L.br0 w z) y) x +
          L.br0 (L.br0 w (L.br0 y z)) x + L.br0 (L.br0 w y) (L.br0 x z) +
          L.br0 (L.br0 w z) (L.br0 x y)))

/-- Definition 23: raw homomorphism data. -/
structure Lie2Hom (L M : Lie2Data k) where
  F0 : L.vec.V0 →ₗ[k] M.vec.V0
  F1 : L.vec.V1 →ₗ[k] M.vec.V1
  F2 : L.vec.V0 →ₗ[k] L.vec.V0 →ₗ[k] M.vec.V1

/-- Definition 23, including the commutative square. -/
structure IsLie2Hom {L M : Lie2Data k} (F : Lie2Hom L M) : Prop where
  functor : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩
  skew : ∀ x y, F.F2 x y = -F.F2 y x
  F2_s : ∀ x y, M.vec.s (F.F2 x y) = M.br0 (F.F0 x) (F.F0 y)
  F2_t : ∀ x y, M.vec.t (F.F2 x y) = F.F0 (L.br0 x y)
  F2_nat : ∀ f g,
    M.vec.comp (M.br1 (F.F1 f) (F.F1 g)) (F.F2 (L.vec.t f) (L.vec.t g)) =
      M.vec.comp (F.F2 (L.vec.s f) (L.vec.s g)) (F.F1 (L.br1 f g))
  square : ∀ x y z,
    M.vec.comp
      (M.vec.comp (M.J (F.F0 x) (F.F0 y) (F.F0 z))
        (M.br1 (M.vec.i (F.F0 x)) (F.F2 y z) +
          M.br1 (F.F2 x z) (M.vec.i (F.F0 y))))
      (F.F2 x (L.br0 y z) + F.F2 (L.br0 x z) y) =
    M.vec.comp
      (M.vec.comp (M.br1 (F.F2 x y) (M.vec.i (F.F0 z)))
        (F.F2 (L.br0 x y) z))
      (F.F1 (L.J x y z))

/-- Page 21: `G₂` followed by `G₁(F₂)` in the target 2-vector space. -/
def Lie2Hom.comp {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N) :
    Lie2Hom L N where
  F0 := G.F0.comp F.F0
  F1 := G.F1.comp F.F1
  F2 := preBilin G.F2 F.F0 F.F0 + postBilin G.F1 F.F2 -
    postBilin (N.vec.i.comp N.vec.t) (preBilin G.F2 F.F0 F.F0)

/-- Page 21: the identity natural transformation on the bracket. -/
def Lie2Hom.id (L : Lie2Data k) : Lie2Hom L L :=
  ⟨LinearMap.id, LinearMap.id, postBilin L.vec.i L.br0⟩

/-- The categories use lawful objects and raw homomorphism data. -/
def twoVectCat (k : Type u) [Field k] : RawCat.{u} where
  Ob := TwoVect k
  Hom V W := LinFunctor V W
  IsHom F := IsLinFunctor F
  id V := LinFunctor.id V
  comp F G := F.comp G

def twoTermCat (k : Type u) [Field k] : RawCat.{u} where
  Ob := TwoTerm k
  Hom C D := ChainMap C D
  IsHom φ := IsChainMap φ
  id C := ChainMap.id C
  comp φ ψ := φ.comp ψ

def lie2AlgCat (k : Type u) [Field k] : RawCat.{u} where
  Ob := {L : Lie2Data k // IsLie2 L}
  Hom X Y := Lie2Hom X.1 Y.1
  IsHom F := IsLie2Hom F
  id X := Lie2Hom.id X.1
  comp F G := F.comp G

def twoTermLInfCat (k : Type u) [Field k] : RawCat.{u} where
  Ob := {V : LInfData k // IsLInf V}
  Hom X Y := LInfHom X.1 Y.1
  IsHom φ := IsLInfHom φ
  id X := LInfHom.id X.1
  comp φ ψ := φ.comp ψ


/-- Proposition 8: send a 2-vector space to its two-term complex `ker s → V₀`. -/
def toTwoTerm (V : TwoVect k) : TwoTerm k where
  C0 := V.V0
  C1 := LinearMap.ker V.s
  d := V.t.comp (Submodule.subtype (LinearMap.ker V.s))

/-- Proposition 8: send a two-term complex to objects `C₀`, arrows `C₀ × C₁`. -/
def ofTwoTerm (C : TwoTerm k) : TwoVect k where
  V0 := C.C0
  V1 := C.C0 × C.C1
  s := {
    toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  t := {
    toFun := fun p => p.1 + C.d p.2
    map_add' := by intros; simp [map_add]; abel
    map_smul' := by intros; simp [map_smul, smul_add] }
  i := {
    toFun := fun x => (x, 0)
    map_add' := by intros; ext <;> simp
    map_smul' := by intros; ext <;> simp }
  s_i := by intro x; rfl
  t_i := by intro x; simp

/-- The map on 1-cells of the functor from 2Vect to 2Term. -/
def toTwoTermMap {V W : TwoVect k} (F : LinFunctor V W) :
    ChainMap (toTwoTerm V) (toTwoTerm W) where
  φ0 := F.F0
  φ1 := (W.arrowK.comp F.F1).comp (Submodule.subtype (LinearMap.ker V.s))


/-- The map on 1-cells of the functor from 2Term to 2Vect. -/
def ofTwoTermMap {C D : TwoTerm k} (φ : ChainMap C D) :
    LinFunctor (ofTwoTerm C) (ofTwoTerm D) where
  F0 := φ.φ0
  F1 := LinearMap.prodMap φ.φ0 φ.φ1

/-- The bilinear morphism bracket of the construction `T(V)`. -/
def lInfBracket (V : LInfData k) :
    (V.V0 × V.V1) →ₗ[k] (V.V0 × V.V1) →ₗ[k] (V.V0 × V.V1) where
  toFun p := {
    toFun := fun q =>
      (V.l2 p.1 q.1, -V.l2m q.1 p.2 + V.l2m (p.1 + V.d p.2) q.2)
    map_add' := by
      rintro ⟨a, g⟩ ⟨b, h⟩
      apply Prod.ext <;> simp [Prod.add_def, map_add] <;> abel
    map_smul' := by
      rintro c ⟨a, g⟩
      apply Prod.ext <;> simp [Prod.smul_def, map_smul, smul_add] }
  map_add' := by
    rintro ⟨x, f⟩ ⟨y, g⟩
    apply LinearMap.ext
    rintro ⟨a, h⟩
    apply Prod.ext <;> simp [Prod.add_def, map_add] <;> abel
  map_smul' := by
    rintro c ⟨x, f⟩
    apply LinearMap.ext
    rintro ⟨a, h⟩
    apply Prod.ext <;> simp [Prod.smul_def, map_smul, smul_add]

/-- The trilinear Jacobiator of `T(V)`. -/
def lInfJacobiator (V : LInfData k) :
    V.V0 →ₗ[k] V.V0 →ₗ[k] V.V0 →ₗ[k] (V.V0 × V.V1) where
  toFun x := {
    toFun := fun y => {
      toFun := fun z => (V.l2 (V.l2 x y) z, V.l3 x y z)
      map_add' := by intros; apply Prod.ext <;> simp [Prod.add_def]
      map_smul' := by intros; apply Prod.ext <;> simp [Prod.smul_def] }
    map_add' := by intros; ext z <;> simp [Prod.add_def]
    map_smul' := by intros; ext z <;> simp [Prod.smul_def] }
  map_add' := by intros; ext y z <;> simp [Prod.add_def]
  map_smul' := by intros; ext y z <;> simp [Prod.smul_def]

/-- The paper's construction `T(V)` on objects, pp. 30–33. -/
def ofLInf (V : LInfData k) : Lie2Data k where
  vec := ofTwoTerm ⟨V.V0, V.V1, V.d⟩
  br0 := V.l2
  br1 := lInfBracket V
  J := lInfJacobiator V

/-- The bracket comparison transformation of `T(φ)`. -/
def lInfHomF2 {V W : LInfData k} (φ : LInfHom V W) :
    V.V0 →ₗ[k] V.V0 →ₗ[k] (W.V0 × W.V1) where
  toFun x := {
    toFun := fun y => (W.l2 (φ.φ0 x) (φ.φ0 y), φ.φ2 x y)
    map_add' := by intros; apply Prod.ext <;> simp [Prod.add_def]
    map_smul' := by intros; apply Prod.ext <;> simp [Prod.smul_def] }
  map_add' := by intros; ext y <;> simp [Prod.add_def]
  map_smul' := by intros; ext y <;> simp [Prod.smul_def]

/-- The paper's construction `T(φ)` on 1-cells, p. 34. -/
def ofLInfHom {V W : LInfData k} (φ : LInfHom V W) :
    Lie2Hom (ofLInf V) (ofLInf W) where
  F0 := φ.φ0
  F1 := LinearMap.prodMap φ.φ0 φ.φ1
  F2 := lInfHomF2 φ

/-- The paper's construction `S(L)` on objects, pp. 34–36. -/
def toLInf (L : Lie2Data k) : LInfData k where
  V0 := L.vec.V0
  V1 := LinearMap.ker L.vec.s
  d := L.vec.t.comp (Submodule.subtype (LinearMap.ker L.vec.s))
  l2 := L.br0
  l2m := {
    toFun := fun x => L.vec.arrowK.comp
      ((L.br1 (L.vec.i x)).comp (Submodule.subtype (LinearMap.ker L.vec.s)))
    map_add' := by intros; ext h; simp [TwoVect.arrowK, TwoVect.arrow, map_add]; abel
    map_smul' := by intros; ext h; simp [TwoVect.arrowK, TwoVect.arrow, map_smul]; module }
  l3 := {
    toFun := fun x => {
      toFun := fun y => L.vec.arrowK.comp (L.J x y)
      map_add' := by intros; ext z; simp
      map_smul' := by intros; ext z; simp }
    map_add' := by intros; ext y z; simp
    map_smul' := by intros; ext y z; simp }

/-- The paper's construction `S(F)` on 1-cells, p. 36. -/
def toLInfHom {L M : Lie2Data k} (F : Lie2Hom L M) :
    LInfHom (toLInf L) (toLInf M) where
  φ0 := F.F0
  φ1 := (M.vec.arrowK.comp F.F1).comp (Submodule.subtype (LinearMap.ker L.vec.s))
  φ2 := postBilin M.vec.arrowK F.F2

end LieTwoAlg.Equiv


