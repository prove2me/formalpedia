-- Prove2me | Definitions.Def_Dieudonne_WittGroupHopf
-- name    : Dieudonne_WittGroupHopf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/59cda4bd-8b3e-5299-9e0a-7310dadea6c4
-- title:
--   Coordinate Hopf algebra of the truncated Witt group
-- statement:
--   Fix a commutative ring $R$, a prime $p$, an integer $n$ and an index type $J$. `WittGroup.Coord R p n J` is a type synonym for the polynomial ring $R[X_{j,i} : j \in J,\ i \in \mathrm{Fin}\,n]$, i.e. `MvPolynomial (J × Fin n) R`, carrying its commutative-ring and $R$-algebra structures; `X j i` is the variable indexed by $(j,i)$, `lift` is the $R$-algebra map determined by prescribing the images $f\,j\,i$ of the variables, and `algHom_ext` is the corresponding extensionality principle. Writing $\mathcal O$ for this ring, `univ R p n j` is the truncated Witt vector $u_j = (X_{j,0},\dots,X_{j,n-1}) \in W_n(\mathcal O)$, and `univLeft`, `univRight` are its two images $(X_{j,i} \otimes 1)_i$ and $(1 \otimes X_{j,i})_i$ in $W_n(\mathcal O \otimes_R \mathcal O)$. The structure maps are the $R$-algebra maps determined on variables by: `comul` sends $X_{j,i}$ to the $i$-th coordinate of $\text{univLeft}_j + \text{univRight}_j$ computed in the ring $W_n(\mathcal O \otimes_R \mathcal O)$ (the $i$-th Witt addition polynomial); `counit` sends every variable to $0$; `antipode` sends $X_{j,i}$ to the $i$-th coordinate of $-u_j$ in $W_n(\mathcal O)$. Coassociativity, the two counit identities and the two antipode identities are proved, giving `Bialgebra`, `HopfAlgebra` and `Coalgebra.IsCocomm` instances on `Coord R p n J`; helper lemmas transport `comul` and `antipode` through an arbitrary ring homomorphism out of $\mathcal O \otimes_R \mathcal O$ or $\mathcal O$ coordinatewise. `pointsEquiv` is the bijection between $R$-algebra maps $\mathcal O \to A$ and families $J \to W_n(A)$, sending $\varphi$ to $(\varphi(X_{j,i}))_i$; it carries the convolution product of algebra maps to addition of Witt-vector families, the convolution unit to $0$, and precomposition with the antipode to negation. Finally `univ_mem_wittHom` shows each $u_j$ lies in the additive subgroup `wittHom R p n (Coord R p n J)`, and `univHom j` is $u_j$ viewed as an element of that subgroup; `X_ne_zero` records nonvanishing of the variables over a nontrivial $R$.
--
--   **Relation to Mathlib.** The underlying ring is Mathlib's `MvPolynomial (J × Fin n) R` under a new name, and the Hopf-algebra structure is assembled with Mathlib's `Bialgebra.ofAlgHom` and `HopfAlgebra.ofAlgHom`, the convolution monoid `WithConv` on algebra maps, and Mathlib's `TruncatedWittVector`; Mathlib itself provides no Hopf-algebra structure representing the truncated Witt group.
--
--   **Where it is used.** This is the affine algebra of the group scheme $W_n^J$ over $R$, used as the representing object on the Dieudonné-theory side of the deformation-theoretic input: the group `wittHom R p n A` of Witt vectors over a bialgebra $A$ satisfying the additivity condition, with its Frobenius and Verschiebung, is the Dieudonné datum attached to $A$, and `univHom` supplies its universal elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_WittGroupHopf.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation

set_option linter.unusedVariables false in

def WittGroup.Coord (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v) : Type (max u v) :=
  MvPolynomial (J × Fin n) R

namespace WittGroup

variable (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v)

noncomputable instance instCommRing : CommRing (Coord R p n J) :=
  inferInstanceAs (CommRing (MvPolynomial (J × Fin n) R))

noncomputable instance instAlgebra : Algebra R (Coord R p n J) :=
  inferInstanceAs (Algebra R (MvPolynomial (J × Fin n) R))

noncomputable instance instInhabited : Inhabited (Coord R p n J) := ⟨0⟩

variable {R p n J}

noncomputable def X (j : J) (i : Fin n) : Coord R p n J := (MvPolynomial.X (j, i) : MvPolynomial (J × Fin n) R)

noncomputable def lift {A : Type w} [CommSemiring A] [Algebra R A] (f : J → Fin n → A) :
    Coord R p n J →ₐ[R] A :=
  (MvPolynomial.aeval fun ji : J × Fin n => f ji.1 ji.2 : MvPolynomial (J × Fin n) R →ₐ[R] A)

@[simp] theorem lift_X {A : Type w} [CommSemiring A] [Algebra R A] (f : J → Fin n → A) (j : J)
    (i : Fin n) : lift f (X j i : Coord R p n J) = f j i :=
  MvPolynomial.aeval_X _ (j, i)

theorem algHom_ext {A : Type w} [Semiring A] [Algebra R A] {f g : Coord R p n J →ₐ[R] A}
    (h : ∀ j i, f (X j i) = g (X j i)) : f = g :=
  MvPolynomial.algHom_ext (fun ji : J × Fin n => h ji.1 ji.2)

variable (R p n) in

noncomputable def univ (j : J) : TruncatedWittVector p n (Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i

@[simp] theorem coeff_univ (j : J) (i : Fin n) : (univ R p n j).coeff i = X j i :=
  TruncatedWittVector.coeff_mk _ _

variable [hp : Fact p.Prime]

section MapMk

variable {S : Type*} {T : Type*} [CommRing S] [CommRing T]

theorem map_mk (g : S →+* T) (f : Fin n → S) :
    TruncWitt.map (p := p) g (TruncatedWittVector.mk p f) = TruncatedWittVector.mk p fun i => g (f i) :=
  TruncatedWittVector.ext fun i => by
    rw [TruncWitt.coeff_map, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_mk]

theorem mk_zero_eq : (TruncatedWittVector.mk p fun _ : Fin n => (0 : S)) = 0 :=
  TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_zero]

end MapMk

section Rehom

variable {S : Type*} {B : Type*} [NonAssocSemiring S] [NonAssocSemiring B]

omit hp in

def rehom (g : S → B) (h1 : g 1 = 1) (hm : ∀ x y, g (x * y) = g x * g y) (h0 : g 0 = 0)
    (ha : ∀ x y, g (x + y) = g x + g y) : S →+* B :=
  ⟨⟨⟨g, h1⟩, hm⟩, h0, ha⟩

omit hp in
@[simp] theorem rehom_apply (g : S → B) (h1 : g 1 = 1) (hm : ∀ x y, g (x * y) = g x * g y)
    (h0 : g 0 = 0) (ha : ∀ x y, g (x + y) = g x + g y) (x : S) : rehom g h1 hm h0 ha x = g x := rfl

end Rehom

theorem map_univ {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) :
    TruncWitt.map (p := p) g (univ R p n j) = TruncatedWittVector.mk p fun i => g (X j i) :=
  map_mk g _

variable (R p n J)

noncomputable def univLeft (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i ⊗ₜ[R] (1 : Coord R p n J)

noncomputable def univRight (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => (1 : Coord R p n J) ⊗ₜ[R] X j i

noncomputable def comul : Coord R p n J →ₐ[R] Coord R p n J ⊗[R] Coord R p n J :=
  lift fun j i => (univLeft R p n J j + univRight R p n J j).coeff i

noncomputable def counit : Coord R p n J →ₐ[R] R :=
  lift fun _ _ => 0

noncomputable def antipode : Coord R p n J →ₐ[R] Coord R p n J :=
  lift fun j i => (-univ R p n j).coeff i

variable {R p n J}

@[simp] theorem comul_X (j : J) (i : Fin n) :
    comul R p n J (X j i) = (univLeft R p n J j + univRight R p n J j).coeff i :=
  lift_X _ j i

omit hp in
@[simp] theorem counit_X (j : J) (i : Fin n) : counit R p n J (X j i) = 0 :=
  lift_X _ j i

@[simp] theorem antipode_X (j : J) (i : Fin n) :
    antipode R p n J (X j i) = (-univ R p n j).coeff i :=
  lift_X _ j i

theorem ringHom_comul_X {B : Type w} [CommRing B] (g : Coord R p n J ⊗[R] Coord R p n J →+* B)
    (j : J) (i : Fin n) :
    g (comul R p n J (X j i)) =
      ((TruncatedWittVector.mk p fun i => g (X j i ⊗ₜ[R] (1 : Coord R p n J))) +
        (TruncatedWittVector.mk p fun i => g ((1 : Coord R p n J) ⊗ₜ[R] X j i))).coeff i := by
  rw [comul_X, ← TruncWitt.coeff_map (p := p) g, map_add, univLeft, univRight, map_mk, map_mk]

theorem mk_ringHom_comul {B : Type w} [CommRing B] (g : Coord R p n J ⊗[R] Coord R p n J →+* B)
    (j : J) :
    (TruncatedWittVector.mk p fun i => g (comul R p n J (X j i))) =
      (TruncatedWittVector.mk p fun i => g (X j i ⊗ₜ[R] (1 : Coord R p n J))) +
        (TruncatedWittVector.mk p fun i => g ((1 : Coord R p n J) ⊗ₜ[R] X j i)) :=
  TruncatedWittVector.ext fun i => by rw [TruncatedWittVector.coeff_mk, ringHom_comul_X]

theorem ringHom_antipode_X {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) (i : Fin n) :
    g (antipode R p n J (X j i)) = (-(TruncatedWittVector.mk p fun i => g (X j i))).coeff i := by
  rw [antipode_X, ← TruncWitt.coeff_map (p := p) g, map_neg, map_univ]

theorem mk_ringHom_antipode {B : Type w} [CommRing B] (g : Coord R p n J →+* B) (j : J) :
    (TruncatedWittVector.mk p fun i => g (antipode R p n J (X j i))) =
      -(TruncatedWittVector.mk p fun i => g (X j i)) :=
  TruncatedWittVector.ext fun i => by rw [TruncatedWittVector.coeff_mk, ringHom_antipode_X]

section Axioms

variable (R p n J)

local notation "𝒪" => Coord R p n J
local notation "T" => Coord R p n J ⊗[R] (Coord R p n J ⊗[R] Coord R p n J)

theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J)) =
      (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)).comp (comul R p n J) := by
  refine algHom_ext fun j i => ?_

  set a : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => X j i ⊗ₜ[R] ((1 : 𝒪) ⊗ₜ[R] (1 : 𝒪)) with ha
  set b : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => (1 : 𝒪) ⊗ₜ[R] (X j i ⊗ₜ[R] (1 : 𝒪)) with hb
  set c : TruncatedWittVector p n T :=
    TruncatedWittVector.mk p fun i => (1 : 𝒪) ⊗ₜ[R] ((1 : 𝒪) ⊗ₜ[R] X j i) with hc

  let FL : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪))
  let FR : 𝒪 ⊗[R] 𝒪 →ₐ[R] T := Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)
  let KL : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : 𝒪 ⊗[R] 𝒪 →ₐ[R] (𝒪 ⊗[R] 𝒪) ⊗[R] 𝒪)
  let KR : 𝒪 ⊗[R] 𝒪 →ₐ[R] T :=
    (Algebra.TensorProduct.includeRight : 𝒪 ⊗[R] 𝒪 →ₐ[R] 𝒪 ⊗[R] (𝒪 ⊗[R] 𝒪))

  have eL := ringHom_comul_X (p := p) (rehom FL FL.map_one FL.map_mul FL.map_zero FL.map_add) j i
  have eR := ringHom_comul_X (p := p) (rehom FR FR.map_one FR.map_mul FR.map_zero FR.map_add) j i
  have fL := mk_ringHom_comul (p := p) (rehom KL KL.map_one KL.map_mul KL.map_zero KL.map_add) j
  have fR := mk_ringHom_comul (p := p) (rehom KR KR.map_one KR.map_mul KR.map_zero KR.map_add) j
  simp only [rehom_apply] at eL eR fL fR
  have hassoc : ∀ x y z : 𝒪, (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      x ⊗ₜ[R] (y ⊗ₜ[R] z) := fun x y z => Algebra.TensorProduct.assoc_tmul R R 𝒪 x y z

  have hFL1 : (TruncatedWittVector.mk p fun i => FL (X j i ⊗ₜ[R] (1 : 𝒪))) = a + b := by
    have hg : (TruncatedWittVector.mk p fun i => FL (X j i ⊗ₜ[R] (1 : 𝒪))) =
        TruncatedWittVector.mk p fun i => KL (comul R p n J (X j i)) := by
      refine congrArg _ (funext fun i => ?_)
      change (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪)
        (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪) (X j i ⊗ₜ[R] (1 : 𝒪))) =
        (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪) (comul R p n J (X j i) ⊗ₜ[R] (1 : 𝒪))
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [hg, fL, ha, hb]
    congr 1
  have hFL2 : (TruncatedWittVector.mk p fun i => FL ((1 : 𝒪) ⊗ₜ[R] X j i)) = c := by
    rw [hc]
    refine congrArg _ (funext fun i => ?_)
    change (Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪)
      (Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪) ((1 : 𝒪) ⊗ₜ[R] X j i)) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def]
    exact hassoc _ _ _
  have hFR1 : (TruncatedWittVector.mk p fun i => FR (X j i ⊗ₜ[R] (1 : 𝒪))) = a := by
    rw [ha]
    refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J) (X j i ⊗ₜ[R] (1 : 𝒪)) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.one_def]
  have hFR2 : (TruncatedWittVector.mk p fun i => FR ((1 : 𝒪) ⊗ₜ[R] X j i)) = b + c := by
    have hg : (TruncatedWittVector.mk p fun i => FR ((1 : 𝒪) ⊗ₜ[R] X j i)) =
        TruncatedWittVector.mk p fun i => KR (comul R p n J (X j i)) := by
      refine congrArg _ (funext fun i => ?_)
      change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J) ((1 : 𝒪) ⊗ₜ[R] X j i) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hg, fR, hb, hc]
    rfl
  have hL : ((Algebra.TensorProduct.assoc R R R 𝒪 𝒪 𝒪).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J))) (X j i) =
      FL (comul R p n J (X j i)) := rfl
  have hR : ((Algebra.TensorProduct.map (AlgHom.id R 𝒪) (comul R p n J)).comp (comul R p n J)) (X j i) =
      FR (comul R p n J (X j i)) := rfl
  rw [hL, hR, eL, eR, hFL1, hFL2, hFR1, hFR2]
  exact congrArg (TruncatedWittVector.coeff i) (add_assoc a b c)

theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪)).comp (comul R p n J) =
      (Algebra.TensorProduct.lid R 𝒪).symm := by
  refine algHom_ext fun j i => ?_
  let g : 𝒪 ⊗[R] 𝒪 →+* R ⊗[R] 𝒪 := (Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : 𝒪)) = 0 := by
    intro i
    change Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪) (X j i ⊗ₜ[R] (1 : 𝒪)) = 0
    rw [Algebra.TensorProduct.map_tmul, counit_X, TensorProduct.zero_tmul]
  have hg2 : ∀ i, g ((1 : 𝒪) ⊗ₜ[R] X j i) = (1 : R) ⊗ₜ[R] X j i := by
    intro i
    change Algebra.TensorProduct.map (counit R p n J) (AlgHom.id R 𝒪) ((1 : 𝒪) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = (Algebra.TensorProduct.lid R 𝒪).symm (X j i)
  rw [h, mk_zero_eq, zero_add, TruncatedWittVector.coeff_mk]
  rfl

theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J)).comp (comul R p n J) =
      (Algebra.TensorProduct.rid R R 𝒪).symm := by
  refine algHom_ext fun j i => ?_
  let g : 𝒪 ⊗[R] 𝒪 →+* 𝒪 ⊗[R] R := (Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : 𝒪)) = X j i ⊗ₜ[R] (1 : R) := by
    intro i
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J) (X j i ⊗ₜ[R] (1 : 𝒪)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hg2 : ∀ i, g ((1 : 𝒪) ⊗ₜ[R] X j i) = 0 := by
    intro i
    change Algebra.TensorProduct.map (AlgHom.id R 𝒪) (counit R p n J) ((1 : 𝒪) ⊗ₜ[R] X j i) = 0
    rw [Algebra.TensorProduct.map_tmul, counit_X, TensorProduct.tmul_zero]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = (Algebra.TensorProduct.rid R R 𝒪).symm (X j i)
  rw [h, mk_zero_eq, add_zero, TruncatedWittVector.coeff_mk]
  rfl

end Axioms

variable (R p n J)

noncomputable instance instBialgebra : Bialgebra R (Coord R p n J) :=
  Bialgebra.ofAlgHom (comul R p n J) (counit R p n J) (comul_coassoc R p n J)
    (comul_rTensor_counit R p n J) (comul_lTensor_counit R p n J)

theorem comulAlgHom_eq : Bialgebra.comulAlgHom R (Coord R p n J) = comul R p n J :=
  AlgHom.ext fun _ => rfl

theorem counitAlgHom_eq : Bialgebra.counitAlgHom R (Coord R p n J) = counit R p n J :=
  AlgHom.ext fun _ => rfl

theorem comul_def (x : Coord R p n J) : Coalgebra.comul (R := R) x = comul R p n J x := rfl

theorem counit_def (x : Coord R p n J) : Coalgebra.counit (R := R) x = counit R p n J x := rfl

theorem antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J))
        (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (Coord R p n J)) =
      (Algebra.ofId R (Coord R p n J)).comp (Bialgebra.counitAlgHom R (Coord R p n J)) := by
  rw [comulAlgHom_eq, counitAlgHom_eq]
  refine algHom_ext fun j i => ?_
  let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J :=
    (Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J))
      (fun _ _ => Commute.all _ _)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : Coord R p n J)) = antipode R p n J (X j i) := by
    intro i
    change Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J)) _
      (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hg2 : ∀ i, g ((1 : Coord R p n J) ⊗ₜ[R] X j i) = X j i := by
    intro i
    change Algebra.TensorProduct.lift (antipode R p n J) (AlgHom.id R (Coord R p n J)) _
      ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = algebraMap R (Coord R p n J) (counit R p n J (X j i))
  rw [h, counit_X, map_zero]
  have hS : (TruncatedWittVector.mk p fun i => antipode R p n J (X j i)) = -univ R p n j := by
    have := mk_ringHom_antipode (p := p) (RingHom.id (Coord R p n J)) j
    simp only [RingHom.id_apply] at this
    exact this
  have hU : (TruncatedWittVector.mk p fun i => (X j i : Coord R p n J)) = univ R p n j := rfl
  rw [hS, hU, neg_add_cancel, TruncatedWittVector.coeff_zero]

theorem antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J)
        (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom R (Coord R p n J)) =
      (Algebra.ofId R (Coord R p n J)).comp (Bialgebra.counitAlgHom R (Coord R p n J)) := by
  rw [comulAlgHom_eq, counitAlgHom_eq]
  refine algHom_ext fun j i => ?_
  let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J :=
    (Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J)
      (fun _ _ => Commute.all _ _)).toRingHom
  have h := ringHom_comul_X (p := p) g j i
  have hg1 : ∀ i, g (X j i ⊗ₜ[R] (1 : Coord R p n J)) = X j i := by
    intro i
    change Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J) _
      (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.id_apply]
  have hg2 : ∀ i, g ((1 : Coord R p n J) ⊗ₜ[R] X j i) = antipode R p n J (X j i) := by
    intro i
    change Algebra.TensorProduct.lift (AlgHom.id R (Coord R p n J)) (antipode R p n J) _
      ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  simp only [hg1, hg2] at h
  change g (comul R p n J (X j i)) = algebraMap R (Coord R p n J) (counit R p n J (X j i))
  rw [h, counit_X, map_zero]
  have hS : (TruncatedWittVector.mk p fun i => antipode R p n J (X j i)) = -univ R p n j := by
    have := mk_ringHom_antipode (p := p) (RingHom.id (Coord R p n J)) j
    simp only [RingHom.id_apply] at this
    exact this
  have hU : (TruncatedWittVector.mk p fun i => (X j i : Coord R p n J)) = univ R p n j := rfl
  rw [hS, hU, add_neg_cancel, TruncatedWittVector.coeff_zero]

noncomputable instance instHopfAlgebra : HopfAlgebra R (Coord R p n J) :=
  HopfAlgebra.ofAlgHom (antipode R p n J) (antipode_rTensor_comul R p n J) (antipode_lTensor_comul R p n J)

theorem antipode_def (x : Coord R p n J) : HopfAlgebra.antipode R x = antipode R p n J x := rfl

instance instIsCocomm : Coalgebra.IsCocomm R (Coord R p n J) := by
  refine ⟨?_⟩
  have h : (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.comp (comul R p n J) =
      comul R p n J := by
    refine algHom_ext fun j i => ?_
    let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J ⊗[R] Coord R p n J :=
      (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.toRingHom
    change g (comul R p n J (X j i)) = comul R p n J (X j i)
    rw [ringHom_comul_X, comul_X, add_comm]
    rfl
  refine LinearMap.ext fun x => ?_
  exact AlgHom.congr_fun h x

variable {R p n J}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

noncomputable def pointsEquiv : (Coord R p n J →ₐ[R] A) ≃ (J → TruncatedWittVector p n A) where
  toFun φ j := TruncatedWittVector.mk p fun i => φ (X j i)
  invFun x := lift fun j i => (x j).coeff i
  left_inv φ := algHom_ext fun j i => by rw [lift_X, TruncatedWittVector.coeff_mk]
  right_inv x := funext fun j => TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk, lift_X]

omit hp in
theorem pointsEquiv_apply (φ : Coord R p n J →ₐ[R] A) (j : J) :
    pointsEquiv φ j = TruncatedWittVector.mk p fun i => φ (X j i) := rfl

omit hp in
theorem coeff_pointsEquiv (φ : Coord R p n J →ₐ[R] A) (j : J) (i : Fin n) :
    (pointsEquiv φ j).coeff i = φ (X j i) := TruncatedWittVector.coeff_mk _ _

theorem pointsEquiv_eq_map_univ (φ : Coord R p n J →ₐ[R] A) (j : J) :
    pointsEquiv φ j = TruncWitt.map (p := p) φ.toRingHom (univ R p n j) := (map_univ φ.toRingHom j).symm

omit hp in
@[simp] theorem pointsEquiv_symm_apply_X (x : J → TruncatedWittVector p n A) (j : J) (i : Fin n) :
    pointsEquiv.symm x (X j i : Coord R p n J) = (x j).coeff i := lift_X _ j i

theorem pointsEquiv_mul (φ ψ : WithConv (Coord R p n J →ₐ[R] A)) :
    pointsEquiv (φ * ψ).ofConv = pointsEquiv φ.ofConv + pointsEquiv ψ.ofConv := by
  funext j
  rw [Pi.add_apply, pointsEquiv_apply, pointsEquiv_apply, pointsEquiv_apply]
  have key : ∀ i, (φ * ψ).ofConv (X j i) =
      (Algebra.TensorProduct.lift φ.ofConv ψ.ofConv (fun _ _ => Commute.all _ _)).toRingHom
        (comul R p n J (X j i)) := by
    intro i
    rw [AlgHom.convMul_apply, comul_def]
    rfl
  simp only [key]
  rw [mk_ringHom_comul]
  congr 1
  · refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.lift φ.ofConv ψ.ofConv _ (X j i ⊗ₜ[R] (1 : Coord R p n J)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · refine congrArg _ (funext fun i => ?_)
    change Algebra.TensorProduct.lift φ.ofConv ψ.ofConv _ ((1 : Coord R p n J) ⊗ₜ[R] X j i) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem pointsEquiv_one : pointsEquiv (1 : WithConv (Coord R p n J →ₐ[R] A)).ofConv = 0 := by
  funext j
  rw [Pi.zero_apply, pointsEquiv_apply]
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_zero, AlgHom.convOne_apply, counit_def,
    counit_X, map_zero]

theorem pointsEquiv_comp_antipode (φ : Coord R p n J →ₐ[R] A) :
    pointsEquiv (φ.comp (antipode R p n J)) = -pointsEquiv φ := by
  funext j
  rw [Pi.neg_apply, pointsEquiv_apply, pointsEquiv_apply]
  exact mk_ringHom_antipode φ.toRingHom j

end Points

theorem univ_mem_wittHom (j : J) : univ R p n j ∈ wittHom R p n (Coord R p n J) := by
  rw [mem_wittHom_iff]
  have hΔ : (comulRingHom R (Coord R p n J) : Coord R p n J →+* Coord R p n J ⊗[R] Coord R p n J) =
      (comul R p n J).toRingHom := RingHom.ext fun x => rfl
  rw [hΔ, map_univ, map_univ, map_univ]
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_mk]
  exact comul_X j i

noncomputable def univHom (j : J) : wittHom R p n (Coord R p n J) := ⟨univ R p n j, univ_mem_wittHom j⟩

@[simp] theorem coe_univHom (j : J) : (univHom (R := R) (p := p) (n := n) j : TruncatedWittVector p n (Coord R p n J)) =
    univ R p n j := rfl

omit hp in

theorem X_ne_zero [Nontrivial R] (j : J) (i : Fin n) : (X j i : Coord R p n J) ≠ 0 :=
  MvPolynomial.X_ne_zero (R := R) (j, i)

end WittGroup

end Deformation


