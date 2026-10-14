-- Prove2me | Definitions.Def_SelmerGroup_GaloisPoints
-- name    : SelmerGroup_GaloisPoints
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T15:53:25.851578+00:00
-- url     : https://prove2.me/theorems/c65e226a-30c5-488c-9532-8bf5f061f567
-- title:
--   Galois action on points of an elliptic curve; local restriction
-- statement:
--   Let $E$ be a Weierstrass curve over a field $K$. For a field $L$ containing $K$:
--
--   1. $E(L)$ is the group of $L$-rational points of $E$, and a $K$-algebra map $f:F\to L$ induces $f_*:E(F)\to E(L)$ on coordinates.
--   2. $E(L)[n]=\{P\in E(L): nP=0\}$ is the $n$-torsion subgroup.
--   3. The absolute Galois group $G_L=\mathrm{Gal}(\bar L/L)$ acts on $E(\bar L)$ through coordinates, and this action preserves $E(\bar L)[n]$.
--   4. A $K$-embedding $\iota_L:\bar K\to\bar L$ is fixed once and for all. It determines the restriction homomorphism $\mathrm{res}_L:G_L\to G_K$, characterised by $\iota_L(\mathrm{res}_L(\sigma)x)=\sigma(\iota_L x)$.
--   5. For a map $f:G_K\to E(\bar K)$, its restriction to $G_L$ is $\sigma\mapsto\iota_{L*}\big(f(\mathrm{res}_L\sigma)\big)\in E(\bar L)$.
--
--   For a place $v$ of a number field $K$ and $L=K_v$, items 3–5 give the decomposition-group action and the restriction map $H^1(G_K,\cdot)\to H^1(G_{K_v},\cdot)$ on cocycles.
--
--   **Formalization Note** $G_L$ is `Field.absoluteGaloisGroup L`. The embedding $\iota_L$ is `IsAlgClosed.lift`.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1

/-!
# Galois modules attached to an elliptic curve

Let `E` be a Weierstrass curve over a field `K`. For a field `L` with a `K`-algebra
structure we define
* `Pts E L`, the group `E(L)` of `L`-rational points of `E`;
* `ptsMap E f : E(F) →+ E(L)` induced by a `K`-algebra map `f : F →ₐ[K] L`;
* `tors E L n`, the `n`-torsion subgroup `E(L)[n]`;
* `absAct E L`, the action of the absolute Galois group `G_L = Gal(L̄/L)` on `E(L̄)`,
  and `absTorsAct E L n`, its restriction to `E(L̄)[n]`;
* `embed L : K̄ →ₐ[K] L̄`, a fixed `K`-embedding of algebraic closures, and the induced
  restriction homomorphism `res L : G_L →* G_K` characterised by
  `embed L (res L σ x) = σ (embed L x)`;
* `localize E L f`, the restriction to `G_L` of a cochain `f : G_K → E(K̄)`, i.e.
  `σ ↦ embed L (f (res L σ))`.
-/

noncomputable section

open WeierstrassCurve

namespace SelmerGroup

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- The group `E(L)` of `L`-rational points of `E`, for a field `L` over `K`. -/
def Pts (L : Type*) [Field L] [Algebra K L] : Type _ := (E.baseChange L).toAffine.Point

instance (L : Type*) [Field L] [Algebra K L] : AddCommGroup (Pts E L) := by
  classical exact inferInstanceAs (AddCommGroup (E.baseChange L).toAffine.Point)

/-- The homomorphism `E(F) → E(L)` induced by a `K`-algebra homomorphism `F → L`. -/
def ptsMap {F L : Type*} [Field F] [Field L] [Algebra K F] [Algebra K L] (f : F →ₐ[K] L) :
    Pts E F →+ Pts E L := by
  classical exact WeierstrassCurve.Affine.Point.map (W' := E) (S := K) f

/-- The action of `Aut_K(L)` on `E(L)`. -/
def galAct (L : Type*) [Field L] [Algebra K L] : (L ≃ₐ[K] L) →* AddMonoid.End (Pts E L) where
  toFun σ := ptsMap E (σ : L →ₐ[K] L)
  map_one' := by
    classical
    refine AddMonoidHom.ext fun P => ?_
    change WeierstrassCurve.Affine.Point.map _ P = P
    rcases P with _ | ⟨h⟩ <;> rfl
  map_mul' σ τ := by
    classical
    refine AddMonoidHom.ext fun P => ?_
    change WeierstrassCurve.Affine.Point.map _ P =
      WeierstrassCurve.Affine.Point.map _ (WeierstrassCurve.Affine.Point.map _ P)
    rcases P with _ | ⟨h⟩ <;> rfl

/-- The `n`-torsion subgroup `E(L)[n]`. -/
def tors (L : Type*) [Field L] [Algebra K L] (n : ℕ) : AddSubgroup (Pts E L) :=
  (nsmulAddMonoidHom n : Pts E L →+ Pts E L).ker

/-- The action of the absolute Galois group `G_L = Gal(L̄/L)` on `E(L̄)`. -/
def absAct (L : Type*) [Field L] [Algebra K L] :
    Field.absoluteGaloisGroup L →* AddMonoid.End (Pts E (AlgebraicClosure L)) where
  toFun σ := galAct E (AlgebraicClosure L) (AlgEquiv.restrictScalars K σ)
  map_one' := by
    rw [← (galAct E (AlgebraicClosure L)).map_one]
    rfl
  map_mul' σ τ := by
    rw [← (galAct E (AlgebraicClosure L)).map_mul]
    rfl

lemma absAct_mem_tors (L : Type*) [Field L] [Algebra K L] (n : ℕ)
    (σ : Field.absoluteGaloisGroup L) (P : Pts E (AlgebraicClosure L))
    (hP : P ∈ tors E (AlgebraicClosure L) n) : absAct E L σ P ∈ tors E (AlgebraicClosure L) n := by
  simp only [tors, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- The action of `G_L` on the `n`-torsion `E(L̄)[n]`. -/
def absTorsAct (L : Type*) [Field L] [Algebra K L] (n : ℕ) :
    Field.absoluteGaloisGroup L →* AddMonoid.End (tors E (AlgebraicClosure L) n) where
  toFun σ :=
    { toFun := fun P => ⟨absAct E L σ P, absAct_mem_tors E L n σ P P.2⟩
      map_zero' := by ext; simp
      map_add' := fun P Q => by ext; simp }
  map_one' := AddMonoidHom.ext fun P => Subtype.ext (by simp; rfl)
  map_mul' σ τ := AddMonoidHom.ext fun P => Subtype.ext (by simp; rfl)

/-- A fixed `K`-embedding of the algebraic closure of `K` into that of `L`. -/
def embed (L : Type*) [Field L] [Algebra K L] : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
  IsAlgClosed.lift

/-- The restriction homomorphism `G_L → G_K` determined by `embed L`:
`embed L (res L σ x) = σ (embed L x)`. -/
def res (L : Type*) [Field L] [Algebra K L] :
    Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K :=
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := (embed L).toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq fun x => ((embed L).commutes x).symm
  { toFun := fun σ =>
      AlgEquiv.restrictNormalHom (AlgebraicClosure K) (AlgEquiv.restrictScalars K σ)
    map_one' := (AlgEquiv.restrictNormalHom (AlgebraicClosure K)).map_one
    map_mul' := fun σ τ => (AlgEquiv.restrictNormalHom (AlgebraicClosure K)).map_mul
      (AlgEquiv.restrictScalars K σ) (AlgEquiv.restrictScalars K τ) }

/-- Restriction to `G_L` of a cochain `f : G_K → E(K̄)`: `σ ↦ embed L (f (res L σ))`. -/
def localize (L : Type*) [Field L] [Algebra K L]
    (f : Field.absoluteGaloisGroup K → Pts E (AlgebraicClosure K)) :
    Field.absoluteGaloisGroup L → Pts E (AlgebraicClosure L) :=
  fun σ => ptsMap E (embed L) (f (res L σ))

end SelmerGroup


