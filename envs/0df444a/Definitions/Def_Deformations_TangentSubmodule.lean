-- Prove2me | Definitions.Def_Deformations_TangentSubmodule
-- name    : Deformations_TangentSubmodule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/0671f100-eebf-5f8a-996a-347c563d8302
-- title:
--   Residue map and tangent space of a pro-Artinian algebra
-- statement:
--   Throughout, $\mathcal O$ is a commutative local ring with residue field $\mathfrak k = \mathrm{ResidueField}\,\mathcal O$, and $R$ is an object of `ProartinianCat 𝓞`, i.e. a topological local $\mathcal O$-algebra which is pro-Artinian, with $\mathcal O \to R$ local and inducing an isomorphism on residue fields.
--
--   First, `residueMap R` is the underlying function $R \to \mathfrak k$ of the canonical morphism `toResidueField R` from $R$ to the residue-field object (the discrete object with carrier $\mathfrak k$, terminal in the category): concretely, the residue map of $R$ followed by the inverse of the identification $\mathfrak k \cong \mathfrak k_R$. The accompanying lemmas record that it sends $1$ to $1$ and $0$ to $0$, is additive and multiplicative, is compatible with the structure map $\mathcal O \to R$ and with $\mathcal O \to \mathfrak k$, vanishes on the maximal ideal of $R$ (its kernel being exactly $\mathfrak m_R$), and is locally constant, the last from continuity into the discrete residue field.
--
--   Next, `IsTangentVector R D`, for a function $D : R \to \mathfrak k$, is the conjunction of four conditions, packaged as a `Prop`-valued structure: additivity $D(r+s) = D(r) + D(s)$; the Leibniz rule twisted by the residue map, $D(rs) = \bar r\,D(s) + D(r)\,\bar s$; vanishing on the image of $\mathcal O$, $D(\mathrm{algebraMap}\,o) = 0$; and local constancy of $D$. Thus no $\mathfrak k$-linearity is imposed, only additivity. Two consequences are recorded: $D(0) = 0$ and $D(1) = 0$.
--
--   Finally, `tangentSubmodule R` is the set of such $D$, presented as a $\mathfrak k$-submodule of the function space $R \to \mathfrak k$ with its pointwise operations: it contains $0$ and is closed under pointwise sums and under multiplication by scalars in $\mathfrak k$. A simp lemma identifies membership in it with the predicate `IsTangentVector`.
--
--   **Relation to Mathlib.** The local-constancy and submodule formalism are Mathlib's (`IsLocallyConstant`, `Submodule`), but the tangent-vector predicate is the project's own: it is an additive, locally constant map to the residue field obeying the Leibniz rule twisted along `residueMap`, rather than an instance of Mathlib's `Derivation` (which is a module-linear map into a module).
--
--   **Where it is used.** This $\mathfrak k$-module is the tangent space $t_R$ of an object of the pro-Artinian category; its dimension controls the number of generators needed to present $R$ as a quotient of a power series ring over $\mathcal O$, and its finiteness gives Noetherianity of deformation rings. For universal deformation rings of a residual Galois representation the tangent space is computed by Galois cohomology, which is where the Taylor–Wiles numerology enters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_TangentSubmodule.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace Deformation

open CategoryTheory IsLocalRing ProartinianCat

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
variable {R : ProartinianCat 𝓞}

variable (R) in

noncomputable def residueMap (r : R) : 𝓴 𝓞 := (toResidueField R).hom r

lemma residueMap_one : residueMap R (1 : R) = 1 := map_one (toResidueField R).hom

lemma residueMap_mul (r s : R) : residueMap R (r * s) = residueMap R r * residueMap R s :=
  map_mul (toResidueField R).hom r s

lemma residueMap_add (r s : R) : residueMap R (r + s) = residueMap R r + residueMap R s :=
  map_add (toResidueField R).hom r s

lemma residueMap_zero : residueMap R (0 : R) = 0 := map_zero (toResidueField R).hom

lemma residueMap_algebraMap (o : 𝓞) :
    residueMap R (algebraMap 𝓞 R o) = algebraMap 𝓞 (𝓴 𝓞) o :=
  (toResidueField R).hom.commutes o

lemma residueMap_eq_zero_of_mem {r : R} (hr : r ∈ maximalIdeal R) : residueMap R r = 0 := by
  show (toResidueField R).hom r = 0
  rw [← RingHom.mem_ker, ker_toResidueField R]
  exact hr

lemma isLocallyConstant_residueMap : IsLocallyConstant (residueMap R) :=
  (IsLocallyConstant.iff_continuous
    ((toResidueField R).hom : R → (residueField (𝓞 := 𝓞)))).mpr (toResidueField R).hom.cont

variable (R) in

structure IsTangentVector (D : R → 𝓴 𝓞) : Prop where
  map_add : ∀ r s, D (r + s) = D r + D s
  leibniz : ∀ r s, D (r * s) = residueMap R r * D s + D r * residueMap R s
  map_algebraMap : ∀ o : 𝓞, D (algebraMap 𝓞 R o) = 0
  isLocallyConstant : IsLocallyConstant D

namespace IsTangentVector

variable {D : R → 𝓴 𝓞} (hD : IsTangentVector R D)

include hD

lemma map_zero : D 0 = 0 := by
  have h := (hD.map_add 0 0).symm
  rw [add_zero] at h
  exact add_left_cancel (h.trans (add_zero (D 0)).symm)

lemma map_one : D 1 = 0 := by simpa using hD.map_algebraMap 1

end IsTangentVector

variable (R) in

def tangentSubmodule : Submodule (𝓴 𝓞) (R → 𝓴 𝓞) where
  carrier := {D | IsTangentVector R D}
  zero_mem' :=
    { map_add := fun _ _ => (add_zero (0 : 𝓴 𝓞)).symm
      leibniz := fun r s => by simp
      map_algebraMap := fun _ => rfl
      isLocallyConstant := IsLocallyConstant.const 0 }
  add_mem' := by
    rintro D D' hD hD'
    exact
      { map_add := fun r s => by
          simp only [Pi.add_apply, hD.map_add, hD'.map_add]; ring
        leibniz := fun r s => by
          simp only [Pi.add_apply, hD.leibniz, hD'.leibniz]; ring
        map_algebraMap := fun o => by
          simp only [Pi.add_apply, hD.map_algebraMap, hD'.map_algebraMap, add_zero]
        isLocallyConstant :=
          IsLocallyConstant.comp₂ hD.isLocallyConstant hD'.isLocallyConstant (· + ·) }
  smul_mem' := by
    rintro c D hD
    exact
      { map_add := fun r s => by
          simp only [Pi.smul_apply, hD.map_add, smul_eq_mul]; ring
        leibniz := fun r s => by
          simp only [Pi.smul_apply, hD.leibniz, smul_eq_mul]; ring
        map_algebraMap := fun o => by
          simp only [Pi.smul_apply, hD.map_algebraMap, smul_zero]
        isLocallyConstant := hD.isLocallyConstant.comp (c • ·) }

@[simp]
lemma mem_tangentSubmodule {D : R → 𝓴 𝓞} : D ∈ tangentSubmodule R ↔ IsTangentVector R D :=
  Iff.rfl

end ProartinianCat

end Deformation


