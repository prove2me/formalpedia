-- Prove2me | Definitions.Def_Deformations_DualNumbers
-- name    : Deformations_DualNumbers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/9b22d289-5a0d-58b7-93db-ddf7384edd51
-- title:
--   Dual numbers as an object of the pro-Artinian category
-- statement:
--   Fix a commutative local ring $\mathcal O$ and write $k = \mathcal O/\mathfrak m_{\mathcal O}$ for its residue field, denoted `𝓴 𝓞`. This module equips Mathlib's ring of dual numbers $k[\varepsilon] = k \oplus k\varepsilon$ with $\varepsilon^2 = 0$ (the trivial square-zero extension of $k$ by $k$) with all the structure needed to view it as an object of the category `ProartinianCat 𝓞`, whose objects are topological commutative $\mathcal O$-algebras $R$ that are local rings with linear, $T_0$, complete topology in which every quotient by an open ideal is Artinian, such that $\mathcal O \to R$ is a local homomorphism and $\mathcal O \to \mathrm{ResidueField}(R)$ is surjective, and whose morphisms are continuous $\mathcal O$-algebra homomorphisms. Accordingly it is recorded that $k[\varepsilon]$ is a finite $k$-module, hence an Artinian ring; that it carries the discrete topology; that $\mathcal O \to k[\varepsilon]$, $a \mapsto \mathrm{inl}(\bar a)$, is local; and that $\mathcal O$ surjects onto the residue field of $k[\varepsilon]$. The auxiliary lemma `residue_inl_fst_eq` states that for $y \in k[\varepsilon]$ the elements $\mathrm{inl}(y_{\mathrm{fst}})$ and $y$ have the same image in the residue field of $k[\varepsilon]$, i.e. $k\varepsilon \subseteq \mathfrak m_{k[\varepsilon]}$.
--
--   The object itself is `dualNumbers 𝓞`, the object of `ProartinianCat 𝓞` with carrier $k[\varepsilon]$; its topology is discrete. The morphism `dualNumbersFst 𝓞 : dualNumbers 𝓞 ⟶ residueField` is given by the first-coordinate $\mathcal O$-algebra homomorphism $k[\varepsilon] \to k$, $a + b\varepsilon \mapsto a$, which is continuous since the source is discrete. Finally `eq_dualNumbersFst` asserts that every morphism from `dualNumbers 𝓞` to `residueField` equals this projection, `residueField` being terminal in `ProartinianCat 𝓞`.
--
--   **Relation to Mathlib.** The carrier is Mathlib's `DualNumber`, i.e. `TrivSqZeroExt` of a ring over itself, together with its `fstHom`; the ambient category `ProartinianCat`, the classes [`IsProartinian`](../def/Deformations_IsProartinian.html#L185), [`IsResidueAlgebra`](../def/Deformations_IsResidueAlgebra.html#L15) and `IsLocalProartinianAlgebra`, and the terminal object `residueField` are the project's own notions.
--
--   **Where it is used.** The dual numbers are the test object of deformation theory: morphisms from a universal deformation ring to $k[\varepsilon]$ compute the tangent space of the deformation functor, which is identified with a Galois cohomology group and bounded in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_DualNumbers.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

namespace Deformation

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

instance : Module.Finite (𝓴 𝓞) ((𝓴 𝓞)[ε]) :=
  inferInstanceAs (Module.Finite (𝓴 𝓞) ((𝓴 𝓞) × (𝓴 𝓞)))

instance : IsArtinianRing ((𝓴 𝓞)[ε]) :=
  IsArtinianRing.of_finite (𝓴 𝓞) ((𝓴 𝓞)[ε])

instance : TopologicalSpace ((𝓴 𝓞)[ε]) := ⊥

instance : DiscreteTopology ((𝓴 𝓞)[ε]) := ⟨rfl⟩

instance : IsLocalHom (algebraMap 𝓞 ((𝓴 𝓞)[ε])) where
  map_nonunit a ha := by
    rw [show algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl (algebraMap 𝓞 (𝓴 𝓞) a) from rfl,
      TrivSqZeroExt.isUnit_inl_iff] at ha
    exact (isUnit_map_iff (algebraMap 𝓞 (𝓴 𝓞)) a).mp ha

lemma residue_inl_fst_eq (y : (𝓴 𝓞)[ε]) :
    residue ((𝓴 𝓞)[ε]) (TrivSqZeroExt.inl y.fst) = residue ((𝓴 𝓞)[ε]) y := by
  refine Ideal.Quotient.eq.mpr ?_
  have h3 : TrivSqZeroExt.inl y.fst - y = -TrivSqZeroExt.inr y.snd := by
    ext <;> simp
  rw [h3]
  refine neg_mem (IsLocalRing.mem_maximalIdeal _ |>.mpr ?_)
  rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_inr_iff]
  exact fun h => (not_subsingleton (𝓴 𝓞)) h

instance : IsResidueAlgebra 𝓞 ((𝓴 𝓞)[ε]) where
  isSurjective' := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := 𝓞) y.fst
    refine ⟨a, ?_⟩
    have h1 : algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl y.fst := by
      rw [show algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl (algebraMap 𝓞 (𝓴 𝓞) a) from rfl,
        show algebraMap 𝓞 (𝓴 𝓞) a = residue 𝓞 a from rfl, ha]
    calc algebraMap 𝓞 (𝓴 ((𝓴 𝓞)[ε])) a
        = residue ((𝓴 𝓞)[ε]) (algebraMap 𝓞 ((𝓴 𝓞)[ε]) a) := rfl
      _ = residue ((𝓴 𝓞)[ε]) (TrivSqZeroExt.inl y.fst) := by rw [h1]
      _ = (Ideal.Quotient.mk (maximalIdeal ((𝓴 𝓞)[ε]))) y := residue_inl_fst_eq 𝓞 y

instance : IsLocalProartinianAlgebra 𝓞 ((𝓴 𝓞)[ε]) := ⟨⟩

noncomputable def dualNumbers : ProartinianCat 𝓞 :=
  .of 𝓞 ((𝓴 𝓞)[ε])

instance : DiscreteTopology (dualNumbers 𝓞) :=
  inferInstanceAs (DiscreteTopology ((𝓴 𝓞)[ε]))

noncomputable def dualNumbersFst : dualNumbers 𝓞 ⟶ residueField where
  hom := ⟨TrivSqZeroExt.fstHom 𝓞 (𝓴 𝓞) (𝓴 𝓞), continuous_of_discreteTopology⟩

lemma eq_dualNumbersFst (f : dualNumbers 𝓞 ⟶ residueField) : f = dualNumbersFst 𝓞 :=
  Subsingleton.elim _ _

end ProartinianCat

end Deformation


