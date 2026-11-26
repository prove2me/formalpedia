-- Prove2me | Definitions.Def_ProEtale_Comparator_Lib
-- name    : ProEtale_Comparator_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:35.849987+00:00
-- url     : https://prove2.me/theorems/11bdd775-5ac5-5abc-ace8-a0ad445c8c9d
-- title:
--   Comparison of ℓ-adic and étale cohomology: full faithfulness of the étale-to-pro-étale inclusion and descriptions of the cohomology systems
-- statement:
--   This file continues the published file of the same name, which provides the definitions for comparing the $\ell$-adic cohomology of a scheme $X$ with the étale cohomology of the constant sheaves $\mathbb Z/\ell^n\mathbb Z$, via the zig-zag
--   $$H^m_{\ell\text{-adic}}(X) \longrightarrow \lim_n H^m(X_{\text{proét}}, \mathbb Z/\ell^n) \longleftarrow \lim_n H^m(X_{\text{ét}}, \mathbb Z/\ell^n).$$
--   This part contains:
--
--   1. the inclusion functor $\nu : S_{\text{ét}} \to S_{\text{proét}}$ from the small étale site to the pro-étale site of a scheme $S$ is full and faithful;
--   2. the value of the étale cohomology system at level $n$ is, by definition, the sheaf cohomology group $H^m\big(X_{\text{ét}}, \underline{\mathbb Z/\ell^n\mathbb Z}\big)$ of the constant étale sheaf;
--   3. the value of the pro-étale cohomology system at level $n$ is, by definition, $H^m\big(X_{\text{proét}}, C(-, \mathbb Z/\ell^n\mathbb Z)\big)$, the cohomology of the sheaf of continuous (equivalently locally constant) $\mathbb Z/\ell^n$-valued functions;
--   4. Mathlib's $\ell$-adic sheaf $U \mapsto C(U, \mathbb Z_\ell)$ coincides by definition with the general sheaf of continuous $\mathbb Z_\ell$-valued functions.
--
--   These statements make the comparison maps transparent for the challenge statement that compares $\ell$-adic and étale cohomology.
--
--   **Formalization Note** Main declarations: the `Full` and `Faithful` instances for `AlgebraicGeometry.Scheme.toProEtale S`, `EllAdicEtaleComparison.etaleCohomologySystem_obj`, `EllAdicEtaleComparison.proetaleCohomologySystem_obj`, `EllAdicEtaleComparison.ellAdicSheaf_eq_topologicalSheaf`. Items 2–4 are definitional (`rfl`). Cohomology is Mathlib's `CategoryTheory.Sheaf.H` with values in `Ab.{u+1}` for `X : Scheme.{u}`; coefficients are `ULift.{u+1} (ZMod (ℓ ^ n))` on the étale side and `topologicalSheafULift X (ZMod (ℓ ^ n))` on the pro-étale side. No primality of $\ell$ is assumed in items 2–3; item 4 assumes `Fact ℓ.Prime`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Comparator/Definitions.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Definitions: comparison maps between `ℓ`-adic and étale cohomology

This file provides the definitions shared by the `leanprover/comparator`
challenge/solution pair in this directory (see `Challenge.lean` and `Solution.lean`).
It only imports mathlib.

This file constructs, two canonical comparison maps relating it to the étale
cohomology of the constant sheaves `ℤ/ℓⁿℤ`. The
canonical comparison is the zig-zag

`X.EllAdicCohomology ℓ m ⟶ lim_n Hᵐ(X_proét, ℤ/ℓⁿℤ) ⟵ lim_n Hᵐ(X_ét, ℤ/ℓⁿℤ)`

through the pro-étale cohomology of the sheaves of continuous (equivalently, locally
constant) `ℤ/ℓⁿℤ`-valued functions, defined in exact analogy with mathlib's
`ellAdicSheaf`:

- `EllAdicEtaleComparison.ellAdicCohomologyToLimit`: the first map, induced by the
  reductions `ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves.
- `EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom`: the levelwise second
  map, given by functoriality of `Ext` along the pullback `ν^*` from the small étale
  site to the pro-étale site, together with the canonical comparison morphisms of
  constant sheaves (all obtained from adjunctions).
-/

universe u v w

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty


variable (X : Scheme.{u})

/-! ### The inclusion of the small étale site into the pro-étale site

We equip the inclusion `ν : X.Etale ⥤ X.ProEt` with its continuity and flatness
instances, and record that the associated pullback functor on abelian sheaves is exact.
-/

namespace AlgebraicGeometry
namespace Scheme


variable (S : Scheme.{u})

instance inst_ComparatorDefinitions_L70 : (toProEtale S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance inst_ComparatorDefinitions_L73 : (toProEtale S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful


end Scheme
end AlgebraicGeometry

open AlgebraicGeometry.Scheme ProEt

namespace EllAdicEtaleComparison


/-! ### Terminal objects and constant sheaf units -/


/-! ### The étale side: the system of constant sheaves `ℤ/ℓⁿℤ` -/


/-- The value of `etaleCohomologySystem` at level `n` is the étale cohomology
`Hᵐ(X_ét, ℤ/ℓⁿℤ)` in the sense of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem etaleCohomologySystem_obj (ℓ m n : ℕ) :
    (etaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) m) :=
  rfl

/-! ### The pro-étale side: the system of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions

In analogy with mathlib's `ellAdicSheaf` (`U ↦ C(U, ℤ_[ℓ])`), we consider the sheaves
`U ↦ C(U, ℤ/ℓⁿℤ)` on the pro-étale site of `X`. Since `ℤ/ℓⁿℤ` is discrete, these are
the sheaves of locally constant `ℤ/ℓⁿℤ`-valued functions; their cohomology is the
pro-étale cohomology of `X` with `ℤ/ℓⁿℤ`-coefficients.
-/

section Topological

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]


lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl


variable {C : Type*} [Category C] {J : GrothendieckTopology C}


end Topological


/-- The value of `proetaleCohomologySystem` at level `n` is the pro-étale cohomology
`Hᵐ(X_proét, ℤ/ℓⁿℤ)` of the sheaf of continuous `ℤ/ℓⁿℤ`-valued functions in the sense
of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem proetaleCohomologySystem_obj (ℓ m n : ℕ) :
    (proetaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H (topologicalSheafULift.{u, 0, u + 1} X (ZMod (ℓ ^ n))) m) :=
  rfl

/-! ### The reduction map from `ℓ`-adic cohomology to the limit -/


/-! ### The comparison map from étale to pro-étale cohomology -/


end EllAdicEtaleComparison


