-- Prove2me | Definitions.Def_RPLib_S4_EtShUnramKer
-- name    : RPLib_S4_EtShUnramKer
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:18:17.040832+00:00
-- url     : https://prove2.me/theorems/d2841781-80f7-4008-ab92-9a2de2fe7e11
-- title:
--   Open kernel of a lisse Galois representation; ranges of normal embeddings
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For a lisse sheaf $F$ and $x \in X$, the kernel of the action $\mathrm{Gal}(\kappa(x)^{\mathrm{sep}}/\kappa(x)) \to \mathrm{Aut}(F_{\bar x})$ is open (the stalk is finitely generated and every generator has an open stabiliser). Also: two embeddings over $K$ of a normal extension of $K$ into the same field have the same range.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalCont
import Definitions.Def_RPLib_S4_EtShConst

/-!
# S4-EtSheaves, O10c part 5a: open kernel of a lisse Galois representation; ranges of normal embeddings

* `isOpen_ker_galRep`: for lisse `F`, the kernel of `Gal(κ(x)^sep/κ(x)) → Aut(F_x̄)` is open (finite stalk, each
  generator has an open stabilizer).
* `mem_fieldRange_of_normal`: two embeddings of a normal extension have the same range.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- **The Galois representation on a lisse stalk has open kernel.** -/
theorem isOpen_ker_galRep {F : EtSh Λ X} (hF : IsLisse Λ F) (x : X) :
    IsOpen ((galRep Λ F x).ker : Set (Gal x)) := by
  have hfin : Module.Finite Λ (stalk Λ F x) := hF.finite_stalkF (geomPtAt x)
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose H hHo hH using fun v : stalk Λ F x => exists_open_fix Λ F x v
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hmem : (⋂ v ∈ s, (H v : Set (Gal x))) ∈ nhds (1 : Gal x) :=
    (Filter.biInter_finset_mem s).mpr fun v _ => (hHo v).mem_nhds (H v).one_mem
  refine Filter.mem_of_superset hmem fun σ hσ => ?_
  rw [Set.mem_iInter₂] at hσ
  show σ ∈ (galRep Λ F x).ker
  rw [MonoidHom.mem_ker]
  exact LinearMap.ext_on hs fun v hv => hH v σ (hσ v hv)

/-- Two embeddings of a normal extension `E/F` into `M` have the same range. -/
theorem mem_fieldRange_of_normal {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra F M]
    [Normal F E] (f g : E →ₐ[F] M) (x : E) : f x ∈ g.fieldRange := by
  let e := g.equivFieldRange
  have : Normal F g.fieldRange := Normal.of_algEquiv e
  rw [← AlgHom.fieldRange_of_normal (f.comp e.symm.toAlgHom)]
  refine ⟨e x, ?_⟩
  show f (e.symm (e x)) = f x
  rw [AlgEquiv.symm_apply_apply]

end RamanujanPetersson.EtSheaves


