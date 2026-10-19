-- Prove2me | Definitions.Def_MazurTransfer_PullbackRelativeFieldPoints
-- name    : MazurTransfer_PullbackRelativeFieldPoints
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:42:45.489982+00:00
-- url     : https://prove2.me/theorems/54d06334-3e8e-49cb-9e41-481c700b86db
-- title:
--   Field-valued points of a Cartesian fibre and relative points
-- statement:
--   Let $R$ be a commutative ring, $K$ a field, and let a Cartesian square of schemes have upper map $p:X^{\prime}\to X$, lower map $i:\operatorname{Spec}K\to\operatorname{Spec}R$, and structure maps $c^{\prime}$ and $c$. Composition with $p$ gives a bijection
--   $$\{a:\operatorname{Spec}K\to X^{\prime}\mid c^{\prime}\circ a=\operatorname{id}\}\;\xrightarrow{\sim}\;\{b:\operatorname{Spec}K\to X\mid c\circ b=i\},\qquad a\longmapsto p\circ a.$$
--
--   The constructor and its structural bijectivity proof retain the projection map explicitly. They transfer point injectivity from the actual literal order-thirteen curve over a field to relative field-valued points of the integral curve.
-- source:
--   MazurTheorem working proof PullbackRelativeFieldPoints.lean, exact byte-for-byte copy with unchanged imports, declarations, proofs, and statement types. Copyright 2026 Vas and contributors, Apache-2.0. Named downstream consumer: Order13LiteralCurvePointDifferenceInjection.relative_point_map_injective_of_dictionary.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual points of a scheme fibre identify bijectively with
relative field-valued points of the original scheme, retaining projection.
Named downstream consumer: read the integral order13 Abel-Jacobi dictionary
on the literal field curve and transfer its point injectivity. -/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
namespace MazurTransfer.PullbackRelativeFieldPoints
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u
variable {R K : Type u} [CommRing R] [Field K] {X X' : Scheme.{u}}
  (c : X ⟶ Spec (.of R)) (c' : X' ⟶ Spec (.of K))
  (p : X' ⟶ X) (i : Spec (.of K) ⟶ Spec (.of R))
  (h : IsPullback p c' c i)

def project (a : SchemeHomOver (𝟙 (Spec (.of K))) c') : SchemeHomOver i c :=
  ⟨a.val ≫ p, by
    calc
      _ = a.val ≫ (p ≫ c) := Category.assoc _ _ _
      _ = a.val ≫ (c' ≫ i) := congrArg (fun b => a.val ≫ b) h.w
      _ = (a.val ≫ c') ≫ i := (Category.assoc _ _ _).symm
      _ = i := (congrArg (fun b => b ≫ i) a.property).trans (Category.id_comp i)⟩

theorem project_bijective : Function.Bijective (project c c' p i h) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact h.hom_ext (congrArg Subtype.val hab) (a.property.trans b.property.symm)
  · intro a
    obtain ⟨l, hl, hb⟩ := h.exists_lift a.val (𝟙 _) (a.property.trans (Category.id_comp i).symm)
    exact ⟨⟨l,hb⟩,Subtype.ext hl⟩

end MazurTransfer.PullbackRelativeFieldPoints
#print axioms MazurTransfer.PullbackRelativeFieldPoints.project_bijective


