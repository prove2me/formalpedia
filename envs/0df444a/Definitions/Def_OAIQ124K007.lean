-- Prove2me | Definitions.Def_OAIQ124K007
-- name    : OAIQ124K007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:45:02.979687+00:00
-- url     : https://prove2.me/theorems/3c2bd16f-ea50-4aee-ab41-edb65985bd50
-- title:
--   Definitions bundle OAIQ124K007 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 24 definitions, 2 inductive types or structures, 3 instances and 8 theorems. The definitions and types are `OAI.KLInvariance.Hilbert.shiftedImagePieceEquiv`, `OAI.KLInvariance.Hilbert.shiftedImagePieceMap`, `OAI.KLInvariance.Hilbert.shiftedPieceEquiv`, `OAI.KLInvariance.Hilbert.subPieceEquiv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnIso`, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso`, `OAI.KLInvariance.MomentGraph.Sheaf.OnIso.prodZero`, `OAI.KLInvariance.MomentGraph.Sheaf.castStalkIso`, `OAI.KLInvariance.MomentGraph.Sheaf.pi`, `OAI.KLInvariance.MomentGraph.Sheaf.prod`, `OAI.KLInvariance.MomentGraph.Sheaf.zero`, `OAI.KLInvariance.ReflectionPairTranslation.Twist.scalarEquiv`, `OAI.KLInvariance.SchedulePaths.dispatch`, `OAI.KLInvariance.SchedulePaths.pathTerm`, `OAI.KLInvariance.SchedulePaths.step`, `OAI.KLInvariance.SignedDihedral.arrowAfter`, `OAI.KLInvariance.SignedDihedral.countAfter`, `OAI.KLInvariance.TitsSpace.RatioOrder.Adapted`, `OAI.KLInvariance.TitsSpace.RatioOrder.Chamber`, `OAI.KLInvariance.TitsSpace.RatioOrder.turnDenominator`, `OAI.KLInvariance.TitsSpace.RatioOrder.turnNumerator`, `OAI.KLInvariance.TitsSpace.edgeFactorDegree`, `OAI.KLInvariance.TitsSpace.finiteEdges`, `OAI.KLInvariance.TitsSpace.rWordInterval`, `OAI.KLInvariance.intervalBottom`, `OAI.KLInvariance.intervalTop`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_CanonicalKL`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_HilbertSeries`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_OrdinaryR`, `KazhdanLusztig_PlaneLocalization`, `KazhdanLusztig_PositiveTransfer`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_Sheaves`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K000`, `OAIQ124K001`, `OAIQ124K002` and `OAIQ124K003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K011`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K000
import Definitions.Def_OAIQ124K001
import Definitions.Def_OAIQ124K002
import Definitions.Def_OAIQ124K003

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_OrdinaryR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace OrdinaryR

open LaurentPolynomial

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
@[simp] theorem eval_variableUnit (p : ℤ[X]) :
    Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ))
      (variableUnit : LaurentPolynomial ℤ) p = p.toLaurent := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (LaurentPolynomial ℤ))
      (variableUnit : LaurentPolynomial ℤ) = Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.toLaurent_C]
      exact (map_intCast (LaurentPolynomial.C : ℤ →+* LaurentPolynomial ℤ) a).symm
    · simp
  exact congrArg (fun f : ℤ[X] →+* LaurentPolynomial ℤ => f p) h

end OrdinaryR


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CanonicalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

/-- Named endpoints for an actual nonempty interval. -/
def intervalBottom (cs : CoxeterSystem M W) {u b : W} (hub : BruhatLE cs u b) :
    Interval cs u b := ⟨u, bruhat_refl cs u, hub⟩

def intervalTop (cs : CoxeterSystem M W) {u b : W} (hub : BruhatLE cs u b) :
    Interval cs u b := ⟨b, hub, bruhat_refl cs b⟩

end KLInvariance

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

theorem closedUnder_insert (live : Set E) (Ω : Set V)
    (hΩ : B.ClosedUnder live Ω) (a : V) (hmax : ∀ y, a < y → y ∈ Ω) :
    B.ClosedUnder live (insert a Ω) := by
  intro e he hs
  rcases Set.mem_insert_iff.mp hs with hs | hs
  · exact Set.mem_insert_of_mem _ (hmax _ (hs ▸ G.increasing e))
  · exact Set.mem_insert_of_mem _ (hΩ e he hs)

end Sheaf
end KLInvariance.MomentGraph

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_5
def edgeFactorDegree (x : W) (a : PositiveRoot M cs) : ℕ :=
  ∑ P : (planeWeight x a).support, (planeWeight x a P.val).toNat

end
end KLInvariance.TitsSpace


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V)

variable [Semiring R]
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions
def pathTerm (T : R) (v : V → R) : List E → V → R
  | [], x => v x
  | e :: p, x => if source e = x then T * pathTerm T v p (target e) else 0

/-- One elementary matrix `1+T E_xy`, acting without choosing an enumeration
of the finite vertex set. -/
def step (T : R) (e : E) (v : V → R) : V → R :=
  fun x => v x + if source e = x then T * v (target e) else 0

/-- Edges are listed in decreasing schedule order, so the chronologically
last transfer is the outermost one. -/
def dispatch (T : R) (v : V → R) : List E → V → R
  | [] => v
  | e :: p => step source target T e (dispatch T v p)

end
end KLInvariance.SchedulePaths

/-! NEW GRAPH CLOSURE -/


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i}

/-- Finite direct sums represented by products, as used in the plane localization. -/
def pi (B : ι → Sheaf.{u,v,w,z} (R := R) G) : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (∀ i, (B i).vertex x)
  edge e := ModuleCat.of R (∀ i, (B i).edge e)
  lower e := LinearMap.pi (fun i => ((B i).lower e).comp (LinearMap.proj i))
  upper e := LinearMap.pi (fun i => ((B i).upper e).comp (LinearMap.proj i))

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Partial sheaf isomorphisms on upper sets, and their actual descending
extension. In particular the incoming edge component is induced by the upper
scalar quotient, not independently assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G)

def castStalkIso {x y : V} (h : x=y) (j : B.vertex x ≃ₗ[R] C.vertex x) :
    B.vertex y ≃ₗ[R] C.vertex y := h ▸ j

structure OnIso (U : Set V) where
  vertex : ∀ x, x ∈ U → B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, G.target e ∈ U → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    edge e ht (B.lower e v) = C.lower e (vertex (G.source e) hs v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    edge e ht (B.upper e v) = C.upper e (vertex (G.target e) ht v)

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

/-- Degree pieces of a shifted finite free module, as a genuine linear equivalence. -/
def shiftedPieceEquiv {ι : Type ui} (𝓐 : ℤ → Submodule k A) (d : ι → ℤ) (n : ℤ) :
    Graded.shiftedPiece 𝓐 d n ≃ₗ[k] (∀ i, 𝓐 (n-d i)) where
  toFun v i := ⟨v.val i, v.property i⟩
  invFun v := ⟨fun i => v i, fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance shiftedPiece_finite {ι : Type ui} [Finite ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.Finite k (Graded.shiftedPiece 𝓐 d n) :=
  Module.Finite.of_surjective (shiftedPieceEquiv 𝓐 d n).symm.toLinearMap
    (shiftedPieceEquiv 𝓐 d n).symm.surjective


end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def subPieceEquiv (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ) :
    subPiece 𝓜 S n ≃ₗ[k] piece 𝓜 (S.restrictScalars k) n where
  toFun v := ⟨⟨v.val.val,v.property⟩,v.val.property⟩
  invFun v := ⟨⟨v.val.val,v.property⟩,v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.Hilbert

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure OnIso (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V)
    extends Sheaf.OnIso B.forget C.forget U where
  vertex_graded : ∀ x (hx : x ∈ U) n v,
    v ∈ (B.vertex x).piece n → vertex x hx v ∈ (C.vertex x).piece n
  edge_graded : ∀ e (he : G.target e ∈ U) n v,
    v ∈ (B.edge e).piece n → edge e he v ∈ (C.edge e).piece n

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

 def zero : Sheaf.{u,v,w,z} (R := R) G where
  vertex _ := ModuleCat.of R PUnit.{z+1}
  edge _ := ModuleCat.of R PUnit.{z+1}
  lower _ := 0
  upper _ := 0

 def prod (B C : Sheaf.{u,v,w,z} (R := R) G) : Sheaf.{u,v,w,z} (R := R) G where
  vertex x := ModuleCat.of R (B.vertex x × C.vertex x)
  edge e := ModuleCat.of R (B.edge e × C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  {B C : Sheaf.{u,v,w,z} (R := R) G} (D : Sheaf.{u,v,w,z} (R := R) G)

noncomputable def OnIso.prodZero {U : Set V} (j : OnIso B C U)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  vertex x hx := by
    letI := hV x hx
    exact (j.vertex x hx).trans (addZeroRight _ _)
  edge e he := by
    letI := hE e he
    exact (j.edge e he).trans (addZeroRight _ _)
  lower e hs ht v := by
    apply Prod.ext
    · exact j.lower e hs ht v
    · exact (D.lower e).map_zero.symm
  upper e ht v := by
    apply Prod.ext
    · exact j.upper e ht v
    · exact (D.upper e).map_zero.symm

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Restriction of the honest reflection-twisted module to the fixed base field.
The automorphism fixes the base field, so no scalar information is discarded. -/
namespace KLInvariance.ReflectionPairTranslation.Twist
universe uk ur uy
variable {k : Type uk} [Field k] {R : Type ur} [CommRing R] [Algebra k R]
  (τ : R ≃ₐ[k] R) (Y : Type uy) [AddCommGroup Y] [Module R Y] [Module k Y]
  [IsScalarTower k R Y]

instance scalarModule : Module k (Twist τ.toRingEquiv Y) :=
  ({ equivVal τ.toRingEquiv Y with map_add' := fun _ _ => rfl } :
    Twist τ.toRingEquiv Y ≃+ Y).module k

instance scalarTower : IsScalarTower k R (Twist τ.toRingEquiv Y) where
  smul_assoc c r y := by
    apply Twist.ext
    change τ (c • r) • y.val=c • (τ r • y.val)
    rw [map_smul,smul_assoc]

def scalarEquiv : Twist τ.toRingEquiv Y ≃ₗ[k] Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.ReflectionPairTranslation.Twist

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Genuine word costalk character from the integral word pairing, transported
along the fixed symmetric-algebra coordinate isomorphism. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

local instance finiteEdges (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _

end
end KLInvariance.TitsSpace

end


section

/-! Genuine word stalk-to-costalk R-convolution, derived from the Hecke bar
and the constructed integral perfect word pairing. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance charDecEqB_r6af06b_1 (a : Type*) : DecidableEq a := Classical.decEq a
local instance rWordInterval (l : List I) : Fintype (Interval cs 1 (cs.wordProd l)) := by
  let := interval_finite cs 1 (cs.wordProd l)
  exact Fintype.ofFinite _

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem coordinate_sum (a : I → ℝ) : ∑ i, a i • root i = a := by
  ext j
  simp [root, Pi.single_apply, Finset.sum_apply]

theorem dual_coordinate_sum (h : Module.Dual ℝ (I → ℝ)) (a : I → ℝ) :
    h a = ∑ i, a i * h (root i) := by
  conv_lhs => rw [← coordinate_sum a]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem PositiveFunctional.root_pos {h : Module.Dual ℝ (I → ℝ)}
    (hh : PositiveFunctional h) (a : PositiveRoot M cs) : 0 < h a.val := by
  rw [dual_coordinate_sum]
  obtain ⟨i,hi⟩ : ∃ i, a.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact a.property.1.ne_zero (funext hn)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (a.property.2 j) (hh j).le)
    ⟨i,Finset.mem_univ _,mul_pos (lt_of_le_of_ne' (a.property.2 i) hi) (hh i)⟩

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem denominator_pos (a : PositiveRoot M cs) : 0 < O.denominator a.val :=
  O.positive.root_pos a

/-- The cut at zero is the genuine inversion set of the upper vertex. -/
def Adapted (y : W) : Prop := ∀ a : PositiveRoot M cs,
  (O.slope a < 0 ↔ rootInverted y a) ∧ O.slope a ≠ 0


/-- A functional in the chamber indexed by y has exactly Inv(y) as its
negative roots. This is stronger data used only to construct the order. -/
def Chamber (y : W) : Prop := ∀ i, 0 < O.numerator (action M cs y (root i))

end RatioOrder

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
def turnNumerator (i : I) : Module.Dual ℝ (I → ℝ) :=
  O.numerator.comp (action M cs (cs.simple i)).toLinearMap

def turnDenominator (i : I) (k : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (O.numerator - k • O.denominator).comp (action M cs (cs.simple i)).toLinearMap

end RatioOrder

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section


namespace KLInvariance.SignedDihedral
noncomputable section

 attribute [local instance] OAI.KLInvariance.SignedDihedral.instDecidable_solutions
noncomputable def arrowAfter (a label z : ℤ) : ℕ :=
  if |a| < |z| ∧ Odd (a+z) ∧ Before label (a+z) then 1 else 0

/-- Double internal ranks and the singleton top, with no singleton bottom
term because upward arrows never end at the bottom. -/
 noncomputable def countAfter (a label c : ℤ) : ℕ :=
  (∑ r ∈ Finset.range c.natAbs, (arrowAfter a label r + arrowAfter a label (-r))) +
    arrowAfter a label c

end
end KLInvariance.SignedDihedral

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/


section

/-! The relative rank-one structure models are natural under full strictly
order-compatible graph embeddings, with exactly the pulled-back labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} {W : Type uw} [PartialOrder W]
  {F : Type uf} {H : OrderedGraph W F}
noncomputable section

 theorem moduleEq_pi_apply {X : Type*} (p : X → Prop) {x y : X} (h : x=y)
    (v : PLift (p x) → R) (t : PLift (p y)) :
    moduleEq (congrArg (fun z => ModuleCat.of R (PLift (p z) → R)) h) v t =
      v ⟨h.symm ▸ t.down⟩ := by
  subst y
  rfl

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def shiftedImagePieceMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    subPiece 𝓜 S (n-d) →ₗ[k] subPiece 𝓝 (S.map f) n where
  toFun v := ⟨⟨f v.val.val,Submodule.mem_map.mpr ⟨_,v.val.property,rfl⟩⟩,
    by
      change f v.val.val ∈ 𝓝 n
      simpa using hf (n-d) v.val.val v.property⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' c v := by ext; exact (f.restrictScalars k).map_smul c v.val.val

 theorem shiftedImagePieceMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    Function.Surjective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) := by
  rintro ⟨⟨m,hm⟩,hgrad⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  refine ⟨⟨⟨component 𝓜 (n-d) v,hS (n-d) v hv⟩,
    (DirectSum.decompose 𝓜 v (n-d)).property⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (component 𝓜 (n-d) v) = f v
  rw [← map_component 𝓜 𝓝 f d hf n v]
  exact DirectSum.decompose_of_mem_same 𝓝 hgrad

noncomputable def shiftedImagePieceEquiv
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) (n : ℤ) :
    subPiece 𝓜 S (n-d) ≃ₗ[k] subPiece 𝓝 (S.map f) n :=
  LinearEquiv.ofBijective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) ⟨by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    apply hinj
    exact congrArg (fun z => z.val.val) h,
    shiftedImagePieceMap_surjective 𝓜 𝓝 S hS f d hf n⟩

end KLInvariance.Hilbert

end


end OAI
end


