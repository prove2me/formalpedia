-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
-- name    : OAI_Algebra_AffineCancellation_QuotientGrading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:00:52.418693+00:00
-- url     : https://prove2.me/theorems/ccddf383-b64e-41c5-8a8b-d0dee8cc380a
-- title:
--   Induced grading on a quotient of a graded algebra by a homogeneous kernel
-- statement:
--   Let $k$ be a commutative ring and let $\iota$ be an additive commutative monoid. Let $R$ be a commutative $k$-algebra graded by $\iota$, that is $R=\bigoplus_{i\in\iota}G_i$ with $k$-submodules $G_i$, $1\in G_0$ and $G_iG_j\subseteq G_{i+j}$, and write $r_i$ for the degree-$i$ component of $r\in R$. Let $Q$ be a commutative $k$-algebra and $q:R\to Q$ a $k$-algebra homomorphism.
--
--   1. **Image pieces.** $Q_i=q(G_i)$ is a $k$-submodule of $Q$, and $q$ restricts to $k$-linear maps $G_i\to Q_i$.
--
--   2. **Decomposition through $R$.** The $k$-linear map $R\to\bigoplus_{i\in\iota}Q_i$, $r\mapsto(q(r_i))_{i}$, followed by summation $\bigoplus_iQ_i\to Q$, equals $q$. Suppose the kernel of $q$ is a homogeneous ideal, i.e. it contains every homogeneous component of each of its elements. Then $q(a)=q(b)$ implies $(q(a_i))_i=(q(b_i))_i$.
--
--   3. **Decomposition of $Q$.** If $q$ is surjective and $\ker q$ is homogeneous, there is a well-defined $k$-linear map
--   $$Q\longrightarrow\bigoplus_{i\in\iota}Q_i,\qquad q(r)\longmapsto\bigl(q(r_i)\bigr)_{i\in\iota},$$
--   which does not depend on the chosen preimage. It sends an element of $Q_i$ to the same element in the $i$-th summand, and it is inverse to summation, so $Q=\bigoplus_{i}Q_i$ as $k$-modules.
--
--   4. **Induced grading.** Under the same hypotheses, $Q=\bigoplus_{i\in\iota}Q_i$ is a graded $k$-algebra: $1\in Q_0$ and $Q_iQ_j\subseteq Q_{i+j}$.
--
--   This is the familiar fact that a quotient of a graded algebra by a homogeneous ideal inherits a grading whose pieces are the images of the original ones. For example, a weighted grading of a polynomial ring descends to the quotient by a weighted-homogeneous equation.
--
--   **Formalization Note** $\iota$ also carries decidable equality, as Mathlib's direct sums require. The hypotheses are `hq : Function.Surjective q` and `hK : (RingHom.ker q).IsHomogeneous G`. The pieces are `pieces G q i = (G i).map q`, and `decomposition` and `grading` are definitions marked `@[instance_reducible]` rather than global instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/QuotientGrading.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/QuotientGrading.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND

namespace OAI

noncomputable section

namespace ComplexCancellation.QuotientGrading
open DirectSum
variable {k R Q ι : Type*} [CommRing k] [CommRing R] [CommRing Q]
  [Algebra k R] [Algebra k Q] [AddCommMonoid ι] [DecidableEq ι]
  (G : ι → Submodule k R) [GradedAlgebra G]
  (q : R →ₐ[k] Q)

def pieces (i : ι) : Submodule k Q := (G i).map q.toLinearMap

def componentMap (i : ι) : G i →ₗ[k] pieces G q i :=
  (q.toLinearMap.comp (G i).subtype).codRestrict _ (fun r => ⟨r, r.2, rfl⟩)

def sourceDecompose : R →ₗ[k] ⨁ i, pieces G q i :=
  (DirectSum.lmap (componentMap G q)).comp (decomposeLinearEquiv G).toLinearMap

lemma sourceDecompose_eq (hK : (RingHom.ker q).IsHomogeneous G)
    {a b : R} (hab : q a = q b) : sourceDecompose G q a = sourceDecompose G q b := by
  ext i
  have hz : q (a-b) = 0 := by rw [map_sub, hab, sub_self]
  have hh := (hK.mem_iff.mp hz) i
  change q (decompose G (a-b) i) = 0 at hh
  rw [decompose_sub] at hh
  change q (decompose G a i) = q (decompose G b i)
  simpa only [DirectSum.sub_apply, Submodule.coe_sub, map_sub, sub_eq_zero] using hh

def decomposeMap (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : Q →ₗ[k] ⨁ i, pieces G q i where
  toFun r := sourceDecompose G q (Classical.choose (hq r))
  map_add' r s := by
    rw [← map_add]
    apply sourceDecompose_eq G q hK
    simp only [map_add, Classical.choose_spec (hq _)]
  map_smul' a r := by
    change sourceDecompose G q (Classical.choose (hq (a • r))) =
      a • sourceDecompose G q (Classical.choose (hq r))
    rw [← map_smul]
    apply sourceDecompose_eq G q hK
    simp only [map_smul, Classical.choose_spec (hq _)]

@[simp] lemma decomposeMap_q (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) (r : R) :
    decomposeMap G q hq hK (q r) = sourceDecompose G q r :=
  sourceDecompose_eq G q hK (Classical.choose_spec (hq (q r)))

lemma coe_sourceDecompose (r : R) :
    coeLinearMap (pieces G q) (sourceDecompose G q r) = q r := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp
  | @homogeneous i r =>
    change coeLinearMap (pieces G q) (DirectSum.lmap (componentMap G q)
      (decompose G (r : R))) = _
    rw [decompose_coe, DirectSum.lmap_of]
    change coeLinearMap (pieces G q)
      (DirectSum.lof k ι (fun i => pieces G q i) i (componentMap G q i r)) = _
    rw [coeLinearMap_lof]
    rfl
  | add r s hr hs => simp [hr, hs]

lemma decomposeMap_homogeneous (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) (i : ι) (r : pieces G q i) :
    decomposeMap G q hq hK r = DirectSum.lof k ι (fun i => pieces G q i) i r := by
  obtain ⟨s, hs, hsr⟩ := r.2
  have he : (r : Q) = q s := hsr.symm
  rw [he, decomposeMap_q]
  change DirectSum.lmap (componentMap G q) (decompose G s) = _
  rw [decompose_of_mem G hs, DirectSum.lmap_of]
  apply congrArg (DirectSum.of (fun i => pieces G q i) i)
  exact Subtype.ext hsr

@[instance_reducible] def decomposition (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : Decomposition (pieces G q) :=
  Decomposition.ofLinearMap (pieces G q) (decomposeMap G q hq hK)
    (by
      ext r
      obtain ⟨s, rfl⟩ := hq r
      exact (congrArg (coeLinearMap (pieces G q)) (decomposeMap_q G q hq hK s)).trans
        (coe_sourceDecompose G q s))
    (by
      apply DirectSum.linearMap_ext k
      intro i
      apply LinearMap.ext
      intro r
      change decomposeMap G q hq hK
        (coeLinearMap (pieces G q) (DirectSum.lof k ι (fun i => pieces G q i) i r)) = _
      rw [coeLinearMap_lof]
      exact decomposeMap_homogeneous G q hq hK i r)

@[instance_reducible] def grading (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : GradedAlgebra (pieces G q) where
  toDecomposition := decomposition G q hq hK
  one_mem := ⟨1, SetLike.one_mem_graded G, map_one q⟩
  mul_mem := by
    intro i j r s hr hs
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨b, hb, rfl⟩ := hs
    exact ⟨a*b, SetLike.mul_mem_graded ha hb, map_mul q a b⟩

end ComplexCancellation.QuotientGrading

end

end OAI


