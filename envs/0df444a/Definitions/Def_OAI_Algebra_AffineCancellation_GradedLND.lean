-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
-- name    : OAI_Algebra_AffineCancellation_GradedLND
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:59:25.849984+00:00
-- url     : https://prove2.me/theorems/d5a87d61-6f5d-4e90-9308-1dd9f643fbc8
-- title:
--   Homogeneous components of a derivation of a $\mathbb{Z}$-graded algebra
-- statement:
--   Let $k$ be a commutative ring and let $R$ be a commutative $k$-algebra with a $\mathbb{Z}$-grading $R=\bigoplus_{i\in\mathbb{Z}}R_i$ by $k$-submodules, with $1\in R_0$ and $R_iR_j\subseteq R_{i+j}$. For $r\in R$ let $\pi_i(r)\in R_i$ be its homogeneous component of degree $i$.
--
--   1. **Projections.** Each $\pi_i$ is a $k$-linear projection. If $r\in R_i$ and $s\in R$, then $\pi_{i+j}(rs)=r\,\pi_j(s)$ for every $j\in\mathbb{Z}$.
--
--   2. **Component of a linear map.** For a $k$-linear map $D:R\to R$ and $j\in\mathbb{Z}$, the degree-$j$ component $D_j$ is the $k$-linear map
--   $$D_j(r)=\sum_{i\in\mathbb{Z}}\pi_{i+j}\bigl(D(\pi_i(r))\bigr).$$
--   Thus $D_j(r)=\pi_{i+j}(D(r))$ for $r\in R_i$, and $D_j$ shifts degrees by exactly $j$.
--
--   3. **Component of a derivation.** If $D$ is a $k$-linear derivation, then $D_j$ satisfies the Leibniz rule $D_j(rs)=r\,D_j(s)+s\,D_j(r)$. So $D_j$ is again a derivation, the homogeneous component of $D$ of degree $j$.
--
--   4. **Filtration.** For $d\in\mathbb{Z}$, $R_{\le d}=\sum_{i\le d}R_i$ is the increasing filtration associated with the grading.
--
--   5. **Shift bound.** A derivation $D$ has shift bound $j$ if $D(R_i)\subseteq R_{\le i+j}$ for every $i\in\mathbb{Z}$, i.e. $D$ raises degrees by at most $j$. In that case $D_j$ is the top homogeneous part of $D$.
--
--   Passing from a derivation with bounded degree shift to its top homogeneous component is a standard device in the study of locally nilpotent derivations. It replaces $D$ by a homogeneous derivation that is easier to analyse. A separate result shows that the top component of a locally nilpotent derivation with shift bound $j$ is again locally nilpotent.
--
--   **Formalization Note** The grading is a `GradedAlgebra G` for `G : ℤ → Submodule k R`, and $\pi_i$ is `GradedAlgebra.proj G i`. `componentLinear` is built from the direct-sum decomposition, and `component G D j` is obtained from it with `Derivation.mk'`. The filtration is the supremum `⨆ i : {i : ℤ // i ≤ d}, G i`, and `ShiftBound G D j` is a proposition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/GradedLND.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/GradedLND.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

abbrev proj (i : ℤ) : R →ₗ[k] R := GradedAlgebra.proj G i

lemma proj_mul_left {r : R} {i : ℤ} (hr : r ∈ G i) (s : R) (j : ℤ) :
    proj G (i+j) (r*s) = r * proj G j s :=
  coe_decompose_mul_add_of_left_mem G hr

/-- The shift-j component of a linear map, on an arbitrary ℤ-graded algebra. -/
def componentLinear (D : R →ₗ[k] R) (j : ℤ) : R →ₗ[k] R :=
  (DirectSum.toModule k ℤ R (fun i =>
    ((proj G (i+j)).comp D).comp (G i).subtype)).comp
    (DirectSum.decomposeAlgEquiv G).toLinearMap

lemma componentLinear_of_mem (D : R →ₗ[k] R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : componentLinear G D j r = proj G (i+j) (D r) := by
  change DirectSum.toModule k ℤ R _ (decompose G r) = _
  rw [decompose_of_mem G hr]
  change DirectSum.toModule k ℤ R (fun t =>
    ((proj G (t+j)).comp D).comp (G t).subtype)
      (DirectSum.lof k ℤ (fun t => G t) i ⟨r, hr⟩) = _
  rw [DirectSum.toModule_lof]
  rfl

lemma componentLinear_leibniz (D : Derivation k R R) (j : ℤ) (r s : R) :
    componentLinear G D.toLinearMap j (r*s) =
      r * componentLinear G D.toLinearMap j s + s * componentLinear G D.toLinearMap j r := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp
  | @homogeneous i r =>
    induction s using DirectSum.Decomposition.inductionOn G with
    | zero => simp
    | @homogeneous h s =>
      rw [componentLinear_of_mem G D.toLinearMap j (SetLike.GradedMul.mul_mem r.2 s.2),
        componentLinear_of_mem G D.toLinearMap j s.2,
        componentLinear_of_mem G D.toLinearMap j r.2]
      simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add]
      rw [show i+h+j = i+(h+j) by omega, proj_mul_left G r.2]
      rw [show i+(h+j) = h+(i+j) by omega, proj_mul_left G s.2]
    | add s t hs ht => simp only [mul_add, map_add, hs, ht, add_mul]; abel
  | add r t hr ht => simp only [add_mul, map_add, hr, ht, mul_add]; abel

def component (D : Derivation k R R) (j : ℤ) : Derivation k R R :=
  Derivation.mk' (componentLinear G D.toLinearMap j) (by
    intro r s
    simpa only [smul_eq_mul] using componentLinear_leibniz G D j r s)

/-- The increasing filtration associated to an integer grading. -/
def filtration (d : ℤ) : Submodule k R := ⨆ i : {i : ℤ // i ≤ d}, G i

def ShiftBound (D : Derivation k R R) (j : ℤ) : Prop :=
  ∀ i r, r ∈ G i → D r ∈ filtration G (i+j)

end ComplexCancellation.GradedLND

end

end OAI


