-- Prove2me | Definitions.Def_LIPAlgorithm_LabelEq
-- name    : LIPAlgorithm_LabelEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:24.453379+00:00
-- url     : https://prove2.me/theorems/1fd0ace3-6f1b-4c29-aecf-cedb265c25c1
-- title:
--   Equality of the exact marker labels
-- statement:
--   For a well-rounded lattice $L$ and a marker $w$, let $U(w)=\mathrm{span}\{u_j(w):j\in J(w)\}$, $C=L\cap U(w)$, $R=L\cap U(w)^\perp$, and let $w_R$ be the component of $w$ in $U(w)^\perp$. Two pairs $(L_1,w_1)$, $(L_2,w_2)$ have **equal labels** if the following agree: the scale of the lattice; the ordered set $J(w)$; the Gram matrix of the $u_j(w)$; the module $T_C=X_w^{-1}(C)$ in the coordinates of the $u_j(w)$; the scores $\langle w,u_j(w)\rangle$. In addition, there must be an isometry $O_R:U(w_1)^\perp\to U(w_2)^\perp$ with $O_R(R_1)=R_2$, $O_R(w_{1,R})=w_{2,R}$ and
--
--   $$(O_U\oplus O_R)(L_1)=L_2,$$
--
--   where $O_U$ is the map $u_{1,j}\mapsto u_{2,j}$. A marker is **resolving** if $n-|J(w)|\le\lceil 2n/\log n\rceil$.
--
--   Equal labels are the collision event of the birthday algorithm.
--
--   **Formalization Note** The label is a predicate: by Theorem 5.14 and its "Target primitive", two canonical strings of residual-glue instances agree exactly when these conditions hold. The serialization of the instance attached to $(L,w)$ is not written out.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §6.1, p.31; Definition 6.3, p.32; p.25; Lemma 6.4, p.32

import Mathlib
import Definitions.Def_LIPAlgorithm_Resolved

namespace LIPAlgorithm

/-- The fixed subspace `U(w) = span{u_j(w) : j ∈ J(w)}` (§6.1, p.31). -/
noncomputable def fixedSpan {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Submodule ℝ (E n) :=
  Submodule.span ℝ ((fun j => fixedVec L j w) '' (fixedSteps L w : Set ℕ))

/-- The fixed lattice `C(L, w) = L ∩ U(w)` (§6.1, p.31). -/
noncomputable def fixedLat {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Submodule ℤ (E n) :=
  L ⊓ (fixedSpan L w).restrictScalars ℤ

/-- The residual lattice `R(L, w) = L ∩ U(w)⊥` (§6.1, p.31). -/
noncomputable def resLat {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Submodule ℤ (E n) :=
  L ⊓ (fixedSpan L w)ᗮ.restrictScalars ℤ

/-- The residual marker `w_R`, the component of `w` in `U(w)⊥` (§6.1, p.31). -/
noncomputable def resMarker {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : ↥(fixedSpan L w)ᗮ :=
  (fixedSpan L w)ᗮ.orthogonalProjectionOnto w

/-- The pairing group `a(L) = ⟨⟨x, y⟩ : x, y ∈ L⟩_Z = α(L)·Z` (§2.1, p.9). Equal groups are equal scales `α`. -/
def scaleGroup {n : ℕ} (L : Submodule ℤ (E n)) : AddSubgroup ℝ :=
  AddSubgroup.closure {a | ∃ x ∈ L, ∃ y ∈ L, a = inner ℝ x y}

/-- The rational module `T_C(L, w) = X_w⁻¹ C(L, w)` (§6.1, p.31), where `X_w e_j = u_j(w)`.

**Formalization Note.** A coordinate vector is a function on `ℕ` that vanishes off `J(w)`, so two such modules
can be compared when `J(w)` agree, as in the first item of the fixed data. -/
noncomputable def coordModule {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Set (ℕ → ℝ) :=
  {c | (∀ j, j ∉ fixedSteps L w → c j = 0) ∧
    ∑ j ∈ fixedSteps L w, c j • fixedVec L j w ∈ fixedLat L w}

/-- The residual isometries of Theorem 6.5(b), p.32: `O_R : U(w₁)⊥ → U(w₂)⊥` with `O_R(R₁) = R₂`,
`O_R(w₁,R) = w₂,R` and `(O_U ⊕ O_R)(L₁) = L₂`, where `O_U` is the map `u_{1,j} ↦ u_{2,j}` of Lemma 6.4, p.32.

**Formalization Note.** The last clause spells out `O_U ⊕ O_R` on the decomposition `x = ∑_j c_j u_{1,j} + y`,
so that the definition does not construct `O_U`. It is the glued-lattice form of the glue condition (5.1), p.29. -/
def residualWitness {n : ℕ} (L₁ : Submodule ℤ (E n)) (w₁ : E n) (L₂ : Submodule ℤ (E n)) (w₂ : E n) :
    Set (↥(fixedSpan L₁ w₁)ᗮ ≃ₗᵢ[ℝ] ↥(fixedSpan L₂ w₂)ᗮ) :=
  {OR | (∀ y : ↥(fixedSpan L₁ w₁)ᗮ, (y : E n) ∈ resLat L₁ w₁ ↔ ((OR y : ↥(fixedSpan L₂ w₂)ᗮ) : E n) ∈ resLat L₂ w₂) ∧
    OR (resMarker L₁ w₁) = resMarker L₂ w₂ ∧
    ∀ (c : ℕ → ℝ) (y : ↥(fixedSpan L₁ w₁)ᗮ),
      (∑ j ∈ fixedSteps L₁ w₁, c j • fixedVec L₁ j w₁) + (y : E n) ∈ L₁ ↔
        (∑ j ∈ fixedSteps L₁ w₁, c j • fixedVec L₂ j w₂) + ((OR y : ↥(fixedSpan L₂ w₂)ᗮ) : E n) ∈ L₂}

/-- Equality of the exact marker labels `Lab(L₁, w₁) = Lab(L₂, w₂)` (Definition 6.3, p.32), as a predicate.
By Theorem 5.14 and its "Target primitive" (p.25), the canonical strings agree exactly when the scales and the fixed
data agree and there is a residual isometry preserving the residual marker and the glue. The fixed data are the four
items of p.31: the ordered set `J(w)`, the Gram matrix of the `u_j(w)`, the module `T_C(L, w)` and the marker scores
`⟨w, u_j(w)⟩`.

**Formalization Note.** The serialization of `G(L, w)` is not spelled out: `Can` is existential in `theorem_5_14`.
Equal normal forms `NF_mod` are equal modules (Definition 5.4, p.26), so `T_C` is compared directly. -/
def LabelEq {n : ℕ} (L₁ : Submodule ℤ (E n)) (w₁ : E n) (L₂ : Submodule ℤ (E n)) (w₂ : E n) : Prop :=
  scaleGroup L₁ = scaleGroup L₂ ∧
    fixedSteps L₁ w₁ = fixedSteps L₂ w₂ ∧
    (∀ a ∈ fixedSteps L₁ w₁, ∀ b ∈ fixedSteps L₁ w₁,
      inner ℝ (fixedVec L₁ a w₁) (fixedVec L₁ b w₁) = inner ℝ (fixedVec L₂ a w₂) (fixedVec L₂ b w₂)) ∧
    coordModule L₁ w₁ = coordModule L₂ w₂ ∧
    (∀ j ∈ fixedSteps L₁ w₁, inner ℝ w₁ (fixedVec L₁ j w₁) = inner ℝ w₂ (fixedVec L₂ j w₂)) ∧
    (residualWitness L₁ w₁ L₂ w₂).Nonempty

/-- "Call a marker w resolving if its residual rank is at most r∗(n) := ⌈2n/log n⌉" (p.25); the residual rank is
`n − |J(w)|` (Lemma 6.6, p.33). The base of the logarithm is `2`, as in `scaleS`. -/
noncomputable def IsResolving {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Prop :=
  n - (fixedSteps L w).card ≤ ⌈2 * (n : ℝ) / Real.logb 2 n⌉₊

end LIPAlgorithm


