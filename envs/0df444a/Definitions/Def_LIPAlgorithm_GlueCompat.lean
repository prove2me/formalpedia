-- Prove2me | Definitions.Def_LIPAlgorithm_GlueCompat
-- name    : LIPAlgorithm_GlueCompat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:38.277202+00:00
-- url     : https://prove2.me/theorems/514a524e-44a5-454f-9a53-cd42ea9a2267
-- title:
--   Section, quotient, discriminant group and glue compatibility
-- statement:
--   For a lattice $L$, set $V=\mathrm{span}(\mathrm{Min}(L))$, the section $A=L\cap V$, the projected quotient $Q=\pi_{V^\perp}(L)$, the dual $A^*=\{y\in V:\langle y,a\rangle\in\mathbb Z\ \forall a\in A\}$ and the discriminant group $D(A)=A^*/A$.
--
--   For isometries $O_A:V_1\to V_2$ and $O_Q:V_1^\perp\to V_2^\perp$, **glue compatibility** says $O_A\circ\tau_{L_1}=\tau_{L_2}\circ O_Q$, with $\tau_L(q)=\pi_V(x)+A$ for any lift $x\in L$ of $q$. In terms of lifts: whenever $x_1\in L_1$, $x_2\in L_2$ and $O_Q\pi_{V_1^\perp}x_1=\pi_{V_2^\perp}x_2$, one has
--
--   $$O_A(\pi_{V_1}x_1)-\pi_{V_2}x_2\in A_2.$$
--
--   This is the condition under which isometries of the pieces assemble to an isometry of the lattices.
--
--   **Formalization Note** $A$ and $Q$ are subgroups of $\mathbb R^n$ that are not of full rank, so an isometry between them is an isometry of the ambient subspaces carrying one onto the other.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 2.9, pp.11–12; §2.1, p.9

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_LIPAlgorithm_minShell

namespace LIPAlgorithm

/-- `V = span(Min(L))` (Lemma 2.9, p.11). -/
def spanMin {n : ℕ} (L : Submodule ℤ (E n)) : Submodule ℝ (E n) :=
  Submodule.span ℝ (minShell L)

/-- The section `A = L ∩ V` (Lemma 2.9, p.11). -/
def secA {n : ℕ} (L : Submodule ℤ (E n)) : Submodule ℤ (E n) :=
  L ⊓ (spanMin L).restrictScalars ℤ

/-- The projected quotient `Q = π_{V⊥}(L)` (Lemma 2.9, p.11), as a subgroup of `ℝⁿ`. -/
noncomputable def quotQ {n : ℕ} (L : Submodule ℤ (E n)) : Submodule ℤ (E n) :=
  L.map (((spanMin L)ᗮ.starProjection : E n →ₗ[ℝ] E n).restrictScalars ℤ)

/-- The dual `A* = {y ∈ span(A) : ⟨y, a⟩ ∈ ℤ for all a ∈ A}` (§2.1, p.9) of the section.
Since `span(A) = V`, this is the published full-space dual cut down to `V`. -/
noncomputable def secDual {n : ℕ} (L : Submodule ℤ (E n)) : Submodule ℤ (E n) :=
  RegevLWE.GaussConv.dual (secA L) ⊓ (spanMin L).restrictScalars ℤ

/-- The discriminant group `D(A) = A*/A` (§2.1, p.9), of the section `A` of `L`. -/
abbrev discr {n : ℕ} (L : Submodule ℤ (E n)) :=
  ↥(secDual L) ⧸ (secA L).submoduleOf (secDual L)

/-- An isometry between two subspaces of `ℝⁿ` carries the lattice `A₁` onto the lattice `A₂`: this is
`O ∈ Iso(A₁, A₂)` for lattices that are not of full rank (Lemma 2.9(ii), p.12). -/
def MapsOnto {n : ℕ} {S₁ S₂ : Submodule ℝ (E n)} (O : S₁ ≃ₗᵢ[ℝ] S₂) (A₁ A₂ : Submodule ℤ (E n)) :
    Prop :=
  (fun x : S₁ => ((O x : S₂) : E n)) '' {x : S₁ | (x : E n) ∈ A₁} = (A₂ : Set (E n))

/-- The glue compatibility `O_A ∘ τ_{L₁} = τ_{L₂} ∘ O_Q` of Lemma 2.9(ii), p.12, written by lifts: for
`q ∈ Q₁` with a lift `x₁ ∈ L₁`, and a lift `x₂ ∈ L₂` of `O_Q q`, the elements `O_A(π_{V₁} x₁)` and
`π_{V₂} x₂` of `A₂*` agree modulo `A₂`.

**Formalization Note.** Since `τ_L(q) = π_V(x) + A` for any lift `x` (Lemma 2.9(i)), this is the printed
equation evaluated on representatives. `O_Q` carries `Q₁` onto `Q₂`, so a lift `x₂` exists for every `q`. -/
def GlueCompat {n : ℕ} (L₁ L₂ : Submodule ℤ (E n))
    (OA : spanMin L₁ ≃ₗᵢ[ℝ] spanMin L₂) (OQ : ↥(spanMin L₁)ᗮ ≃ₗᵢ[ℝ] ↥(spanMin L₂)ᗮ) : Prop :=
  ∀ x₁ ∈ L₁, ∀ x₂ ∈ L₂,
    (OQ ((spanMin L₁)ᗮ.orthogonalProjectionOnto x₁) : E n) = (spanMin L₂)ᗮ.starProjection x₂ →
      ((OA ((spanMin L₁).orthogonalProjectionOnto x₁) : spanMin L₂) : E n) -
        (spanMin L₂).starProjection x₂ ∈ secA L₂

end LIPAlgorithm


