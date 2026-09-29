-- Prove2me | Definitions.Def_Hairer_RegularityStructure
-- name    : Hairer_RegularityStructure
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:36:26.052595+00:00
-- url     : https://prove2.me/theorems/22abc435-1ec7-4dc3-bf3e-d4d5059bb6b6
-- title:
--   Regularity structures, sectors and products
-- statement:
--   The algebraic notions of the theory.
--
--   A **regularity structure** $(A,T,G)$ (Definition 2.1) consists of an index set
--   $A \subseteq \mathbb{R}$ containing $0$, bounded from below and locally finite; a graded model
--   space $T = \bigoplus_{\alpha \in A} T_\alpha$ whose degree-zero part is one-dimensional and
--   carries a unit $\mathbf{1}$; and a group $G$ of linear operators on $T$ such that
--   $\Gamma a - a \in \bigoplus_{\beta<\alpha} T_\beta$ for every $a \in T_\alpha$ and
--   $\Gamma \mathbf{1} = \mathbf{1}$.
--
--   Here the graded space is modelled by a family `E : A → Type` of real normed spaces indexed by
--   the index set, `ModelSpace A E` is the algebraic direct sum $\bigoplus_{a \in A} E_a$, `proj a`
--   is the projection $Q_a$ onto the homogeneous component of order $a$ and `incl a` the
--   corresponding inclusion. The structure group is a subgroup of the group of linear
--   automorphisms of the model space.
--
--   A **sector** of regularity $\alpha \le 0$ (Definition 2.5) is a graded subspace
--   $V = \bigoplus_\beta V_\beta$, $V_\beta \subseteq T_\beta$, which vanishes in degrees
--   $\beta<\alpha$ and is invariant under $G$; Hairer additionally asks that each $V_\beta$ admit
--   a complement in $T_\beta$, which is automatic in the algebraic setting used here.
--
--   A **product** on $T$ (Definition 4.1) is a continuous bilinear map $\star$ sending
--   $T_\alpha \times T_\beta$ into $T_{\alpha+\beta}$ and for which $\mathbf{1}$ is a two-sided
--   unit; continuity is expressed as a bound
--   $\|Q_c(a \star b)\| \le C\|a\|\,\|b\|$ for each pair of homogeneities. A pair of sectors
--   $(V,W)$ is **$\gamma$-regular** (Definition 4.6) if $\Gamma(a \star b) = (\Gamma a)\star(\Gamma b)$
--   for all $\Gamma \in G$, $a \in V_\alpha$, $b \in W_\beta$ with $\alpha+\beta<\gamma$.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Definition 2.1 (p. 18), Definition 2.5 (p. 19), Definition 4.1 and Definition 4.6 (pp. 48-49)

import Definitions.Def_Hairer_TestFunctions

/-!
# Regularity structures, sectors and products

Formalisation of the algebraic notions of

  M. Hairer, *A theory of regularity structures*, Invent. Math. 198 (2014) 269–504,
  arXiv:1303.5113:

Definition 2.1 (regularity structure), Definition 2.5 (sector), Definition 4.1
(product on `T`) and Definition 4.6 (`γ`-regular pair of sectors).

The graded model space `T = ⨁_{α ∈ A} T_α` is modelled by a family `E : A → Type` of
normed real vector spaces indexed by the index set `A ⊆ ℝ`, and `T` itself is the
algebraic direct sum `⨁ a, E a`.
-/

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

variable {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
  [∀ a : A, NormedSpace ℝ (E a)]

/-- The model space `T = ⨁_{α ∈ A} T_α` of a regularity structure. -/
abbrev ModelSpace (A : Set ℝ) (E : A → Type) [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)] : Type := ⨁ a : A, E a

/-- The projection `Q_a : T → T_a` onto the homogeneous component of order `a`. -/
abbrev proj (a : A) : ModelSpace A E →ₗ[ℝ] E a := DirectSum.component ℝ A E a

/-- The inclusion `T_a → T` of a homogeneous component into the model space. -/
abbrev incl (a : A) : E a →ₗ[ℝ] ModelSpace A E := DirectSum.lof ℝ A E a

/-- **Definition 2.1 (Hairer).** `(A, T, G)` is a regularity structure:
`A ⊆ ℝ` contains `0`, is bounded below and locally finite; the model space
`T = ⨁_{α ∈ A} T_α` is graded with `T_0` one-dimensional, spanned by the unit `1`;
and `G` is a group of linear operators on `T` such that `Γa - a` has components only
in degrees `β < α` for `a ∈ T_α`, and `Γ1 = 1`. -/
structure IsRegularityStructure (A : Set ℝ) (E : A → Type)
    [∀ a : A, NormedAddCommGroup (E a)] [∀ a : A, NormedSpace ℝ (E a)]
    (G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)) (one : ModelSpace A E) : Prop where
  /-- `0 ∈ A`. -/
  zero_mem : (0 : ℝ) ∈ A
  /-- `A` is bounded from below. -/
  bddBelow : BddBelow A
  /-- `A` is locally finite. -/
  locallyFinite : ∀ r : ℝ, {a : ℝ | a ∈ A ∧ a ≤ r}.Finite
  /-- `T_0 ≈ ℝ`. -/
  rank_zero : ∀ a : A, (a : ℝ) = 0 → Module.finrank ℝ (E a) = 1
  /-- The unit is a nonzero element of `T_0`. -/
  one_ne_zero : one ≠ 0
  /-- The unit is homogeneous of order `0`. -/
  one_homogeneous : ∀ a : A, (a : ℝ) ≠ 0 → proj a one = 0
  /-- For `a ∈ T_α` and `Γ ∈ G`, the element `Γa - a` lies in `⨁_{β < α} T_β`. -/
  triangular : ∀ Γ ∈ G, ∀ (a b : A) (τ : E a), (a : ℝ) ≤ (b : ℝ) →
      proj b (Γ (incl a τ) - incl a τ) = 0
  /-- `Γ1 = 1` for every `Γ ∈ G`. -/
  one_invariant : ∀ Γ ∈ G, Γ one = one

/-- The subspace `V = ⨁_{β ∈ A} V_β ⊆ T` determined by a family of subspaces
`V_β ⊆ T_β`. -/
def sectorSpace (V : ∀ a : A, Submodule ℝ (E a)) : Submodule ℝ (ModelSpace A E) where
  carrier := {τ | ∀ a : A, proj a τ ∈ V a}
  add_mem' := by intro σ τ hσ hτ a; simpa using add_mem (hσ a) (hτ a)
  zero_mem' := by intro a; simp
  smul_mem' := by intro c τ hτ a; simpa using Submodule.smul_mem _ c (hτ a)

/-- **Definition 2.5 (Hairer).** A *sector* of regularity `α ≤ 0` is a graded subspace
`V = ⨁_β V_β` with `V_β ⊆ T_β` which vanishes in degrees `β < α` and is invariant
under the structure group `G`.

(Hairer additionally requires each `V_β` to admit a complement in `T_β`; over a field
this is automatic in the algebraic setting used here.) -/
structure IsSector (G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E))
    (V : ∀ a : A, Submodule ℝ (E a)) (α : ℝ) : Prop where
  /-- The regularity of a sector is non-positive. -/
  reg_nonpos : α ≤ 0
  /-- `V_β = 0` for `β < α`. -/
  vanishing : ∀ a : A, (a : ℝ) < α → V a = ⊥
  /-- `V` is invariant under the structure group. -/
  invariant : ∀ Γ ∈ G, ∀ τ ∈ sectorSpace V, Γ τ ∈ sectorSpace V

/-- **Definition 4.1 (Hairer).** A *product* on `T` is a continuous bilinear map
`⋆` which maps `T_α × T_β` into `T_{α+β}` and for which `1` is a two-sided unit. -/
structure IsProduct (one : ModelSpace A E)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E) : Prop where
  /-- `a ⋆ b ∈ T_{α+β}` for `a ∈ T_α`, `b ∈ T_β`. -/
  graded : ∀ (a b c : A) (σ : E a) (τ : E b), (c : ℝ) ≠ (a : ℝ) + (b : ℝ) →
      proj c (star (incl a σ) (incl b τ)) = 0
  /-- `1 ⋆ a = a`. -/
  one_left : ∀ τ : ModelSpace A E, star one τ = τ
  /-- `a ⋆ 1 = a`. -/
  one_right : ∀ τ : ModelSpace A E, star τ one = τ
  /-- Continuity of `⋆ : T_α × T_β → T_{α+β}`. -/
  bounded : ∀ a b : A, ∃ C : ℝ, ∀ (σ : E a) (τ : E b) (c : A),
      ‖proj c (star (incl a σ) (incl b τ))‖ ≤ C * ‖σ‖ * ‖τ‖

/-- **Definition 4.6 (Hairer).** The pair of sectors `(V, W)` is `γ`-regular for the
product `⋆` if `Γ(a ⋆ b) = (Γa) ⋆ (Γb)` for all `Γ ∈ G`, `a ∈ V_α`, `b ∈ W_β` with
`α + β < γ`. -/
def IsGammaRegular (G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E))
    (V W : ∀ a : A, Submodule ℝ (E a))
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E) (γ : ℝ) : Prop :=
  ∀ Γ ∈ G, ∀ a b : A, (a : ℝ) + (b : ℝ) < γ → ∀ σ ∈ V a, ∀ τ ∈ W b,
    Γ (star (incl a σ) (incl b τ)) = star (Γ (incl a σ)) (Γ (incl b τ))

end Hairer


