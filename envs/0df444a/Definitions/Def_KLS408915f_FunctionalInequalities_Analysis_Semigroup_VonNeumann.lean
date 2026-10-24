-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:12:19.729341+00:00
-- url     : https://prove2.me/theorems/0e11bdcc-7b35-4b95-84de-21d852064870
-- title:
--   Self-adjointness and resolvent identities for the adjoint product
-- statement:
--   For a closed densely defined real-linear operator $T:H_0\to H_1$, `inner_adjointComp` identifies the form of $T^\dagger T$ with $\langle Tx,Ty\rangle$, and `inner_adjointComp_self` identifies its quadratic form with $\|Tx\|^2$. The bundle proves density of $D(T^\dagger T)$ and self-adjointness of `adjointComp T` via `dense_adjointComp_domain` and `isSelfAdjoint_adjointComp`. For the resolvent $J_s$, it proves membership in $D(T^\dagger T)$, the identity $T^\dagger T(J_sf)=s^{-1}(f-J_sf)$, surjectivity of $1+T^\dagger T$, and the defect formula `sub_resolvent_eq_smul` on $D(T^\dagger T)$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean#L70-L392 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.VonNeumann`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- the form identity: `T†T` acts through the form.

For `x ∈ D(T†T)` and `y ∈ D(T)` one has `⟪T†T x, y⟫ = ⟪T x, T y⟫`.  This is
`LinearPMap.adjoint_isFormalAdjoint` read through `adjointComp_apply`; density of `D(T)` is
needed because Mathlib's adjoint is a junk value otherwise.  Neither `T.IsClosed` nor
completeness of `H₁` is used.  The membership of `y` is taken as a hypothesis rather than
packaged into a subtype, so that the lemma rewrites against goals mentioning a bare `y : H₀`. -/
theorem inner_adjointComp {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    (x : (adjointComp T).domain) {y : H₀} (hy : y ∈ T.domain) :
    ⟪adjointComp T x, y⟫ = ⟪T ⟨(x : H₀), x.2.2⟩, T ⟨y, hy⟩⟫ := by
  rw [adjointComp_apply]
  exact LinearPMap.adjoint_isFormalAdjoint hd _ ⟨y, hy⟩
/-- The Dirichlet form of `T†T`: for `x ∈ D(T†T)`, `⟪T†T x, x⟫ = ‖T x‖ ^ 2`.

the form identity with `y = x`, which is legitimate because `D(T†T) ⊆ D(T)`.  This is the form that the
semigroup contracts; `FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq` is its
specialization to the closed weighted gradient.  Neither `T.IsClosed` nor completeness of `H₁`
is used. -/
theorem inner_adjointComp_self {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀))
    (x : (adjointComp T).domain) :
    ⟪adjointComp T x, (x : H₀)⟫ = ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by
  rw [inner_adjointComp hd x x.2.2, real_inner_self_eq_norm_sq]
/-- `T†T` is symmetric: it is a formal adjoint of itself.

Both sides of `⟪T†T x, y⟫ = ⟪x, T†T y⟫` equal `⟪T x, T y⟫` by the form identity, the right-hand one after a
real inner-product flip.  This is the input that `LinearPMap.IsFormalAdjoint.le_adjoint` turns
into `T†T ≤ (T†T)†` once `D(T†T)` is known to be dense. -/
theorem adjointComp_isFormalAdjoint {T : H₀ →ₗ.[ℝ] H₁} (hd : Dense (T.domain : Set H₀)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  rw [inner_adjointComp hd x y.2.2, ← real_inner_comm ((x : H₀)) (adjointComp T y),
    inner_adjointComp hd y x.2.2]
  exact real_inner_comm _ _
section Resolvent
variable [CompleteSpace H₁]
/-- the resolvent domain identity, domain half: the weak solution `J_s f` lies in `D(T†T)`.

From the weak equation `⟪u, v⟫ + s ⟪T u, T v⟫ = ⟪f, v⟫` the vector `T u` pairs continuously
against `T v`, with representative `w = s⁻¹ (f - u)`, so `T u ∈ D(T†)` by
`LinearPMap.mem_adjoint_domain_of_exists`.  **Density of `D(T)` is not needed for this half**
(see the module docstring). -/
theorem mem_adjointComp_domain_resolventDomain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    {s : ℝ} (hs : 0 < s) (f : H₀) :
    ((resolventDomain T hT hs f : H₀)) ∈ (adjointComp T).domain := by
  set u := resolventDomain T hT hs f with hu
  refine ⟨mem_adjointCompDomain.mpr ⟨u.2, ?_⟩, u.2⟩
  have hue : (⟨(u : H₀), u.2⟩ : T.domain) = u := rfl
  rw [hue]
  refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨s⁻¹ • (f - (u : H₀)), ?_⟩
  intro v
  have h := resolventDomain_spec T hT hs f v
  rw [← hu] at h
  rw [real_inner_smul_left, inner_sub_left]
  field_simp
  linarith
/-- the resolvent domain identity, value half: `T† (T (J_s f)) = s⁻¹ (f - J_s f)`.

The same representative `w = s⁻¹ (f - u)` that witnesses membership in `D(T†)` is the value of
the adjoint, by `LinearPMap.adjoint_apply_eq`; this step does use density of `D(T)`.  The
membership proof is taken as an argument so that the statement does not depend on how it was
produced. -/
theorem adjointComp_resolventDomain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : H₀)
    (hmem : ((resolventDomain T hT hs f : H₀)) ∈ (adjointComp T).domain) :
    adjointComp T ⟨(resolventDomain T hT hs f : H₀), hmem⟩
      = s⁻¹ • (f - (resolventDomain T hT hs f : H₀)) := by
  set u := resolventDomain T hT hs f with hu
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq hd _ ?_
  intro v
  have h := resolventDomain_spec T hT hs f v
  rw [← hu] at h
  show ⟪s⁻¹ • (f - (u : H₀)), (v : H₀)⟫ = ⟪T u, T v⟫
  rw [real_inner_smul_left, inner_sub_left]
  field_simp
  linarith
/-- `1 + T†T` is surjective: every `z : H₀` is `x + T†T x` for some `x ∈ D(T†T)`.

This is the resolvent domain identity at `s = 1`, and it is the only consequence of the resolvent domain identity used in the proofs of self-adjointness of T†T and
density of D(T†T). -/
theorem exists_add_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (z : H₀) :
    ∃ x : (adjointComp T).domain, (x : H₀) + adjointComp T x = z := by
  have h1 : (0 : ℝ) < 1 := zero_lt_one
  refine ⟨⟨(resolventDomain T hT h1 z : H₀),
    mem_adjointComp_domain_resolventDomain T hT h1 z⟩, ?_⟩
  rw [adjointComp_resolventDomain T hT hd h1 z]
  rw [inv_one, one_smul]
  abel
/-- density of D(T†T): `D(T†T)` is dense.

Proved directly, not from self-adjointness of T†T (see the module docstring for why the route's order is not
available).  If `g` is orthogonal to `D(T†T)`, write `g = x + T†T x` with `x ∈ D(T†T)` by
surjectivity of `1 + T†T`; then `0 = ⟪x, g⟫ = ‖x‖² + ‖T x‖²` by the form identity, so `x = 0` and `g = 0`.
A submodule of a complete inner product space with trivial orthogonal complement is dense. -/
theorem dense_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) :
    Dense (((adjointComp T).domain : Submodule ℝ H₀) : Set H₀) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  obtain ⟨x, hx⟩ := exists_add_adjointComp T hT hd g
  have hzero : ⟪(x : H₀), g⟫ = 0 := hg (x : H₀) x.2
  rw [← hx, inner_add_right, ← real_inner_comm ((x : H₀)) (adjointComp T x),
    inner_adjointComp hd x x.2.2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hzero
  have hxz : (x : H₀) = 0 := by
    have : ‖(x : H₀)‖ = 0 := by nlinarith [norm_nonneg (x : H₀), sq_nonneg ‖T ⟨(x : H₀), x.2.2⟩‖]
    simpa using this
  have hx0 : x = 0 := Subtype.ext hxz
  rw [← hx, hx0]
  simp
/-- self-adjointness of T†T (von Neumann): `T†T` is self-adjoint.

Symmetry (`adjointComp_isFormalAdjoint`) together with density of `D(T†T)` (density of D(T†T)) gives
`T†T ≤ (T†T)†`.  For the reverse inclusion take `y ∈ D((T†T)†)`, solve `u + T†T u = y + (T†T)† y`
with `u ∈ D(T†T)` by surjectivity of `1 + T†T`, and test against an arbitrary `z = x + T†T x`:
both `⟪z, y⟫` and `⟪z, u⟫` collapse to `⟪x, y + (T†T)† y⟫`, so `y - u` is orthogonal to all of
`H₀` and therefore `y = u ∈ D(T†T)`, with `(T†T)† y = T†T u`.  The two inclusions have equal
domains, so `LinearPMap.eq_of_le_of_domain_eq` finishes. -/
theorem isSelfAdjoint_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) : IsSelfAdjoint (adjointComp T) := by
  have hdA := dense_adjointComp_domain T hT hd
  have hsym := adjointComp_isFormalAdjoint hd
  have hle : adjointComp T ≤ (adjointComp T)† := hsym.le_adjoint hdA
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdA (T := adjointComp T)
  have key : ∀ y : ((adjointComp T)†).domain, ∃ hm : (y : H₀) ∈ (adjointComp T).domain,
      adjointComp T ⟨(y : H₀), hm⟩ = (adjointComp T)† y := by
    intro y
    obtain ⟨u, hueq⟩ := exists_add_adjointComp T hT hd ((y : H₀) + (adjointComp T)† y)
    have hperp : ∀ z : H₀, ⟪z, (y : H₀) - (u : H₀)⟫ = 0 := by
      intro z
      obtain ⟨x, hxeq⟩ := exists_add_adjointComp T hT hd z
      have e1 : ⟪adjointComp T x, (y : H₀)⟫ = ⟪(x : H₀), (adjointComp T)† y⟫ := by
        rw [← real_inner_comm (adjointComp T x) ((y : H₀)), ← hfa y x]
        exact real_inner_comm _ _
      have e2 : ⟪adjointComp T x, (u : H₀)⟫ = ⟪(x : H₀), adjointComp T u⟫ := hsym x u
      have ea : ⟪(x : H₀) + adjointComp T x, (y : H₀)⟫
          = ⟪(x : H₀), (y : H₀) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, inner_add_right, e1]
      have eb : ⟪(x : H₀) + adjointComp T x, (u : H₀)⟫
          = ⟪(x : H₀), (y : H₀) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, e2, ← inner_add_right, hueq]
      rw [← hxeq, inner_sub_right, ea, eb, sub_self]
    have hyu : (y : H₀) = (u : H₀) :=
      sub_eq_zero.mp (inner_self_eq_zero.mp (hperp ((y : H₀) - (u : H₀))))
    refine ⟨hyu ▸ u.2, ?_⟩
    have hAu : adjointComp T ⟨(y : H₀), hyu ▸ u.2⟩ = adjointComp T u := by
      congr 1
      exact Subtype.ext hyu
    rw [hAu]
    have : (u : H₀) + adjointComp T u = (y : H₀) + (adjointComp T)† y := hueq
    rw [hyu] at this
    exact add_left_cancel this
  have hge : (adjointComp T)† ≤ adjointComp T := by
    refine ⟨fun y hy => (key ⟨y, hy⟩).choose, ?_⟩
    intro a b hab
    obtain ⟨hm, hval⟩ := key a
    have : b = ⟨(a : H₀), hm⟩ := Subtype.ext hab.symm
    rw [this, hval]
  rw [LinearPMap.isSelfAdjoint_def]
  exact LinearPMap.eq_of_le_of_domain_eq hge (le_antisymm hge.1 hle.1)
/-- the resolvent defect identity: the Yosida approximation on `D(T†T)`.

For `f ∈ D(T†T)`, `f - J_s f = s • J_s (T†T f)`; equivalently `L_s f = s⁻¹ (f - J_s f)` equals
`J_s (T†T f)`.  By the form identity, `f` itself solves the weak equation with datum `f + s • T†T f`, so
uniqueness (`eq_resolventDomain`) gives `J_s (f + s • T†T f) = f`, and linearity of `J_s`
separates the two terms. -/
theorem sub_resolvent_eq_smul (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : (adjointComp T).domain) :
    (f : H₀) - resolventCLM T hT hs f = s • resolventCLM T hT hs (adjointComp T f) := by
  have hweak : WeakResolvent T s ((f : H₀) + s • adjointComp T f) ⟨(f : H₀), f.2.2⟩ := by
    intro v
    have h := inner_adjointComp hd f v.2
    rw [inner_add_left, real_inner_smul_left, h]
  have heq := eq_resolventDomain T hT hs hweak
  have h2 : resolventCLM T hT hs ((f : H₀) + s • adjointComp T f) = (f : H₀) := by
    rw [resolventCLM_apply, ← heq]
  rw [map_add, map_smul] at h2
  exact (eq_sub_of_add_eq' h2).symm
end Resolvent
end Semigroup
end Analysis
end FunctionalInequalities


