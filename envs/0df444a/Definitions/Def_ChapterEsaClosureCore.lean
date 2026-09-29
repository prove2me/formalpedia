-- Prove2me | Definitions.Def_ChapterEsaClosureCore
-- name    : ChapterEsaClosureCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:19:19.207277+00:00
-- url     : https://prove2.me/theorems/486e34cc-abce-4241-a210-ae8228c75f31
-- title:
--   Every essential-self-adjointness theorem of this development — the Faris–Lavine chain of `BookProof.ChapterFarisLavine`, ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.EsaClosureCore`, source chapter `BookProof/ChapterEsaClosureCore.lean`).
--
--   Every essential-self-adjointness theorem of this development — the Faris–Lavine chain of `BookProof.ChapterFarisLavine`, the Navier–Stokes sequence-space chain (`BilinearEsa`, `AffineFiber`, `AffineBlock`, `SignFlip`, `SignedShift`, `ThreeComponent`), the Hermite-core theorems of the gravity and Yang–Mills routes — is stated as *trivial deficiency*: the only vector `w` with `⟪T v, w⟫ = ± i ⟪v, w⟫` for every `v` in the core is `w = 0` (`BookProof.FarisLavine.EssentiallySelfAdjointOn`).
--
--   That is the classical criterion, but it is a statement *about* the operator on the core; the object the physics needs — the self-adjoint generator whose unitary group is the flow, and the operator whose resolvent the Hashimoto/SIRK algorithm computes — is the **closure**. This module builds it and proves the two facts that make "essentially self-adjoint" mean what it says:
--
--   * `exists_isSelfAdjointExtension_of_esa` — **existence**: a densely defined symmetric operator with trivial deficiency has a self-adjoint extension, namely the closure of its graph. The construction is explicit (`clGraph`, `clDom`, `clExt`), and no positivity, boundedness or semiboundedness hypothesis is used. * `isSelfAdjointExtension_unique_of_esa` — **uniqueness**: *any* self-adjoint extension of an essentially self-adjoint operator has the same domain and the same values. So the closure is the only self-adjoint operator the core determines.
--
--   `IsSelfAdjointExtension` is the positivity-free companion of `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`; `isSelfAdjointExtension_of_positive` records that a positive self-adjoint extension is one.
--
--   `BookProof.ChapterHashimotoComplexShifts` runs the shift-invert rational Krylov algorithm at non-real shifts, where positivity of the operator is not needed — only symmetry and the self-adjointness criterion. Its headline (`hashimoto_multishift_selects_friedrichs`) was nevertheless stated for a *positive* self-adjoint extension. `hashimoto_multishift_selects_esa` removes the positivity hypothesis and feeds it the closure produced here: for an essentially self-adjoint operator on a dense core, and for an arbitrary sequence of non-real shifts, the resolvents `X_j = (γ_j − A)⁻¹` exist, are bounded by `1/|Im γ_j|`, satisfy the resolvent identity and the SIRK relation, have Galerkin truncations converging strongly, and each one of them determines `A` — the *unique* self-adjoint extension — completely.
--
--   Nothing here is a statement about any particular differential operator; it is the abstract von Neumann theory (deficiency indices `(0,0)` ⟹ unique self-adjoint extension) that the concrete chapters instantiate.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaClosureCore.lean

import Mathlib
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore

/-!
# Essential self-adjointness selects a **unique** self-adjoint operator

Every essential-self-adjointness theorem of this development — the Faris–Lavine
chain of `BookProof.ChapterFarisLavine`, the Navier–Stokes sequence-space chain
(`BilinearEsa`, `AffineFiber`, `AffineBlock`, `SignFlip`, `SignedShift`,
`ThreeComponent`), the Hermite-core theorems of the gravity and Yang–Mills
routes — is stated as *trivial deficiency*: the only vector `w` with
`⟪T v, w⟫ = ± i ⟪v, w⟫` for every `v` in the core is `w = 0`
(`BookProof.FarisLavine.EssentiallySelfAdjointOn`).

That is the classical criterion, but it is a statement *about* the operator on
the core; the object the physics needs — the self-adjoint generator whose
unitary group is the flow, and the operator whose resolvent the
Hashimoto/SIRK algorithm computes — is the **closure**.  This module builds it
and proves the two facts that make "essentially self-adjoint" mean what it says:

* `exists_isSelfAdjointExtension_of_esa` — **existence**: a densely defined
  symmetric operator with trivial deficiency has a self-adjoint extension,
  namely the closure of its graph.  The construction is explicit
  (`clGraph`, `clDom`, `clExt`), and no positivity, boundedness or
  semiboundedness hypothesis is used.
* `isSelfAdjointExtension_unique_of_esa` — **uniqueness**: *any* self-adjoint
  extension of an essentially self-adjoint operator has the same domain and the
  same values.  So the closure is the only self-adjoint operator the core
  determines.

`IsSelfAdjointExtension` is the positivity-free companion of
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`;
`isSelfAdjointExtension_of_positive` records that a positive self-adjoint
extension is one.

## The Hashimoto/SIRK consequence

`BookProof.ChapterHashimotoComplexShifts` runs the shift-invert rational Krylov
algorithm at non-real shifts, where positivity of the operator is not needed —
only symmetry and the self-adjointness criterion.  Its headline
(`hashimoto_multishift_selects_friedrichs`) was nevertheless stated for a
*positive* self-adjoint extension.  `hashimoto_multishift_selects_esa` removes
the positivity hypothesis and feeds it the closure produced here: for an
essentially self-adjoint operator on a dense core, and for an arbitrary
sequence of non-real shifts, the resolvents `X_j = (γ_j − A)⁻¹` exist, are
bounded by `1/|Im γ_j|`, satisfy the resolvent identity and the SIRK relation,
have Galerkin truncations converging strongly, and each one of them determines
`A` — the *unique* self-adjoint extension — completely.

## Honest boundary

Nothing here is a statement about any particular differential operator; it is
the abstract von Neumann theory (deficiency indices `(0,0)` ⟹ unique
self-adjoint extension) that the concrete chapters instantiate.
-/

open Filter Topology

namespace BookProof.EsaClosure

open BookProof.FarisLavine (EssentiallySelfAdjointOn SymmetricOn)
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-! ## Part 1 — the graph and its closure -/

/-- The graph `{(x, T x) : x ∈ D}` of `T`, as a submodule of `F × F`. -/
def opGraph (T : D →ₗ[ℂ] F) : Submodule ℂ (F × F) :=
  LinearMap.range (D.subtype.prod T)

theorem mem_opGraph (T : D →ₗ[ℂ] F) (v : D) : ((v : F), T v) ∈ opGraph T := ⟨v, rfl⟩

theorem opGraph_eq_range (T : D →ₗ[ℂ] F) :
    (opGraph T : Set (F × F)) = Set.range fun v : D => ((v : F), T v) := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩

/-- The **closure of the graph** of `T`. -/
def clGraph (T : D →ₗ[ℂ] F) : Submodule ℂ (F × F) := (opGraph T).topologicalClosure

theorem opGraph_le_clGraph (T : D →ₗ[ℂ] F) : opGraph T ≤ clGraph T :=
  Submodule.le_topologicalClosure _

theorem mem_clGraph_of_mem_opGraph {T : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ opGraph T) :
    p ∈ clGraph T := opGraph_le_clGraph T hp

theorem clGraph_isClosed (T : D →ₗ[ℂ] F) :
    IsClosed ((clGraph T : Submodule ℂ (F × F)) : Set (F × F)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every point of the closed graph is a limit point in the topological sense:
membership can be checked against any closed set containing the graph. -/
theorem clGraph_subset_of_isClosed {T : D →ₗ[ℂ] F} {S : Set (F × F)} (hS : IsClosed S)
    (hsub : ∀ v : D, ((v : F), T v) ∈ S) :
    ((clGraph T : Submodule ℂ (F × F)) : Set (F × F)) ⊆ S := by
  have h : (opGraph T : Set (F × F)) ⊆ S := by
    rw [opGraph_eq_range]
    rintro _ ⟨v, rfl⟩
    exact hsub v
  simpa [clGraph, Submodule.topologicalClosure_coe] using closure_minimal h hS

/-- **The closed graph is still a graph of the adjoint pairing**: every pair
`(x, y)` in the closure satisfies `⟪y, v⟫ = ⟪x, T v⟫` for `v` in the core. -/
theorem clGraph_inner {T : D →ₗ[ℂ] F} (hsym : SymmetricOn D T) {p : F × F}
    (hp : p ∈ clGraph T) (v : D) : (inner ℂ p.2 (v : F) : ℂ) = inner ℂ p.1 (T v) := by
  have hclosed : IsClosed {q : F × F | (inner ℂ q.2 (v : F) : ℂ) = inner ℂ q.1 (T v)} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  exact clGraph_subset_of_isClosed hclosed (fun u => hsym u v) hp

/-- **Symmetry passes to the closure** (as a pairing statement on the graph). -/
theorem clGraph_inner_pair {T : D →ₗ[ℂ] F} (hsym : SymmetricOn D T) {p q : F × F}
    (hp : p ∈ clGraph T) (hq : q ∈ clGraph T) :
    (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2 := by
  have hclosed : IsClosed {r : F × F | (inner ℂ p.2 r.1 : ℂ) = inner ℂ p.1 r.2} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  exact clGraph_subset_of_isClosed hclosed (fun v => clGraph_inner hsym hp v) hq

/-- **Closability**: a densely defined symmetric operator has a graph whose
closure is again a graph — the fibre over `0` is trivial. -/
theorem clGraph_snd_eq_zero_of_fst_eq_zero {T : D →ₗ[ℂ] F} (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D T) {y : F} (h : ((0 : F), y) ∈ clGraph T) : y = 0 := by
  refine Dense.eq_zero_of_inner_left ℂ hdense (fun v hv => ?_)
  have := clGraph_inner hsym h ⟨v, hv⟩
  simpa using this

/-- The **domain of the closure**: the first projection of the closed graph. -/
def clDom (T : D →ₗ[ℂ] F) : Submodule ℂ F := (clGraph T).map (LinearMap.fst ℂ F F)

theorem mem_clDom_iff {T : D →ₗ[ℂ] F} {x : F} : x ∈ clDom T ↔ ∃ y, (x, y) ∈ clGraph T := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩

theorem coe_mem_clDom (T : D →ₗ[ℂ] F) (v : D) : (v : F) ∈ clDom T :=
  mem_clDom_iff.2 ⟨T v, mem_clGraph_of_mem_opGraph (mem_opGraph T v)⟩

/-- The value of the closure at a point of its domain (chosen; unique by
`clFun_unique`). -/
noncomputable def clFun (T : D →ₗ[ℂ] F) (x : clDom T) : F :=
  Classical.choose (mem_clDom_iff.1 x.2)

theorem clFun_spec (T : D →ₗ[ℂ] F) (x : clDom T) : ((x : F), clFun T x) ∈ clGraph T :=
  Classical.choose_spec (mem_clDom_iff.1 x.2)

theorem clFun_unique {T : D →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    {x : clDom T} {y : F} (h : ((x : F), y) ∈ clGraph T) : clFun T x = y := by
  have hz : ((0 : F), clFun T x - y) ∈ clGraph T := by
    have := Submodule.sub_mem (clGraph T) (clFun_spec T x) h
    simpa using this
  exact sub_eq_zero.mp (clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym hz)

/-- **The closure of `T`**, as a linear operator on `clDom T`. -/
noncomputable def clExt (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    clDom T →ₗ[ℂ] F where
  toFun := clFun T
  map_add' x y := by
    refine clFun_unique hdense hsym ?_
    have := Submodule.add_mem (clGraph T) (clFun_spec T x) (clFun_spec T y)
    simpa using this
  map_smul' c x := by
    refine clFun_unique hdense hsym ?_
    have := Submodule.smul_mem (clGraph T) c (clFun_spec T x)
    simpa using this

@[simp] theorem clExt_apply (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (x : clDom T) : clExt T hdense hsym x = clFun T x := rfl

theorem clExt_extends (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (v : D) : clExt T hdense hsym ⟨(v : F), coe_mem_clDom T v⟩ = T v :=
  clFun_unique hdense hsym (mem_clGraph_of_mem_opGraph (mem_opGraph T v))

theorem clExt_symmetricOn (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    SymmetricOn (clDom T) (clExt T hdense hsym) := fun x y =>
  clGraph_inner_pair hsym (clFun_spec T x) (clFun_spec T y)

/-- **The closure is closed**: a convergent net in the graph of `clExt` has its
limit in the graph. -/
theorem mem_clGraph_of_tendsto {T : D →ₗ[ℂ] F} {ι : Type*} {l : Filter ι} [l.NeBot]
    {x : ι → clDom T} {p q : F}
    (hx : Tendsto (fun n => ((x n : F))) l (nhds p))
    (hA : Tendsto (fun n => clFun T (x n)) l (nhds q)) : (p, q) ∈ clGraph T := by
  have hprod : Tendsto (fun n => (((x n : F)), clFun T (x n))) l (nhds (p, q)) :=
    hx.prodMk_nhds hA
  exact (clGraph_isClosed T).mem_of_tendsto hprod
    (Eventually.of_forall fun n => clFun_spec T (x n))

/-- "`A` on `Dom` is a self-adjoint extension of `H` on `D`": the positivity-free
companion of `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`
(`BookProof.EsaClosure.isSelfAdjointExtension_of_positive`, in
`BookProof.ChapterEsaClosure`, derives this from that). -/
def IsSelfAdjointExtension {D Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (A : Dom →ₗ[ℂ] F) : Prop :=
  (∀ x : D, ∃ h : (x : F) ∈ Dom, A ⟨(x : F), h⟩ = H x) ∧ SymmetricOn Dom A ∧
    (∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)

/-! ## Part 2 — the closure is self-adjoint -/

section SelfAdjoint

variable [CompleteSpace F]

/-- The range of `γ − clExt` is closed: the operator is bounded below by
`|Im γ|` and its graph is closed by construction. -/
theorem clRange_isClosed (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    {γ : ℂ} (hγ : γ.im ≠ 0) :
    IsClosed ((cshiftRange (clExt T hdense hsym) γ : Submodule ℂ F) : Set F) := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  set A := clExt T hdense hsym with hA
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (|γ.im| * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : |γ.im| * ‖((x m - x n : clDom T) : F)‖ ≤ ‖cshiftMap A γ (x m - x n)‖ :=
      norm_cshiftMap_ge (clExt_symmetricOn T hdense hsym) _ _
    rw [map_sub, hx m, hx n] at hb
    have hlt : ‖u m - u n‖ < |γ.im| * eps := by
      have hd := hN m hm n hn
      rwa [dist_eq_norm] at hd
    have hkey : |γ.im| * ‖((x m : F)) - ((x n : F))‖ < |γ.im| * eps := by
      refine lt_of_le_of_lt ?_ hlt
      simpa using hb
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_left hkey hpos.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hAconv : Tendsto (fun n => clFun T (x n)) atTop (nhds (γ • w - p)) := by
    have hval : ∀ n, clFun T (x n) = γ • ((x n : F)) - u n := by
      intro n
      have hn := hx n
      simp only [cshiftMap_apply, hA, clExt_apply] at hn
      rw [← hn]; abel
    simp only [hval]
    exact (hw.const_smul γ).sub hup
  have hmem : (w, γ • w - p) ∈ clGraph T := mem_clGraph_of_tendsto hw hAconv
  have hwmem : w ∈ clDom T := mem_clDom_iff.2 ⟨_, hmem⟩
  refine ⟨⟨w, hwmem⟩, ?_⟩
  have hval : clFun T ⟨w, hwmem⟩ = γ • w - p := clFun_unique hdense hsym hmem
  simp only [cshiftMap_apply, hA, clExt_apply, hval]
  abel

omit [CompleteSpace F] in
/-- The range of `γ − clExt` is dense, for `γ = ± i`: a vector orthogonal to it
is a deficiency vector of `T` at the conjugate point, and there are none. -/
theorem clRange_orthogonal_eq_bot (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D T) (hesa : EssentiallySelfAdjointOn D T) :
    (cshiftRange (clExt T hdense hsym) Complex.I)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  refine hesa.2 w fun v => ?_
  have hmemD : (v : F) ∈ clDom T := coe_mem_clDom T v
  have hmem : cshiftMap (clExt T hdense hsym) Complex.I ⟨(v : F), hmemD⟩
      ∈ cshiftRange (clExt T hdense hsym) Complex.I := ⟨_, rfl⟩
  have h0 : (inner ℂ (cshiftMap (clExt T hdense hsym) Complex.I ⟨(v : F), hmemD⟩) w : ℂ) = 0 :=
    hw _ hmem
  rw [cshiftMap_apply, inner_sub_left, inner_smul_left, clExt_apply,
    show clFun T ⟨(v : F), hmemD⟩ = T v from clExt_extends T hdense hsym v] at h0
  have hconj : (starRingEnd ℂ) Complex.I = -Complex.I := by simp
  rw [hconj] at h0
  linear_combination -h0

/-- `i − clExt` is surjective. -/
theorem clShift_surjective (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (hesa : EssentiallySelfAdjointOn D T) :
    Function.Surjective (cshiftMap (clExt T hdense hsym) Complex.I) := by
  have hclosed : IsClosed ((cshiftRange (clExt T hdense hsym) Complex.I : Submodule ℂ F) : Set F) :=
    clRange_isClosed T hdense hsym (by simp)
  haveI : CompleteSpace (cshiftRange (clExt T hdense hsym) Complex.I) := hclosed.completeSpace_coe
  have htop : cshiftRange (clExt T hdense hsym) Complex.I = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (cshiftRange (clExt T hdense hsym) Complex.I)
    rw [clRange_orthogonal_eq_bot T hdense hsym hesa, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ cshiftRange (clExt T hdense hsym) Complex.I := by rw [htop]; trivial
  exact hmem

/-- **The closure of an essentially self-adjoint operator is self-adjoint.**
Given `w` with `T* w = u`, solve `(i − A) x = i w − u`; then `w − x` is a
deficiency vector of `T` at `i`, hence zero. -/
theorem clExt_selfAdjointCriterion (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D T) (hesa : EssentiallySelfAdjointOn D T) (w u : F)
    (hw : ∀ v : clDom T, (inner ℂ (clExt T hdense hsym v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ clDom T, clExt T hdense hsym ⟨w, h⟩ = u := by
  set A := clExt T hdense hsym with hAdef
  obtain ⟨x, hx⟩ := clShift_surjective T hdense hsym hesa (Complex.I • w - u)
  have hxval : Complex.I • ((x : F)) - A x = Complex.I • w - u := by
    simpa [cshiftMap_apply, hAdef] using hx
  -- `g = w - x` is a deficiency vector of `T` at `i`
  have hg : ∀ v : D, (inner ℂ (T v) (w - (x : F)) : ℂ)
      = Complex.I * inner ℂ (v : F) (w - (x : F)) := by
    intro v
    have hmemD : (v : F) ∈ clDom T := coe_mem_clDom T v
    have hTv : A ⟨(v : F), hmemD⟩ = T v := clExt_extends T hdense hsym v
    have h1 : (inner ℂ (A ⟨(v : F), hmemD⟩) w : ℂ) = inner ℂ (v : F) u := hw ⟨(v : F), hmemD⟩
    have h2 : (inner ℂ (A ⟨(v : F), hmemD⟩) ((x : F)) : ℂ) = inner ℂ (v : F) (A x) :=
      clExt_symmetricOn T hdense hsym ⟨(v : F), hmemD⟩ x
    have h3 : u - A x = Complex.I • (w - (x : F)) := by
      have : A x = Complex.I • ((x : F)) - (Complex.I • w - u) := by
        rw [← hxval]; abel
      rw [this, smul_sub]
      abel
    calc (inner ℂ (T v) (w - (x : F)) : ℂ)
        = (inner ℂ (A ⟨(v : F), hmemD⟩) w : ℂ) - inner ℂ (A ⟨(v : F), hmemD⟩) ((x : F)) := by
          rw [← hTv, inner_sub_right]
      _ = (inner ℂ (v : F) u : ℂ) - inner ℂ (v : F) (A x) := by rw [h1, h2]
      _ = (inner ℂ (v : F) (u - A x) : ℂ) := by rw [inner_sub_right]
      _ = (inner ℂ (v : F) (Complex.I • (w - (x : F))) : ℂ) := by rw [h3]
      _ = Complex.I * inner ℂ (v : F) (w - (x : F)) := by rw [inner_smul_right]
  have hzero : w - (x : F) = 0 := hesa.1 _ hg
  have hwx : w = (x : F) := by
    have := sub_eq_zero.mp hzero
    exact this
  have hwmem : w ∈ clDom T := hwx ▸ x.2
  refine ⟨hwmem, ?_⟩
  have hxx : (⟨w, hwmem⟩ : clDom T) = x := Subtype.ext hwx
  rw [hxx]
  have : A x = Complex.I • ((x : F)) - (Complex.I • w - u) := by rw [← hxval]; abel
  rw [this, hwx]
  abel

/-- **Existence.**  A densely defined symmetric operator with trivial deficiency
has a self-adjoint extension: the closure of its graph.  No positivity,
boundedness or semiboundedness is assumed. -/
theorem exists_isSelfAdjointExtension_of_esa (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D T) (hesa : EssentiallySelfAdjointOn D T) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSelfAdjointExtension T A :=
  ⟨clDom T, clExt T hdense hsym,
    fun v => ⟨coe_mem_clDom T v, clExt_extends T hdense hsym v⟩,
    clExt_symmetricOn T hdense hsym,
    clExt_selfAdjointCriterion T hdense hsym hesa⟩

/-! ## Part 3 — uniqueness -/

/-- **Uniqueness.**  Any self-adjoint extension of an essentially self-adjoint
operator is *the* adjoint: its domain is exactly the set of vectors on which the
adjoint of `T` is defined, and its values are the adjoint's values.  Combined
with `exists_isSelfAdjointExtension_of_esa` this is von Neumann's theorem:
deficiency indices `(0,0)` ⟹ a unique self-adjoint extension. -/
theorem selfAdjointExtension_eq_adjoint {Dom : Submodule ℂ F} {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F}
    (hesa : EssentiallySelfAdjointOn D T) (hA : IsSelfAdjointExtension T A) (w u : F) :
    ((∀ v : D, (inner ℂ (T v) w : ℂ) = inner ℂ (v : F) u) ↔
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u) := by
  obtain ⟨hext, hsymA, hsa⟩ := hA
  constructor
  · intro hw
    obtain ⟨x, hx⟩ := cshiftMap_surjective hsymA hsa (γ := Complex.I) (by simp)
      (Complex.I • w - u)
    have hxval : Complex.I • ((x : F)) - A x = Complex.I • w - u := by
      simpa [cshiftMap_apply] using hx
    have hg : ∀ v : D, (inner ℂ (T v) (w - (x : F)) : ℂ)
        = Complex.I * inner ℂ (v : F) (w - (x : F)) := by
      intro v
      obtain ⟨hmemD, hTv⟩ := hext v
      have h1 : (inner ℂ (T v) w : ℂ) = inner ℂ (v : F) u := hw v
      have h2 : (inner ℂ (T v) ((x : F)) : ℂ) = inner ℂ (v : F) (A x) := by
        rw [← hTv]
        exact hsymA ⟨(v : F), hmemD⟩ x
      have h3 : u - A x = Complex.I • (w - (x : F)) := by
        have hAx : A x = Complex.I • ((x : F)) - (Complex.I • w - u) := by rw [← hxval]; abel
        rw [hAx, smul_sub]; abel
      calc (inner ℂ (T v) (w - (x : F)) : ℂ)
          = (inner ℂ (T v) w : ℂ) - inner ℂ (T v) ((x : F)) := by rw [inner_sub_right]
        _ = (inner ℂ (v : F) u : ℂ) - inner ℂ (v : F) (A x) := by rw [h1, h2]
        _ = (inner ℂ (v : F) (u - A x) : ℂ) := by rw [inner_sub_right]
        _ = (inner ℂ (v : F) (Complex.I • (w - (x : F))) : ℂ) := by rw [h3]
        _ = Complex.I * inner ℂ (v : F) (w - (x : F)) := by rw [inner_smul_right]
    have hwx : w = (x : F) := sub_eq_zero.mp (hesa.1 _ hg)
    have hwmem : w ∈ Dom := hwx ▸ x.2
    refine ⟨hwmem, ?_⟩
    have hxx : (⟨w, hwmem⟩ : Dom) = x := Subtype.ext hwx
    rw [hxx]
    have hAx : A x = Complex.I • ((x : F)) - (Complex.I • w - u) := by rw [← hxval]; abel
    rw [hAx, hwx]; abel
  · rintro ⟨hwmem, hAw⟩ v
    obtain ⟨hmemD, hTv⟩ := hext v
    rw [← hTv, ← hAw]
    exact hsymA ⟨(v : F), hmemD⟩ ⟨w, hwmem⟩

/-- **The self-adjoint extension of an essentially self-adjoint operator is
unique**: two of them have the same domain and the same values. -/
theorem isSelfAdjointExtension_unique_of_esa {Dom₁ Dom₂ : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    {A₁ : Dom₁ →ₗ[ℂ] F} {A₂ : Dom₂ →ₗ[ℂ] F} (hesa : EssentiallySelfAdjointOn D T)
    (h₁ : IsSelfAdjointExtension T A₁) (h₂ : IsSelfAdjointExtension T A₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), A₁ ⟨x, h⟩ = A₂ ⟨x, h'⟩ := by
  have key : ∀ (x : F) (h : x ∈ Dom₁), ∃ h' : x ∈ Dom₂, A₂ ⟨x, h'⟩ = A₁ ⟨x, h⟩ := by
    intro x h
    exact (selfAdjointExtension_eq_adjoint hesa h₂ x (A₁ ⟨x, h⟩)).1
      ((selfAdjointExtension_eq_adjoint hesa h₁ x (A₁ ⟨x, h⟩)).2 ⟨h, rfl⟩)
  have key' : ∀ (x : F) (h : x ∈ Dom₂), ∃ h' : x ∈ Dom₁, A₁ ⟨x, h'⟩ = A₂ ⟨x, h⟩ := by
    intro x h
    exact (selfAdjointExtension_eq_adjoint hesa h₁ x (A₂ ⟨x, h⟩)).1
      ((selfAdjointExtension_eq_adjoint hesa h₂ x (A₂ ⟨x, h⟩)).2 ⟨h, rfl⟩)
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro x hx; exact (key x hx).choose
    · intro x hx; exact (key' x hx).choose
  · intro x h h'
    obtain ⟨hx₂, hval⟩ := key x h
    exact hval.symm

end SelfAdjoint

/-! ## Part 4 — the Cayley transform: the generator produces a unitary -/

section Cayley

variable [CompleteSpace F] {Dom : Submodule ℂ F}

omit [CompleteSpace F] in
/-- For a symmetric operator `‖A x + i x‖ = ‖A x − i x‖`: the expectation
`⟪A x, x⟫` is real, so the two cross terms vanish.  This is what makes the
Cayley transform an isometry. -/
theorem norm_add_I_eq_norm_sub_I {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A) (x : Dom) :
    ‖A x + Complex.I • (x : F)‖ = ‖A x - Complex.I • (x : F)‖ := by
  have him : (inner ℂ (A x) (x : F) : ℂ).im = 0 := inner_apply_self_im A hsym x
  have hcross : RCLike.re (inner ℂ (A x) (Complex.I • (x : F)) : ℂ) = 0 := by
    rw [inner_smul_right]; simp [him]
  have h1 : ‖A x + Complex.I • (x : F)‖ ^ 2 = ‖A x - Complex.I • (x : F)‖ ^ 2 := by
    rw [@norm_add_sq ℂ, @norm_sub_sq ℂ, hcross]; ring
  nlinarith [h1, norm_nonneg (A x + Complex.I • (x : F)), norm_nonneg (A x - Complex.I • (x : F))]

/-- **The Cayley transform of a self-adjoint operator is a unitary of the whole
space.**  `U = (A − i)(A + i)⁻¹` is everywhere defined, linear, norm-preserving
and bijective, and it carries `A x + i x` to `A x − i x` on the domain.  It is
the step from the self-adjoint generator to a unitary that does *not* need
Stone's theorem; the unitary *group* `e^{-itA}` remains the recorded research
boundary. -/
theorem exists_cayley_unitary {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u) :
    ∃ U : F ≃ₗᵢ[ℂ] F, ∀ x : Dom, U (A x + Complex.I • (x : F)) = A x - Complex.I • (x : F) := by
  classical
  set p : Dom →ₗ[ℂ] F := -cshiftMap A (-Complex.I) with hp
  set m : Dom →ₗ[ℂ] F := -cshiftMap A Complex.I with hm
  have hpx : ∀ x : Dom, p x = A x + Complex.I • (x : F) := by
    intro x
    simp only [hp, LinearMap.neg_apply, cshiftMap_apply, neg_sub, neg_smul]
    abel
  have hmx : ∀ x : Dom, m x = A x - Complex.I • (x : F) := by
    intro x
    simp only [hm, LinearMap.neg_apply, cshiftMap_apply, neg_sub]
  have hpinj : Function.Injective p := by
    intro x y hxy
    have h : -(cshiftMap A (-Complex.I) x) = -(cshiftMap A (-Complex.I) y) := by
      simpa [hp] using hxy
    exact cshiftMap_injective hsym (by simp) (neg_injective h)
  have hpsurj : Function.Surjective p := by
    intro u
    obtain ⟨x, hx⟩ := cshiftMap_surjective hsym hsa (γ := -Complex.I) (by simp) (-u)
    exact ⟨x, by simp [hp, hx]⟩
  have hminj : Function.Injective m := by
    intro x y hxy
    have h : -(cshiftMap A Complex.I x) = -(cshiftMap A Complex.I y) := by simpa [hm] using hxy
    exact cshiftMap_injective hsym (by simp) (neg_injective h)
  have hmsurj : Function.Surjective m := by
    intro u
    obtain ⟨x, hx⟩ := cshiftMap_surjective hsym hsa (γ := Complex.I) (by simp) (-u)
    exact ⟨x, by simp [hm, hx]⟩
  let ep : Dom ≃ₗ[ℂ] F := LinearEquiv.ofBijective p ⟨hpinj, hpsurj⟩
  let em : Dom ≃ₗ[ℂ] F := LinearEquiv.ofBijective m ⟨hminj, hmsurj⟩
  have hnorm : ∀ u : F, ‖(ep.symm.trans em) u‖ = ‖u‖ := by
    intro u
    have hu : u = p (ep.symm u) := (ep.apply_symm_apply u).symm
    calc ‖(ep.symm.trans em) u‖ = ‖m (ep.symm u)‖ := rfl
      _ = ‖A (ep.symm u) - Complex.I • ((ep.symm u : Dom) : F)‖ := by rw [hmx]
      _ = ‖A (ep.symm u) + Complex.I • ((ep.symm u : Dom) : F)‖ :=
            (norm_add_I_eq_norm_sub_I hsym _).symm
      _ = ‖p (ep.symm u)‖ := by rw [hpx]
      _ = ‖u‖ := by rw [← hu]
  refine ⟨{ toLinearEquiv := ep.symm.trans em, norm_map' := hnorm }, fun x => ?_⟩
  have hx : ep.symm (A x + Complex.I • (x : F)) = x := by
    have hpe : ep x = A x + Complex.I • (x : F) := hpx x
    rw [← hpe, ep.symm_apply_apply]
  change em (ep.symm (A x + Complex.I • (x : F))) = _
  rw [hx]
  exact hmx x

/-- **The Cayley transform of the closure of an essentially self-adjoint
operator.**  Combining `exists_isSelfAdjointExtension_of_esa` with
`exists_cayley_unitary`: an essentially self-adjoint operator on a dense core
produces a self-adjoint operator and, from it, a unitary of the whole space. -/
theorem exists_selfAdjointExtension_and_cayley_of_esa (T : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T)
    (hesa : EssentiallySelfAdjointOn D T) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (U : F ≃ₗᵢ[ℂ] F),
      IsSelfAdjointExtension T A ∧
      ∀ x : Dom, U (A x + Complex.I • (x : F)) = A x - Complex.I • (x : F) := by
  obtain ⟨Dom, A, hA⟩ := exists_isSelfAdjointExtension_of_esa T hdense hsym hesa
  obtain ⟨hext, hsymA, hsa⟩ := hA
  obtain ⟨U, hU⟩ := exists_cayley_unitary hsymA hsa
  exact ⟨Dom, A, U, ⟨hext, hsymA, hsa⟩, hU⟩

end Cayley


end BookProof.EsaClosure


