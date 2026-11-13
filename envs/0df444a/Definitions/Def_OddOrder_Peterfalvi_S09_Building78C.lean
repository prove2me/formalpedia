-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_Building78C
-- name    : OddOrder_Peterfalvi_S09_Building78C
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:59:57.349595+00:00
-- url     : https://prove2.me/theorems/269f613e-1722-444c-898c-aa1c70dd6399
-- title:
--   Peterfalvi §7: the supported projection and the (7.7.a) decomposition
-- statement:
--   Part of the Peterfalvi §7 certificate-discharge development, proving the (7.7.a) decomposition and the (12.14) evaluation $\psi^\rho(x)=\chi(x)$.
--
--   Main definition: `supportedProj` (the projection $\eta\mapsto\eta\cdot\mathbb{1}_A$ of a class function onto $\mathrm{CF}(L,A)$). Results include `inner_supportedProj`, `eq_zero_on_A_of_inner_zero` (the (7.7.a) determination step), `chiRho_decomp_proof` (the decomposition) and `chiRho_apply_eq_zeta0_of_inner_tau_uniform` (the two-sided evaluation).
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_Building78C.lean

/-
# Peterfalvi §7 — discharging the `(7.7.a)`/`(7.8.c)` certificates of `S09`

`S09_NonexistenceCertain.lean` carries Peterfalvi's `(7.7.a)` (`Hypothesis76.chiRho_decomp`) and
`(7.8.c.i)` (`Hypothesis78.chiRho_eq_inner_beta`) as structural certificate fields: deriving them
needs the `CF(L,A)`-basis argument of Peterfalvi (7.7), whose foundation is the **spanning
identity** formalized here.

This file lives outside `S09` (which is concurrently edited for the `(7.11)` assembly) to avoid
conflicts; it imports the `S09` machinery and supplies standalone lemmas toward the certificate
discharge (issue 1013).
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_Building78C.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily

namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **Peterfalvi (7.7.a), the spanning identity.**  For a *normal* subgroup `K ◁ L` and a class
function `ψ` on `L` supported inside `K` (vanishing off `K`),
`Ind_K^L Res_K^L ψ = [L : K] · ψ`.

This is the key step in Peterfalvi's proof that `CF(L, A)` (with `A = K^#`) is spanned by the
family `{Ind_K^L θ}`: since `ψ = (1/e) Ind_K^L Res_K^L ψ` lies in the span of the induced
characters, the basis argument of (7.7.a) applies.

Proof.  Pointwise.  For `y ∈ K`, normality makes every conjugate `x⁻¹ y x ∈ K`, so each induction
summand is `ψ(x⁻¹ y x) = ψ(y)` (class function); the `|L|` summands divided by `|K|` give
`[L:K]·ψ(y)`.  For `y ∉ K`, no conjugate lies in `K`, so the induction vanishes — as does `ψ(y)`. -/
theorem induce_restrict_eq_index_smul (K : Subgroup L) [hK : K.Normal]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ClassFunction.induce K (ClassFunction.restrict K ψ) = (K.index : ℂ) • ψ := by
  classical
  ext y
  rw [ClassFunction.induce_apply, ClassFunction.smul_apply]
  by_cases hy : y ∈ K
  · -- Every induction summand equals `ψ y`.
    have hterm : ∀ x : L, ClassFunction.induceTerm K (ClassFunction.restrict K ψ) x y = ψ y := by
      intro x
      have hxy : x⁻¹ * y * x ∈ K := by simpa using hK.conj_mem y hy x⁻¹
      rw [ClassFunction.induceTerm_of_mem _ hxy, ClassFunction.restrict_apply]
      simpa using ψ.conj_eq y x⁻¹
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have hcard : (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) := by
      rw [← Nat.cast_mul, K.index_mul_card]
    rw [hcard,
      show ⅟(Nat.card ↥K : ℂ) * ((K.index : ℂ) * (Nat.card ↥K : ℂ) * ψ y)
        = (K.index : ℂ) * (⅟(Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ)) * ψ y from by ring,
      invOf_mul_self, mul_one]
  · -- `y ∉ K`: every summand vanishes (no conjugate lands in `K`), and `ψ y = 0`.
    have hterm : ∀ x : L, ClassFunction.induceTerm K (ClassFunction.restrict K ψ) x y = 0 := by
      intro x
      apply ClassFunction.induceTerm_of_not_mem
      intro hmem
      apply hy
      have hconj := hK.conj_mem (x⁻¹ * y * x) hmem x
      have he : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [he] at hconj
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero,
      hψ y hy, mul_zero]

/-- **Peterfalvi (7.7.a), `CF(L,A)` is induced from `K`.**  A class function `ψ` on `L` supported
inside a normal subgroup `K` (i.e. `ψ ∈ CF(L, K^#)`) is the induction of a class function on `K`,
namely `ψ = Ind_K^L ((1/[L:K]) · Res_K^L ψ)`.  Immediate from the spanning identity
`induce_restrict_eq_index_smul` and linearity of induction (`induce_smul`).

This realizes the membership `CF(L,A) ⊆ Ind_K^L(CF(K)) = ⟨Ind_K^L θ⟩_ℂ` that underlies Peterfalvi's
basis argument: every `ψ ∈ CF(L,A)` lies in the `ℂ`-span of the family `T = {Ind_K^L θ}`. -/
theorem eq_induce_restrict_of_supported (K : Subgroup L) [K.Normal]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ψ = ClassFunction.induce K ((K.index : ℂ)⁻¹ • ClassFunction.restrict K ψ) := by
  rw [ClassFunction.induce_smul, induce_restrict_eq_index_smul K ψ hψ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite), one_smul]

/-- **The induced characters span the image of induction** (Peterfalvi (7.7.a) spanning, image
half).  Every induced class function `Ind_K^L φ` lies in the `ℂ`-span of the induced *irreducible*
characters `{Ind_K^L θ : θ ∈ Irr K}`.  Expand `φ` in the irreducible basis of `CF(K)`
(`span_irreducibleCharacter_eq_top`) and push through the linearity of induction
(`induce_add`/`induce_smul`/`induce_zero`) by `Submodule.span_induction`. -/
theorem induce_mem_span_induce_irr (K : Subgroup L) [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (φ : ClassFunction ↥K ℂ) :
    ClassFunction.induce K φ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  have hφ : φ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K => (θ : ClassFunction ↥K ℂ))) := by
    rw [span_irreducibleCharacter_eq_top]; exact Submodule.mem_top
  induction hφ using Submodule.span_induction with
  | mem v hv => obtain ⟨θ, rfl⟩ := hv; exact Submodule.subset_span ⟨θ, rfl⟩
  | zero => rw [ClassFunction.induce_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [ClassFunction.induce_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih => rw [ClassFunction.induce_smul]; exact Submodule.smul_mem _ c ih

/-- **`CF(L,A)` lies in the span of the induced irreducibles** (Peterfalvi (7.7.a) spanning).  A
class function `ψ` supported inside the normal subgroup `K` lies in the `ℂ`-span of the family
`{Ind_K^L θ : θ ∈ Irr K}`: combine `eq_induce_restrict_of_supported` (`ψ = Ind_K^L(e⁻¹ Res ψ)`,
so `ψ ∈ Ind_K^L(CF K)`) with `induce_mem_span_induce_irr`.  This is the spanning input that, after
the degree-`0` reduction (`mem_span_psi_of_apply_one_zero`), supplies the `hspan` hypothesis of
`chiRho_decomp_proof`. -/
theorem supported_mem_span_induce_irr (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (ψ : ClassFunction L ℂ)
    (hψ : ∀ y : L, y ∉ K → ψ y = 0) :
    ψ ∈ Submodule.span ℂ
      (Set.range (fun θ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (θ : ClassFunction ↥K ℂ))) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  rw [eq_induce_restrict_of_supported K ψ hψ]
  exact induce_mem_span_induce_irr K _

/-- **Positive-definiteness of Peterfalvi's class-function inner product.**  Over `ℂ`,
`⟨η, η⟩ = 0` forces `η = 0`.  Indeed `⟨η, η⟩ = |G|⁻¹ Σ_g |η(g)|²`, a sum of non-negative reals, so
it vanishes only when every `η(g) = 0`.  This is the non-degeneracy used in Peterfalvi's (7.7.a)
basis argument: a class function in `CF(L,A)` orthogonal to a spanning set is zero. -/
theorem inner_self_eq_zero [Invertible (Nat.card L : ℂ)] {η : ClassFunction L ℂ}
    (h : ClassFunction.inner η η = 0) :
    η = 0 := by
  have hsum : ClassFunction.innerSum η η = 0 := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum] at h
    have := congrArg (fun z => (Nat.card L : ℂ) * z) h
    simpa [← mul_assoc, mul_invOf_self] using this
  have hreal : (∑ g : L, Complex.normSq (η g)) = 0 := by
    have hcast : (∑ g : L, η g * star (η g)) = ((∑ g : L, Complex.normSq (η g) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun g _ => Complex.mul_conj (η g)
    have : ((∑ g : L, Complex.normSq (η g) : ℝ) : ℂ) = 0 := by
      rw [← hcast]; exact hsum
    exact_mod_cast this
  have hzero : ∀ g : L, Complex.normSq (η g) = 0 :=
    fun g => (Finset.sum_eq_zero_iff_of_nonneg fun g _ => Complex.normSq_nonneg _).mp hreal g
      (Finset.mem_univ g)
  ext g
  simpa using Complex.normSq_eq_zero.mp (hzero g)

/-- **The inner product only sees the second factor on the support of the first.**  If `ψ` and `ψ'`
agree wherever `α` is nonzero, then `⟨α, ψ⟩ = ⟨α, ψ'⟩`.  Used in (7.8.a)/(7.8.c) where a class
function supported on `A` is paired against `(1_G)^ρ`, which equals `1_L` on `A`. -/
theorem inner_eq_of_eqOn_support [Invertible (Nat.card L : ℂ)] {α ψ ψ' : ClassFunction L ℂ}
    (h : ∀ g : L, α g ≠ 0 → ψ g = ψ' g) :
    ClassFunction.inner α ψ = ClassFunction.inner α ψ' := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  by_cases hg : α g = 0
  · rw [hg, zero_mul, zero_mul]
  · rw [h g hg]

/-- **Peterfalvi (7.7.a), the uniqueness principle.**  If `η` lies in the `ℂ`-span of a set `S` of
class functions and is orthogonal to every member of `S`, then `η = 0`.  This is the
non-degeneracy of the inner product on a spanned subspace: the linear functional `⟨·, η⟩` vanishes
on `S`, hence on `span S ∋ η`, giving `⟨η, η⟩ = 0` and `η = 0` by `inner_self_eq_zero`.

In (7.7.a), `S = {ψ_i}` spans `CF(L,A)`, so a class function in `CF(L,A)` is determined by its inner
products against the `ψ_i` — the determination of `χ^ρ` on `A`. -/
theorem eq_zero_of_mem_span_orthogonal [Invertible (Nat.card L : ℂ)]
    {S : Set (ClassFunction L ℂ)} {η : ClassFunction L ℂ}
    (hη : η ∈ Submodule.span ℂ S) (horth : ∀ v ∈ S, ClassFunction.inner v η = 0) :
    η = 0 := by
  have key : ∀ φ ∈ Submodule.span ℂ S, ClassFunction.inner φ η = 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem v hv => exact horth v hv
    | zero => exact ClassFunction.inner_zero_left η
    | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_left, ihx, ihy, add_zero]
    | smul c x _ ih => rw [ClassFunction.inner_smul_left, ih, mul_zero]
  exact inner_self_eq_zero (key η hη)

open scoped Classical in
/-- **The supported projection** `η ↦ η · 𝟙_A` of a class function onto `CF(L, A)`.  When `A` is a
conjugation-invariant set, the pointwise product with the indicator of `A` is again a class
function (the indicator and `η` are both conjugation-invariant).  This is the projection used in
Peterfalvi's (7.7.a) basis argument to compare `χ^ρ` (already supported on `A`) with the candidate
linear combination `Σ c̄_i/‖ζ_i‖² ζ_i` (whose `A`-part is what (7.7.a) computes). -/
noncomputable def supportedProj (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) : ClassFunction L ℂ :=
  ⟨fun x => if x ∈ A then η x else 0, fun g h => by
    by_cases hg : g ∈ A
    · simp only [if_pos hg, if_pos ((hA g h).mpr hg), η.conj_eq g h]
    · simp only [if_neg hg, if_neg (fun hc => hg ((hA g h).mp hc))]⟩

omit [Fintype L] in
open scoped Classical in
@[simp] theorem supportedProj_apply (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) (x : L) :
    supportedProj A hA η x = if x ∈ A then η x else 0 := rfl

omit [Fintype L] in
open scoped Classical in
/-- The supported projection is supported on `A` (lies in `CF(L,A)`). -/
theorem supportedProj_mem_supported (A : Set L) (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A)
    (η : ClassFunction L ℂ) :
    supportedProj A hA η ∈ ClassFunction.supportedSubmodule A := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro x hx
  by_contra hxA
  apply hx
  change supportedProj A hA η x = 0
  simp only [supportedProj_apply, if_neg hxA]

open scoped Classical in
/-- **The supported projection preserves inner products against `CF(L,A)`.**  For `ψ` supported on
`A`, `⟨ψ, η · 𝟙_A⟩ = ⟨ψ, η⟩`: off `A` the factor `ψ(x)` already vanishes, so multiplying `η` by the
indicator of `A` changes nothing. -/
theorem inner_supportedProj [Invertible (Nat.card L : ℂ)] (A : Set L)
    (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A) {ψ : ClassFunction L ℂ}
    (hψ : ψ ∈ ClassFunction.supportedSubmodule A) (η : ClassFunction L ℂ) :
    ClassFunction.inner ψ (supportedProj A hA η) = ClassFunction.inner ψ η := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum]
  congr 1
  simp only [ClassFunction.innerSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [supportedProj_apply, if_pos hx]
  · have hψx : ψ x = 0 := by
      by_contra h0
      exact hx ((ClassFunction.mem_supportedSubmodule.mp hψ) (ClassFunction.mem_support.mpr h0))
    rw [hψx, zero_mul, zero_mul]

open scoped Classical in
/-- **Peterfalvi (7.7.a), the determination step.**  If a set `S` of class functions spans `CF(L,A)`
(`hspan`) and consists of `A`-supported functions (`hS_supp`), then a class function `η` orthogonal
to every member of `S` vanishes on `A`.  Apply the uniqueness principle to the supported projection
`η · 𝟙_A ∈ CF(L,A) = span S`, which is orthogonal to `S` (`inner_supportedProj`), hence zero.

This is the heart of (7.7.a): `χ^ρ − Σ c̄_i/‖ζ_i‖² ζ_i` is orthogonal to the spanning `{ψ_i}` (the
inner products are the `c_i`), so it vanishes on `A` — pinning down `χ^ρ` there. -/
theorem eq_zero_on_A_of_inner_zero [Invertible (Nat.card L : ℂ)] (A : Set L)
    (hA : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A) {S : Set (ClassFunction L ℂ)}
    (hspan : ClassFunction.supportedSubmodule A ≤ Submodule.span ℂ S)
    (hS_supp : ∀ v ∈ S, v ∈ ClassFunction.supportedSubmodule A)
    {η : ClassFunction L ℂ} (horth : ∀ v ∈ S, ClassFunction.inner v η = 0)
    {x : L} (hx : x ∈ A) :
    η x = 0 := by
  have hproj_zero : supportedProj A hA η = 0 :=
    eq_zero_of_mem_span_orthogonal (hspan (supportedProj_mem_supported A hA η))
      (fun v hv => by rw [inner_supportedProj A hA (hS_supp v hv) η]; exact horth v hv)
  have h0 : supportedProj A hA η x = 0 := by rw [hproj_zero]; rfl
  rwa [supportedProj_apply, if_pos hx] at h0

/-- **Peterfalvi (7.7.a), the Gram entry.**  For a pairwise-orthogonal family
`ζ : Fin (n+1) → CF(L)`
and the difference vectors `ψ_j = ζ_j − d_j ζ_0` (`j ≥ 1`), the inner product `⟨ψ_j, ζ_i⟩` (`i ≥ 1`)
is the diagonal entry `‖ζ_j‖²` when `i = j` and `0` otherwise: the `ζ_0` term drops out (`0 ≠ i`)
and
the `ζ_j`-term is the orthonormality indicator.  This is the Gram matrix that pins the coefficients
of the (7.7.a) decomposition. -/
theorem inner_psi_zeta [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    {i j : Fin (n + 1)} (hi : i ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0) (ζ i) =
      if i = j then ClassFunction.inner (ζ j) (ζ j) else 0 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    horth 0 i (Ne.symm hi), mul_zero, sub_zero]
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij, horth j i (fun h => hij h.symm)]

/-- **Peterfalvi (7.7.a), the Gram sum.**  For a pairwise-orthogonal family `ζ` and `j ≥ 1`, pairing
`ψ_j = ζ_j − d_j ζ_0` against any linear combination `Σ_{i ≥ 1} b_i ζ_i` picks out the diagonal:
`⟨ψ_j, Σ_{i≥1} b_i ζ_i⟩ = star(b_j) ‖ζ_j‖²`.  Immediate from the Gram entry `inner_psi_zeta` and
`Finset.sum_eq_single`. In (7.7.a) the candidate is `Σ_{i≥1} (c̄_i/‖ζ_i‖²) ζ_i`, so this equals
`c_j`
(after `star (c̄_j/‖ζ_j‖²)·‖ζ_j‖² = c_j`, using `‖ζ_j‖²` real). -/
theorem inner_psi_candidate [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (b : Fin (n + 1) → ℂ) {j : Fin (n + 1)} (hj : j ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0)
        (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), b i • ζ i) =
      star (b j) * ClassFunction.inner (ζ j) (ζ j) := by
  rw [inner_sum_right, Finset.sum_eq_single j
    (fun i hi hij => by
      rw [ClassFunction.inner_smul_right, inner_psi_zeta ζ d horth (Finset.mem_Ioi.mp hi).ne',
        if_neg hij, mul_zero])
    (fun hj_notin => absurd (Finset.mem_Ioi.mpr (Fin.pos_of_ne_zero hj)) hj_notin)]
  rw [ClassFunction.inner_smul_right, inner_psi_zeta ζ d horth hj, if_pos rfl]

/-- **Peterfalvi (7.7.a), the candidate-coefficient identity.**  With the (7.7.a) coefficients
`b_i = star(c_i)/‖ζ_i‖²`, the pairing of `ψ_j` against the candidate `Σ_{i≥1} b_i ζ_i` recovers
`c_j` exactly: `star(b_j)·‖ζ_j‖² = (c_j/‖ζ_j‖²)·‖ζ_j‖² = c_j` (using `‖ζ_j‖²` real and nonzero).
This is the consistency that makes `Σ c̄_i/‖ζ_i‖² ζ_i` the decomposition of `χ^ρ`. -/
theorem inner_psi_candidate_eq [Invertible (Nat.card L : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (c : Fin (n + 1) → ℂ) (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    {j : Fin (n + 1)} (hj : j ≠ 0) :
    ClassFunction.inner (ζ j - d j • ζ 0)
        (∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
          (star (c i) / ClassFunction.inner (ζ i) (ζ i)) • ζ i) = c j := by
  rw [inner_psi_candidate ζ d horth (fun i => star (c i) / ClassFunction.inner (ζ i) (ζ i)) hj,
    div_eq_mul_inv, star_mul, star_star, star_inv₀,
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.star_inner_self,
    mul_right_comm, inv_mul_cancel₀ (hnorm j), one_mul]

open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (7.7.a), the decomposition.**  Given the §7 `ρ`-machinery (`Hypothesis71`), a
pairwise-orthogonal family `ζ` of class functions with nonzero norms whose difference vectors
`ψ_i = ζ_i − d_i ζ_0` are `A`-supported and span `CF(L, A)`, the `ρ`-image of any `χ` decomposes on
`A` as `χ^ρ(x) = Σ_{i≥1} c̄_i/‖ζ_i‖² · ζ_i(x)`, where `c_i = ⟨ψ_i^τ, χ⟩`.

This **discharges the `Hypothesis76.chiRho_decomp` certificate** of Peterfalvi (7.7.a) (issue 1013):
the candidate `Σ c̄_i/‖ζ_i‖² ζ_i` and `χ^ρ` have the same inner products `c_j` against the spanning
`{ψ_j}` (`chiRho_adjoint` on one side, `inner_psi_candidate_eq` on the other), so their difference
is
orthogonal to a spanning set of `CF(L,A)` and hence vanishes on `A`
(`eq_zero_on_A_of_inner_zero`). -/
theorem chiRho_decomp_proof {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    (hAconj : ∀ g h : L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hspan : ClassFunction.supportedSubmodule (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ≤
      Submodule.span ℂ ((fun j => ζ j - d j • ζ 0) '' {j : Fin (n + 1) | j ≠ 0}))
    (χ : ClassFunction G ℂ) {x : L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner (H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) χ) /
          ClassFunction.inner (ζ i) (ζ i)) * ζ i x := by
  set A' := OddOrder.Peterfalvi.S04.supportInSubgroup A L with hA'
  set c : Fin (n + 1) → ℂ :=
    fun i => ClassFunction.inner (H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) χ with hc
  set cand : ClassFunction L ℂ :=
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
      (star (c i) / ClassFunction.inner (ζ i) (ζ i)) • ζ i with hcand
  -- `η = χ^ρ − cand` is orthogonal to every `ψ_j` and lies in `CF(L,A) = span {ψ_j}`, so it
  -- vanishes on `A`.
  have hηA : (H71.chiRhoCF χ - cand) x = 0 := by
    apply eq_zero_on_A_of_inner_zero A' hAconj hspan
    · rintro v ⟨j, _, rfl⟩
      rw [ClassFunction.mem_supportedSubmodule]
      exact psi_support j
    · rintro v ⟨j, hj, rfl⟩
      rw [ClassFunction.inner_sub_right,
        show ClassFunction.inner (ζ j - d j • ζ 0) (H71.chiRhoCF χ) = c j from
          (H71.chiRho_adjoint ⟨ζ j - d j • ζ 0, psi_support j⟩ χ).symm,
        inner_psi_candidate_eq ζ d horth c hnorm hj, sub_self]
    · rw [hA', OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx
  -- conclude `χ^ρ x = cand x`, then evaluate the sum.
  have hval : H71.chiRho χ x = cand x := by
    have := hηA
    rw [ClassFunction.sub_apply, H71.chiRhoCF_apply] at this
    exact sub_eq_zero.mp this
  rw [hval, hcand, ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [ClassFunction.smul_apply]

/-- **Peterfalvi (12.14), the source-side (7.7.a) evaluation.**  For a pairwise-orthogonal family
`ζ` with `A`-supported difference vectors `ψ_i = ζ_i − d_i ζ_0` spanning `CF(L,A)`, the
distinguished `ζ_0` itself satisfies the (7.7.a) decomposition formula at every `x ∈ A`:
`ζ_0(x) = Σ_{i≥1} star(⟨ψ_i, ζ_0⟩)/‖ζ_i‖² · ζ_i(x)`.

Same skeleton as `chiRho_decomp_proof` with `χ^ρ` replaced by `ζ_0`: the difference
`ζ_0 − candidate` has zero inner product against every spanning `ψ_j`
(`inner_psi_candidate_eq` matches the candidate's coefficients with `⟨ψ_j, ζ_0⟩`), so it
vanishes on `A` by `eq_zero_on_A_of_inner_zero` — the vanishing target need not itself be
supported, since the conclusion factors through `supportedProj`.  Paired with
`chiRho_decomp_proof` at `χ = ν ζ_0` and the (12.14) coefficient identification (`a = 0`), this
gives Peterfalvi's `ψ^ρ(x) = χ(x)`. -/
theorem zeta0_decomp_on_A [Invertible (Nat.card L : ℂ)] (A : Set L)
    (hAconj : ∀ g h : L, h * g * h⁻¹ ∈ A ↔ g ∈ A) {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆ A)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    (hspan : ClassFunction.supportedSubmodule A ≤
      Submodule.span ℂ ((fun j => ζ j - d j • ζ 0) '' {j : Fin (n + 1) | j ≠ 0}))
    {x : L} (hx : x ∈ A) :
    ζ 0 x = ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
      (star (ClassFunction.inner (ζ i - d i • ζ 0) (ζ 0)) /
        ClassFunction.inner (ζ i) (ζ i)) * ζ i x := by
  classical
  set c : Fin (n + 1) → ℂ := fun i => ClassFunction.inner (ζ i - d i • ζ 0) (ζ 0) with hc
  set cand : ClassFunction L ℂ :=
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
      (star (c i) / ClassFunction.inner (ζ i) (ζ i)) • ζ i with hcand
  have hηA : (ζ 0 - cand) x = 0 := by
    apply eq_zero_on_A_of_inner_zero A hAconj hspan
    · rintro v ⟨j, _, rfl⟩
      rw [ClassFunction.mem_supportedSubmodule]
      exact psi_support j
    · rintro v ⟨j, hj, rfl⟩
      rw [ClassFunction.inner_sub_right,
        show ClassFunction.inner (ζ j - d j • ζ 0) (ζ 0) = c j from rfl,
        inner_psi_candidate_eq ζ d horth c hnorm hj, sub_self]
    · exact hx
  have hval : ζ 0 x = cand x := by
    have h := hηA
    rw [ClassFunction.sub_apply] at h
    exact sub_eq_zero.mp h
  rw [hval, hcand, ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [ClassFunction.smul_apply]

open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (12.14), `ψ^ρ(x) = χ(x)`** (the two-sided (7.7.a) evaluation).  If the (7.7.a)
coefficients of `χ` (typically `χ = ν ζ_0`, after the (12.14) `a = 0` counting collapses
`c_{ind1H} = a − 1 = −1 = −d_{ind1H}`) are the **uniform** `c_i = ⟨ψ_i^τ, χ⟩ = −d_i` for all
`i ≥ 1`, then `χ^ρ` agrees with `ζ_0` on `A`: `χ^ρ` decomposes by `chiRho_decomp_proof`, `ζ_0`
by `zeta0_decomp_on_A`, and the source-side coefficients `⟨ψ_i, ζ_0⟩ = 0 − d_i·‖ζ_0‖² = −d_i`
match term by term. -/
theorem chiRho_apply_eq_zeta0_of_inner_tau_uniform {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ζ i - d i • ζ 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (horth : ∀ a b : Fin (n + 1), a ≠ b → ClassFunction.inner (ζ a) (ζ b) = 0)
    (hnorm : ∀ i : Fin (n + 1), ClassFunction.inner (ζ i) (ζ i) ≠ 0)
    (hζ0norm : ClassFunction.inner (ζ 0) (ζ 0) = 1)
    (hAconj : ∀ g h : L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hspan : ClassFunction.supportedSubmodule (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ≤
      Submodule.span ℂ ((fun j => ζ j - d j • ζ 0) '' {j : Fin (n + 1) | j ≠ 0}))
    (χ : ClassFunction G ℂ)
    (hc : ∀ i : Fin (n + 1), i ≠ 0 →
      ClassFunction.inner (H71.τ ⟨ζ i - d i • ζ 0, psi_support i⟩) χ = -(d i))
    {x : L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = ζ 0 x := by
  rw [chiRho_decomp_proof H71 ζ d psi_support horth hnorm hAconj hspan χ hx,
    zeta0_decomp_on_A (OddOrder.Peterfalvi.S04.supportInSubgroup A L) hAconj ζ d psi_support
      horth hnorm hspan
      (by rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi0 : i ≠ 0 := (Finset.mem_Ioi.mp hi).ne'
  have hL : ClassFunction.inner (ζ i - d i • ζ 0) (ζ 0) = -(d i) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, horth i 0 hi0, hζ0norm,
      mul_one, zero_sub]
  rw [hc i hi0, hL]

/-- **Induced irreducible characters have nonzero norm.**  `‖Ind_K^L θ‖² ≠ 0`, since
`|K|·‖Ind θ‖² = |I_L(θ)| > 0` (`card_mul_inner_self_induce_eq_card_inertia`).  Supplies the
`hnorm` hypothesis of `chiRho_decomp_proof` for the family `ζ_i = Ind θ_i` of (7.6)/(7.7.a). -/
theorem induce_norm_ne_zero (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card L : ℂ)]
    [Invertible (Nat.card ↥K : ℂ)] (θ : IrreducibleCharacter ↥K) :
    ClassFunction.inner (ClassFunction.induce K (θ : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)) ≠ 0 := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  intro h0
  have hkey := card_mul_inner_self_induce_eq_card_inertia (G := L) θ
  rw [h0, mul_zero] at hkey
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hkey.symm

/-- **An induced irreducible character is nonzero at `1`.**  `Ind_K^L θ (1) = [L:K] · θ(1)`
(`induce_apply_one`), and both factors are nonzero: `[L:K] ≠ 0` (finite index) and `θ(1)` is the
positive natural number `dim θ` (`irreducibleCharacter_apply_one_eq_pos_natCast`).  This supplies
`ζ_0(1) ≠ 0` (`hz0`), hence the well-definedness of the degree ratios `d_i = ζ_i(1)/ζ_0(1)` and the
degree relation `ζ_i(1) = d_i ζ_0(1)` for the family `ζ_i = Ind_K^L θ_i`. -/
theorem induce_apply_one_ne_zero (K : Subgroup L) [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) :
    ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L) ≠ 0 := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  rw [ClassFunction.induce_apply_one]
  obtain ⟨d, hd, hval⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine mul_ne_zero (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite) ?_
  rw [hval]
  exact Nat.cast_ne_zero.mpr hd.ne'

/-- **The induced character is real at `1`.**  `Ind_K^L θ (1) = [L:K] · θ(1)` is the natural-number
cast `[L:K] · dim θ`, so it is fixed by complex conjugation.  Supplies `star d_i = d_i` for the
degree ratios `d_i = ζ_i(1)/ζ_0(1)` in the `(7.8.a)` `Gamma_orth_nu` computation. -/
theorem induce_apply_one_star (K : Subgroup L) [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (θ : IrreducibleCharacter ↥K) :
    star (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L))
      = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  rw [ClassFunction.induce_apply_one]
  obtain ⟨d, _, hval⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [hval, ← Nat.cast_mul]
  exact star_natCast _

/-- **The induced family is pairwise orthogonal** (Peterfalvi (7.6)/(7.7.a) hypothesis).  For a
family `θ : Fin (n+1) → Irr K` of pairwise non-conjugate irreducibles, the induced characters
`ζ_i = Ind_K^L θ_i` are pairwise orthogonal — the `horth` hypothesis of `chiRho_decomp_proof`.
Direct from `inner_induce_eq_zero_of_not_conj`. -/
theorem induce_family_orthogonal (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card L :
    ℂ)]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hnc : ∀ a b : Fin (n + 1), a ≠ b →
      ∀ g : L, IrreducibleCharacter.conjBy g (θ a) ≠ θ b) :
    ∀ a b : Fin (n + 1), a ≠ b →
      ClassFunction.inner (ClassFunction.induce K (θ a : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (θ b : ClassFunction ↥K ℂ)) = 0 := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  exact fun a b hab => inner_induce_eq_zero_of_not_conj (θ a) (θ b) (hnc a b hab)

/-- **An injective induced family is pairwise orthogonal** (Peterfalvi (7.6)/(7.7.a)).  When the
map `i ↦ Ind_K^L θ_i` is injective, the `θ_i` are pairwise non-conjugate (a conjugacy would force
equal inductions, `induce_eq_induce_iff_conj`), so `induce_family_orthogonal` applies.  This is the
form of `horth` actually supplied by the enumeration of the *distinct* induced characters. -/
theorem induce_family_orthogonal_of_injective (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective
      (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) :
    ∀ a b : Fin (n + 1), a ≠ b →
      ClassFunction.inner (ClassFunction.induce K (θ a : ClassFunction ↥K ℂ))
        (ClassFunction.induce K (θ b : ClassFunction ↥K ℂ)) = 0 := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  exact induce_family_orthogonal K θ fun a b hab g hg =>
    hab (hinj ((induce_eq_induce_iff_conj (θ a) (θ b)).mpr ⟨g, hg⟩))

/-- **The difference `ψ_i = ζ_i − d_i ζ_0` is supported on `K^#`** (Peterfalvi (7.6)/(7.7.a)
hypothesis).  With `ζ = Ind_K^L θ` and the degree relation `ζ_i(1) = d_i ζ_0(1)`, the difference
`Ind θ − d • Ind θ₀` vanishes off `K` (induction from the normal `K` is `K`-supported) and at `1`
(degree relation), so its support lies in `K^# = K \ {1}` — the `psi_support` hypothesis of
`chiRho_decomp_proof`. -/
theorem induce_diff_support {K : Subgroup L} [hK : K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] (θ θ₀ : IrreducibleCharacter ↥K) (d : ℂ)
    (hd : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : L)
        = d * ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) (1 : L)) :
    (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        - d • ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ)).support ⊆ (K : Set L) \ {1} := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  have hvanish : ∀ φ : ClassFunction ↥K ℂ, ∀ x : L, x ∉ K → ClassFunction.induce K φ x = 0 := by
    intro φ x hxK
    have hconj : x ∉ ClassFunction.conjugatesInto K := by
      rw [ClassFunction.mem_conjugatesInto]
      rintro ⟨y, hy⟩
      have h := hK.conj_mem (y⁻¹ * x * y) hy y
      have he : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      exact hxK (he ▸ h)
    rw [ClassFunction.induce_apply, ← ClassFunction.induceSum_apply,
      ClassFunction.induceSum_eq_zero_of_not_conjugatesInto φ hconj, mul_zero]
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, ClassFunction.smul_apply] at hx
  refine ⟨?_, ?_⟩
  · by_contra hxK
    exact hx (by rw [hvanish _ x hxK, hvanish _ x hxK, mul_zero, sub_zero])
  · intro hx1
    rw [Set.mem_singleton_iff] at hx1
    exact hx (by rw [hx1, hd, sub_self])

omit [Fintype L] in
/-- **Peterfalvi (7.7.a), the degree-zero reduction.**  A class function in the span of the full
family `{ζ_i}` that vanishes at `1` lies in the span of the difference vectors
`{ψ_i = ζ_i − d_i ζ_0}`
(`i ≠ 0`). Writing `ψ = Σ a_i ζ_i`, the condition `ψ(1) = 0` gives `Σ a_i d_i = 0`
(`ζ_i(1) = d_i ζ_0(1)`,
`ζ_0(1) ≠ 0`), and then `ψ = Σ_{i≠0} a_i ψ_i` since the `ζ_0`-coefficient `a_0 + Σ_{i≠0} a_i d_i =
Σ_i a_i d_i = 0`.  Combined with `CF(L,A) ⊆ span
{ζ_i}` (`eq_induce_restrict_of_supported` + the family
covering all induced characters), this gives the `hspan` hypothesis of `chiRho_decomp_proof`. -/
theorem mem_span_psi_of_apply_one_zero {n : ℕ} (ζ : Fin (n + 1) → ClassFunction L ℂ)
    (d : Fin (n + 1) → ℂ) (hd : ∀ i : Fin (n + 1), ζ i (1 : L) = d i * ζ 0 (1 : L))
    (hz0 : ζ 0 (1 : L) ≠ 0) {ψ : ClassFunction L ℂ}
    (hψ : ψ ∈ Submodule.span ℂ (Set.range ζ)) (hψ1 : ψ (1 : L) = 0) :
    ψ ∈ Submodule.span ℂ ((fun i => ζ i - d i • ζ 0) '' {i : Fin (n + 1) | i ≠ 0}) := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hψ
  have hd0 : d 0 = 1 := (mul_right_cancel₀ hz0 (by rw [one_mul]; exact hd 0)).symm
  -- `Σ a_i d_i = 0` from `ψ(1) = 0`.
  have hsum0 : ∑ i, a i * d i = 0 := by
    have hv : ∑ i, a i * ζ i (1 : L) = 0 := by
      have h0 : (∑ i, a i • ζ i) (1 : L) = 0 := by rw [ha]; exact hψ1
      rw [ClassFunction.finset_sum_apply] at h0
      simpa only [ClassFunction.smul_apply] using h0
    have h1 : (∑ i, a i * d i) * ζ 0 (1 : L) = 0 := by
      rw [Finset.sum_mul, ← hv]
      exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
    exact (mul_eq_zero.mp h1).resolve_right hz0
  -- `Σ_{i≠0} a_i • (ζ_i − d_i ζ_0) = ψ`.
  have hcombo : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • (ζ i - d i • ζ 0)) = ψ := by
    have hexp : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • (ζ i - d i • ζ 0))
        = (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), a i • ζ i)
          - (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (a i * d i) • ζ 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub, smul_smul]
    rw [hexp, ← Finset.sum_smul,
      Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1))),
      ha, hd0, mul_one, hsum0, zero_sub, neg_smul]
    abel
  rw [← hcombo]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨i, Finset.ne_of_mem_erase hi, rfl⟩

/-- **Peterfalvi (7.7.a), the spanning hypothesis from a covering induced family.**  Given a family
`ζ : Fin (n+1) → CF(L)` whose values *cover* every induced irreducible `Ind_K^L θ` (`hcover`) and
satisfy the degree relation `ζ_i(1) = d_i ζ_0(1)` with `ζ_0(1) ≠ 0`, any class function `ψ`
supported inside the normal subgroup `K` and vanishing at `1` lies in the span of the difference
vectors `{ψ_i = ζ_i − d_i ζ_0 : i ≠ 0}`.

This is the `hspan` hypothesis of `chiRho_decomp_proof`: `supported_mem_span_induce_irr` places `ψ`
in the span of the induced irreducibles, `hcover` + `Submodule.span_mono` transports this to the
span of `{ζ_i}`, and `mem_span_psi_of_apply_one_zero` performs the degree-`0` reduction. -/
theorem supported_mem_span_psi (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (ζ : Fin (n + 1) → ClassFunction L ℂ) (d : Fin (n + 1) → ℂ)
    (hcover : ∀ θ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∈ Set.range ζ)
    (hdeg : ∀ i : Fin (n + 1), ζ i (1 : L) = d i * ζ 0 (1 : L)) (hz0 : ζ 0 (1 : L) ≠ 0)
    {ψ : ClassFunction L ℂ} (hsupp : ∀ y : L, y ∉ K → ψ y = 0) (hψ1 : ψ (1 : L) = 0) :
    ψ ∈ Submodule.span ℂ ((fun i => ζ i - d i • ζ 0) '' {i : Fin (n + 1) | i ≠ 0}) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  refine mem_span_psi_of_apply_one_zero ζ d hdeg hz0 ?_ hψ1
  refine Submodule.span_mono ?_ (supported_mem_span_induce_irr K ψ hsupp)
  rintro v ⟨θ, rfl⟩
  exact hcover θ

/-- **The distinct induced characters as data** (Peterfalvi (7.6) family).  Bundles the
representative family `θ : Fin (n+1) → Irr K` enumerating the *distinct* induced characters
`ζ_i = Ind_K^L θ_i`, together with the two facts `inj` (the members are distinct) and `cover`
(every induced irreducible occurs).  Packaged as data (not an `∃`) so it can be projected inside a
`Type`-valued construction such as `hypothesis76OfDade`. -/
structure DistinctInducedFamily (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] where
  /-- One less than the number of distinct induced characters. -/
  n : ℕ
  /-- A representative irreducible for each distinct induced character. -/
  θ : Fin (n + 1) → IrreducibleCharacter ↥K
  /-- The induced characters `ζ_i = Ind_K^L θ_i` are pairwise distinct. -/
  inj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
  /-- Every induced irreducible occurs among the `ζ_i`. -/
  cover : ∀ φ : IrreducibleCharacter ↥K,
    ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
      Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))

/-- **Construction of the distinct induced family.**  The members are the `Finset.equivFin` listing
of `Finset.univ.image (Ind_K^L ·)`, nonempty since the trivial character contributes; injectivity
is `equivFin.symm.injective` and covering is `Finset.mem_image`. -/
noncomputable def distinctInducedFamily (K : Subgroup L) [K.Normal] [Fintype ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)] :
    DistinctInducedFamily K := by
  classical
  haveI : Finite ↥K := Finite.of_fintype _
  let V : Finset (ClassFunction L ℂ) :=
    Finset.univ.image (fun φ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ))
  have hVne : V.Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (trivialIrreducibleCharacter ↥K))⟩
  have hn : V.card = (V.card - 1) + 1 := (Nat.succ_pred_eq_of_pos hVne.card_pos).symm
  let e : ↥V ≃ Fin ((V.card - 1) + 1) := V.equivFin.trans (finCongr hn)
  have hrep : ∀ i : Fin ((V.card - 1) + 1), ∃ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) = (e.symm i : ClassFunction L ℂ) := by
    intro i
    obtain ⟨φ, _, hφ⟩ := Finset.mem_image.mp (e.symm i).2
    exact ⟨φ, hφ⟩
  choose θ hθ using hrep
  exact
    { n := V.card - 1
      θ := θ
      inj := by
        intro i j hij
        have hval : (e.symm i : ClassFunction L ℂ) = (e.symm j : ClassFunction L ℂ) := by
          rw [← hθ i, ← hθ j]; exact hij
        exact e.symm.injective (Subtype.ext hval)
      cover := by
        intro φ
        have hmem : ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈ V :=
          Finset.mem_image_of_mem _ (Finset.mem_univ φ)
        refine ⟨e ⟨_, hmem⟩, ?_⟩
        change ClassFunction.induce K (θ (e ⟨_, hmem⟩) : ClassFunction ↥K ℂ) = _
        rw [hθ (e ⟨_, hmem⟩)]
        exact congrArg Subtype.val (Equiv.symm_apply_apply e ⟨_, hmem⟩) }

/-- **Reindexing the induced family preserves injectivity.**  For any permutation `σ`, the family
`i ↦ Ind_K^L θ_{σ i}` is injective when `i ↦ Ind_K^L θ_i` is.  Used to move the distinguished member
to index `0` (`σ = Equiv.swap 0 j`) before applying `chiRho_eq_inner_beta_induced` (which expects
the distinguished `ζ` at index `0`). -/
theorem induce_family_comp_perm_injective {K : Subgroup L} [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ} {θ : Fin (n + 1) → IrreducibleCharacter ↥K}
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (fun i => ClassFunction.induce K (θ (σ i) : ClassFunction ↥K ℂ)) :=
  hinj.comp σ.injective

/-- **Reindexing the induced family preserves covering.** -/
theorem induce_family_comp_perm_covering {K : Subgroup L} [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ} {θ : Fin (n + 1) → IrreducibleCharacter ↥K}
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ (σ i) : ClassFunction ↥K ℂ)) := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  intro φ
  obtain ⟨i, hi⟩ := hcover φ
  exact ⟨σ.symm i, by simpa using hi⟩

/-- **Placement of the distinguished and trivial members of the induced family** (the family shape
`hypothesis78OfDade` consumes).  Given the distinguished induced character `χ_dist` (in the range of
`Ind`, distinct from `Ind 1_K`), reindex the `distinctInducedFamily` so that `Ind (θ 0) = χ_dist`
(the `zetaDistinct = 0` slot) and `θ ind1H = 1_K` at some `ind1H ≠ 0` (the `Ind 1_H` slot).

The trivial character is its own induced fibre — `Ind φ = Ind 1_K ⟹ φ = 1_K` by
`induce_injective_of_inertia_stable` (the trivial char is conjugation-stable), so its
`distinctInducedFamily` representative *is* `1_K`.  The swap `0 ↔ j_dist` moves the distinguished
representative to index `0`; `j_dist ≠ j_triv` because `χ_dist ≠ Ind 1_K`. -/
theorem exists_placed_induced_family (K : Subgroup L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (χdist : ClassFunction L ℂ)
    (hχ_range : χdist ∈ Set.range (fun φ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ)))
    (hχ_ne : χdist ≠ ClassFunction.induce K
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ)) :
    ∃ (n : ℕ) (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (ind1H : Fin (n + 1)),
      ind1H ≠ 0 ∧
      ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) = χdist ∧
      θ ind1H = trivialIrreducibleCharacter ↥K ∧
      Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) ∧
      ∀ φ : IrreducibleCharacter ↥K, ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  obtain ⟨φ0, hφ0⟩ := hχ_range
  obtain ⟨jd, hjd⟩ := (distinctInducedFamily K).cover φ0
  obtain ⟨jt, hjt⟩ := (distinctInducedFamily K).cover (trivialIrreducibleCharacter ↥K)
  have htriv : (distinctInducedFamily K).θ jt = trivialIrreducibleCharacter ↥K :=
    induce_injective_of_inertia_stable
      (fun g => by
        rw [← IrreducibleCharacter.conjByPerm_apply]
        exact OddOrder.RepresentationTheory.conjByPerm_trivialIrreducibleCharacter g)
      hjt.symm
  have hjne : jd ≠ jt := by
    rintro rfl
    exact hχ_ne (hφ0.symm.trans (hjd.symm.trans hjt))
  refine ⟨(distinctInducedFamily K).n,
    fun i => (distinctInducedFamily K).θ (Equiv.swap 0 jd i), Equiv.swap 0 jd jt,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 : jt = jd := by
      have hc := congrArg (Equiv.swap 0 jd) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at hc
    exact hjne h2.symm
  · simp only [Equiv.swap_apply_left]; exact hjd.trans hφ0
  · simp only [Equiv.swap_apply_self]; exact htriv
  · exact induce_family_comp_perm_injective (distinctInducedFamily K).inj (Equiv.swap 0 jd)
  · exact induce_family_comp_perm_covering (distinctInducedFamily K).cover (Equiv.swap 0 jd)

/-- **Discharge of the (7.7.a) certificate for an induced family** (Peterfalvi (7.7.a)).  This is
the consolidation of `chiRho_decomp_proof` for the concrete family `ζ_i = Ind_K^L θ_i`: the
orthogonality (`horth`) and spanning (`hspan`) hypotheses of the basis argument are *derived* from
the induced-family data — injectivity `hinj` (distinct members) and covering `hcover` (every induced
irreducible is in the family) — via `induce_family_orthogonal_of_injective`, `induce_norm_ne_zero`,
and `supported_mem_span_psi`.  The only remaining inputs are the geometric facts that `A` (where
`χ^ρ` is read off) sits inside `K^#`: `hAK_off` (`A`-support lies in `K`), `hA_one` (`1 ∉ A`), and
the conjugation-invariance `hAconj`.

When `K = H.subgroupOf L` for the normal subgroup `H ⊴ L` of Peterfalvi's `Hypothesis76` and
`A = H \ {1}`, all of `hinj`/`hcover` come from `exists_distinct_induced_family`,
`hdeg`/`psi_support`
from `induce_apply_one_ne_zero`/`induce_diff_support`, and `hAK_off`/`hA_one`/`hAconj` from
`Subgroup.mem_subgroupOf` + the normality of `H`.  Thus the `Hypothesis76.chiRho_decomp` certificate
is constructible from `(7.1)` data alone, with no certificate assumed. -/
theorem chiRho_decomp_induced {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (χ : ClassFunction G ℂ) {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x =
      ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)),
        (star (ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ) /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) *
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) x := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  refine chiRho_decomp_proof H71 (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d
    psi_support (induce_family_orthogonal_of_injective K θ hinj)
    (fun i => induce_norm_ne_zero K (θ i)) hAconj ?_ χ hx
  intro ψ hψ
  refine supported_mem_span_psi K (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d
    hcover hdeg (induce_apply_one_ne_zero K (θ 0)) ?_ ?_
  · intro y hyK
    by_contra hne
    exact hyK (hAK_off y (hψ (ClassFunction.mem_support.mpr hne)))
  · by_contra hne
    exact hA_one (hψ (ClassFunction.mem_support.mpr hne))

open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (12.14), `ψ^ρ(x) = χ(x)` for the induced family** (the two-sided (7.7.a)
evaluation, `Ind`-family form).  Same family hypotheses as `chiRho_decomp_induced`, plus the
uniform coefficient identification `⟨ψ_i^τ, χ⟩ = −d_i` (available for `χ = ν ζ_0` after the
(12.14) `a = 0` counting `betaDecompOfDade_a_eq_zero`) and the norm-one normalization
`‖Ind θ_0‖² = 1` (Frobenius kernel: `inner_self_induce_eq_one_of_frobeniusGroup`): then
`χ^ρ(x) = Ind θ_0 (x)` for every `x ∈ A`.  The spanning input of the two-sided evaluation is
discharged by `supported_mem_span_psi` exactly as in `chiRho_decomp_induced`. -/
theorem chiRho_apply_eq_zeta0_induced {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i : Fin (n + 1), i ≠ 0 →
      ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ
        = -(d i))
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) x := by
  have : Fintype ↥K := Fintype.ofFinite ↥K
  refine chiRho_apply_eq_zeta0_of_inner_tau_uniform H71
    (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d psi_support
    (induce_family_orthogonal_of_injective K θ hinj)
    (fun i => induce_norm_ne_zero K (θ i)) hζ0norm hAconj ?_ χ hc hx
  intro ψ hψ
  refine supported_mem_span_psi K (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) d
    hcover hdeg (induce_apply_one_ne_zero K (θ 0)) ?_ ?_
  · intro y hyK
    by_contra hne
    exact hyK (hAK_off y (hψ (ClassFunction.mem_support.mpr hne)))
  · by_contra hne
    exact hA_one (hψ (ClassFunction.mem_support.mpr hne))

/-- **`H.subgroupOf L` is normal when `L` conjugation-normalizes `H`.**  If every `l ∈ L`
conjugates `H ≤ G` into itself (the `H_normal_in_L` field of `Hypothesis76`), then `H.subgroupOf L`
is a normal subgroup of `↥L`.  Direct check of the `conj_mem` field via `Subgroup.mem_subgroupOf`
and the coercion `↑(g·n·g⁻¹) = ↑g·↑n·↑g⁻¹`. -/
theorem subgroupOf_normal_of_conj {G : Type*} [Group G] {H L : Subgroup G}
    (hconj : ∀ (g : ↥L) {h : G}, h ∈ H → (g : G) * h * (g : G)⁻¹ ∈ H) :
    (H.subgroupOf L).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj g hn

section SharpSupport

variable {G : Type*} [Group G] {L : Subgroup G}

/-- Membership in the sharp support, phrased on `G`: `x ∈ supportInSubgroup (H \ {1}) L`
iff `(x : G) ∈ H` and `(x : G) ≠ 1`. -/
theorem mem_supportInSubgroup_sharp_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) (x : ↥L) :
    x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔ ((x : G) ∈ H ∧ (x : G) ≠ 1) := by
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hAH]
  simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]

/-- Membership in the sharp support, phrased on the subgroup side `K = H.subgroupOf L`:
`x ∈ supportInSubgroup (H \ {1}) L` iff `x ∈ H.subgroupOf L` and `x ≠ 1`. -/
theorem mem_supportInSubgroup_sharp_subgroupOf_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) (x : ↥L) :
    x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔ (x ∈ H.subgroupOf L ∧ x ≠ 1) := by
  rw [mem_supportInSubgroup_sharp_iff H hAH x, Subgroup.mem_subgroupOf]
  exact and_congr_right fun _ => not_congr OneMemClass.coe_eq_one

/-- The sharp support is contained in `K = H.subgroupOf L`. -/
theorem supportInSubgroup_sharp_subset_subgroupOf (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) {x : ↥L}
    (hx : x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L) : x ∈ H.subgroupOf L :=
  ((mem_supportInSubgroup_sharp_subgroupOf_iff H hAH x).mp hx).1

/-- The identity is not in the sharp support. -/
theorem one_not_mem_supportInSubgroup_sharp (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1}) :
    (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L := fun hx =>
  ((mem_supportInSubgroup_sharp_subgroupOf_iff H hAH 1).mp hx).2 rfl

/-- The sharp support is invariant under `L`-conjugation (from normality of `H` in `L`). -/
theorem supportInSubgroup_sharp_conj_mem_iff (H : Subgroup G) {A : Set G}
    (hAH : A = (H : Set G) \ {1})
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H) (g h : ↥L) :
    h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
  have hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  rw [mem_supportInSubgroup_sharp_subgroupOf_iff H hAH,
    mem_supportInSubgroup_sharp_subgroupOf_iff H hAH]
  refine and_congr ?_ ?_
  · constructor
    · intro hm
      have hc := hKnorm.conj_mem _ hm h⁻¹
      have heq : h⁻¹ * (h * g * h⁻¹) * (h⁻¹)⁻¹ = g := by group
      rwa [heq] at hc
    · intro hm; exact hKnorm.conj_mem _ hm h
  · rw [ne_eq, ne_eq, mul_inv_eq_one, mul_eq_left]

end SharpSupport

/-- **Construction of `Hypothesis76` from `(7.1)` data** (Peterfalvi (7.6)/(7.7.a)).  Given the
Dade-isometry data of `(7.1)` (`H71` together with `hτ : IsDadeIsometry H71.τ`) and a normal
subgroup `H ⊴ L` with `A = H \ {1}`, the entire `Hypothesis76` structure — *including* the
`(7.7.a)` certificate `chiRho_decomp` — is constructed with **no certificate assumed**.

The induced family `ζ_i = Ind_{H}^L θ_i` is the `exists_distinct_induced_family` enumeration of the
distinct induced characters, the degree ratios are `d_i = ζ_i(1)/ζ_0(1)`, and `chiRho_decomp` is
discharged by `chiRho_decomp_induced` (its `hinj`/`hcover` from the enumeration, the geometric
`A = H^#` inputs from `Subgroup.mem_subgroupOf` + normality of `H`).  This realizes the issue-1013
goal: `Hypothesis76` (hence the `(7.7.a)` content) is constructible from coherence/`(7.1)` data
alone. -/
noncomputable def hypothesis76OfFamily
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))) :
    Hypothesis76 G A L :=
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  { hyp71 := H71
    isDadeIsometry := hτ
    H := H
    H_le_L := hHL
    H_normal_in_L := hHnorm
    A_eq_H_sharp := hAH
    n := n
    -- The family and degree ratios are *literal* record fields (term-mode construction), so
    -- `hypothesis76OfFamily_zeta` below is `rfl` — consumers can read the induced-ness of the
    -- family definitionally (the Peterfalvi (13.5.a) integrality needs it).
    zeta := fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
    d := fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
      / ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    zeta_eq_zero_of_not_mem_H := fun _ x hxH =>
      ClassFunction.induce_eq_zero_of_not_mem_normal _ (by rwa [Subgroup.mem_subgroupOf])
    zeta_one_eq_d_mul := fun i => by
      have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
        induce_apply_one_ne_zero _ (θ 0)
      field_simp
    psi_support := fun i => by
      have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
        induce_apply_one_ne_zero _ (θ 0)
      have hdeg : ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
          = (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
              / ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
            * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) := by
        field_simp
      refine (induce_diff_support (θ i) (θ 0) _ hdeg).trans ?_
      intro x hx
      rw [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hx
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hAH]
      simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
      refine ⟨hx.1, fun h1 => hx.2 (Subtype.ext h1)⟩
    zeta_injective := hinj
    zeta_induced := fun i => ⟨θ i, by congr!; exact Subsingleton.elim _ _⟩
    zeta_family_cover := fun φ => by
      obtain ⟨i, hi⟩ := hcover φ
      exact ⟨i, hi.trans (by congr!; exact Subsingleton.elim _ _)⟩
    chiRho_decomp := by
      intro χ x hx
      have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
        induce_apply_one_ne_zero _ (θ 0)
      have hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
          = (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
              / ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
            * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) := by
        intro i
        field_simp
      have hpsupp : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
              / ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
            • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
        intro i
        refine (induce_diff_support (θ i) (θ 0) _ (hdeg i)).trans ?_
        intro y hy
        rw [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hy
        rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hAH]
        simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
        refine ⟨hy.1, fun h1 => hy.2 (Subtype.ext h1)⟩
      exact chiRho_decomp_induced H71 (H.subgroupOf L) θ _ hpsupp hinj hcover hdeg
        (fun g h => supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm g h)
        (fun _ => supportInSubgroup_sharp_subset_subgroupOf H hAH)
        (one_not_mem_supportInSubgroup_sharp H hAH) χ hx }

/-- **`Hypothesis76` from `(7.1)` data with the trivial-base normalization**: the
`distinctInducedFamily` enumeration reindexed (by a transposition) so that
`ζ₀ = Ind_H^L 1_H` — the induced principal character sits at the base index `0`
(`hypothesis76OfDadeTrivialBase_zeta_zero`).  The (13.5)/(13.6) distinguished-index machinery
(`exists_lambda_index`) needs the distinguished `λ = Ind_H^L θ` (`P ⊄ Ker θ`, in particular
`θ ≠ 1_H`) to sit at a *positive* index; pinning the base to `θ = 1_H` guarantees it. -/
noncomputable def hypothesis76OfDadeTrivialBase
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1}) :
    Hypothesis76 G A L :=
  haveI _hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  hypothesis76OfFamily H71 hτ H hHL hHnorm hAH
    (fun i => (distinctInducedFamily (H.subgroupOf L)).θ
      (Equiv.swap 0 (Classical.choose ((distinctInducedFamily (H.subgroupOf L)).cover
        (trivialIrreducibleCharacter ↥(H.subgroupOf L)))) i))
    (induce_family_comp_perm_injective (distinctInducedFamily (H.subgroupOf L)).inj _)
    (induce_family_comp_perm_covering (distinctInducedFamily (H.subgroupOf L)).cover _)

/-- **`Hypothesis76` from `(7.1)` data with a chosen base**: the `distinctInducedFamily`
enumeration reindexed (by a transposition) so that `ζ₀ = Ind_H^L φ₀` for the *given* `φ₀` — the
general form of the trivial-base normalization.  Peterfalvi re-chooses the (7.7) base per
application ((7.8.b) "we use (7.7) with `ζ₀ ∈ 𝒮 − {ζ}`"; (13.5) takes `ζ₀ ∈ 𝒮₁`): the (13.5)
coefficient computations need a **`P`-nonkernel** base (issue 2035 更新 #22 — with the trivial
base the τ₁-conversion `(ζ_i − ζ₀)^{τ₁} = Ind(ζ_i − ζ₀)` is not available, `Ind 1_H ∉ ℤ[𝒮]`),
which this builder provides at `φ₀ := θ_{μ_{j₀}}` (the `μ`-column source,
`mu_j_isIndPC_not_ker`). -/
noncomputable def hypothesis76OfDadeBase
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    (φ₀ :
      haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
      IrreducibleCharacter ↥(H.subgroupOf L)) :
    Hypothesis76 G A L :=
  haveI _hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  hypothesis76OfFamily H71 hτ H hHL hHnorm hAH
    (fun i => (distinctInducedFamily (H.subgroupOf L)).θ
      (Equiv.swap 0 (Classical.choose ((distinctInducedFamily (H.subgroupOf L)).cover φ₀)) i))
    (induce_family_comp_perm_injective (distinctInducedFamily (H.subgroupOf L)).inj _)
    (induce_family_comp_perm_covering (distinctInducedFamily (H.subgroupOf L)).cover _)

end OddOrder.Peterfalvi.S09.Cert


