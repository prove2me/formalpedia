-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry
-- name    : OddOrder_Peterfalvi_S05_SigmaIsometry
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:57:36.813985+00:00
-- url     : https://prove2.me/theorems/b23a8aae-addc-40c9-b6c4-3ff95ccfeaf7
-- title:
--   Peterfalvi (3.2): the map $\sigma$ and its properties (tail)
-- statement:
--   The final part of the Peterfalvi §3 development of the isometry $\sigma:\mathrm{CF}(W)\to\mathrm{CF}(G)$ of (3.2), defined by $\omega^\sigma=\chi$ on the basis of irreducible characters.
--
--   Main definitions: `chiFam` (a fixed choice of the (3.5) orthonormal family $\chi_{ij}$), `sigma` (Peterfalvi (3.2)) and `induceLinear` ($\mathrm{Ind}_W^G$ as a $\mathbb{C}$-linear map). Results include `sigma_apply_of_mem_V` ((3.2)(c)) and `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` ((3.2)(d)).
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_SigmaIsometry.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_SigmaIsometry.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_Isometry32

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

/-- A fixed choice of the `(3.5)` orthonormal family `(χ_{ij})` (indexed by `Ĉ₁ × Ĉ₂`), extracted
from `exists_chiFamily`.  `σ` is built from this. -/
noncomputable def chiFam (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) → ClassFunction G ℂ :=
  (hyp.exists_chiFamily hVeq app).choose

open scoped Classical in
theorem chiFam_spec (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    hyp.chiFam hVeq app (1, 1) = trivialClassFunction G ∧
      (∀ pq, hyp.chiFam hVeq app pq ∈ ZIrr G) ∧
      (∀ a b, ClassFunction.inner (hyp.chiFam hVeq app a) (hyp.chiFam hVeq app b)
        = if a = b then 1 else 0) ∧
      ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
        p ≠ 1 → q ≠ 1 → app.tau.toDadeMap (hyp.alpha hVeq p q)
          = trivialClassFunction G - hyp.chiFam hVeq app (p, 1) - hyp.chiFam hVeq app (1, q)
            + hyp.chiFam hVeq app (p, q) :=
  (hyp.exists_chiFamily hVeq app).choose_spec

/-- **Peterfalvi (3.2)**, the map: the linear `σ : CF(W) → CF(G)` defined by `ω^σ = χ` on the
basis `Irr(W)` (`(3.3)`) via the chosen `(3.5)` family (`Module.Basis.constr`).  Linearity is
automatic; the isometry property and (a)-(d) are proved separately. -/
noncomputable def sigma (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    ClassFunction hyp.W ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (irreducibleCharacterBasis (G := hyp.W)).constr ℂ
    fun ω => hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω)

/-- The defining property of `σ` on the basis `Irr(W)`: `ω^σ = χ` at the matching index pair. -/
theorem sigma_irreducibleCharacter (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω) := by
  conv_lhs => rw [← irreducibleCharacterBasis_apply (G := hyp.W) ω]
  exact (irreducibleCharacterBasis (G := hyp.W)).constr_basis ℂ _ ω

/-- The Gram matrix of `σ` on the basis matches that of `Irr(W)`: `⟨ω^σ, ω'^σ⟩ = ⟨ω, ω'⟩`.  Both
sides are `δ_{ω,ω'}` — the `χ`-family is orthonormal (`chiFam_spec`) and `omegaIrrEquiv.symm` is
injective, while `Irr(W)` is orthonormal (`irreducibleCharacter_inner_eq_ite`). -/
theorem sigma_inner_irreducibleCharacter (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω ω' : IrreducibleCharacter hyp.W) :
    ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
        (hyp.sigma hVeq app (ω' : ClassFunction hyp.W ℂ))
      = ClassFunction.inner (ω : ClassFunction hyp.W ℂ) (ω' : ClassFunction hyp.W ℂ) := by
  rw [sigma_irreducibleCharacter, sigma_irreducibleCharacter, (hyp.chiFam_spec hVeq app).2.2.1,
    irreducibleCharacter_inner_eq_ite]
  by_cases h : ω = ω'
  · rw [if_pos h, if_pos (congrArg _ h)]
  · rw [if_neg h, if_neg fun hh => h (hyp.omegaIrrEquiv.symm.injective hh)]

/-- **Peterfalvi (3.2)** (isometry): `σ` preserves the class-function inner product,
`⟨α^σ, β^σ⟩ = ⟨α, β⟩`.  Expand `α, β` in the `Irr(W)` basis; both inner products become the same
double sum `∑_{ω,ω'} r_ω · conj(s_{ω'}) · ⟨·,·⟩`, and the per-pair Gram entries agree by
`sigma_inner_irreducibleCharacter`. -/
theorem sigma_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (x y : ClassFunction hyp.W ℂ) :
    ClassFunction.inner (hyp.sigma hVeq app x) (hyp.sigma hVeq app y)
      = ClassFunction.inner x y := by
  classical
  have : Finite hyp.W := Finite.of_fintype _
  have : Finite (IrreducibleCharacter hyp.W) := finite_irreducibleCharacter
  have : Fintype (IrreducibleCharacter hyp.W) := Fintype.ofFinite _
  set b := irreducibleCharacterBasis (G := hyp.W) with hb
  have hbω : ∀ ω, b ω = (ω : ClassFunction hyp.W ℂ) := fun ω => by
    rw [hb]; exact irreducibleCharacterBasis_apply ω
  have hσ : ∀ z, hyp.sigma hVeq app z = ∑ ω, b.repr z ω • hyp.sigma hVeq app (b ω) := fun z => by
    conv_lhs => rw [← b.sum_repr z]
    rw [map_sum]; exact Finset.sum_congr rfl fun ω _ => map_smul _ _ _
  -- both inner products expand to the same double sum over the (matching) Gram entries
  have hL := inner_sum_smul_sum (fun ω => b.repr x ω) (fun ω => b.repr y ω)
    (fun ω => hyp.sigma hVeq app (b ω))
  have hR := inner_sum_smul_sum (fun ω => b.repr x ω) (fun ω => b.repr y ω) (fun ω => b ω)
  rw [hσ x, hσ y, hL]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, hR]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun ω' _ => ?_
  rw [hbω ω, hbω ω', hyp.sigma_inner_irreducibleCharacter hVeq app ω ω']

/-- `omegaProdEquiv.symm` inverts `omegaProdChar`: `(ω_{i0}·ω_{0j})` has index pair `(χ₁, χ₂)`. -/
theorem omegaProdEquiv_symm_omegaProdChar (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdEquiv.symm (hyp.omegaProdChar χ₁ χ₂) = (χ₁, χ₂) := by
  rw [show hyp.omegaProdChar χ₁ χ₂ = hyp.omegaProdEquiv (χ₁, χ₂) from rfl, Equiv.symm_apply_apply]

/-- **`omegaProdChar` reconstructs any linear character of `W`**: the product `ω_{i0}·ω_{0j}` of the
`W₁`- and `W₂`-restrictions `χ_k = ξ|_{W_k}` recovers `ξ`.  This is the witness of
`omegaProdChar_surjective`, extracted as a reusable identity (uses `W = W₁ × W₂`,
`wProj1_mul_wProj2`). -/
theorem omegaProdChar_comp_subtype (hyp : TICyclicHypothesis G) (ξ : hyp.W →* ℂˣ) :
    hyp.omegaProdChar (ξ.comp (hyp.W1.subgroupOf hyp.W).subtype)
        (ξ.comp (hyp.W2.subgroupOf hyp.W).subtype) = ξ := by
  ext w
  simp only [omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← map_mul]
  congr 1
  have e1 : (↑(hyp.wFst w) : hyp.W) = hyp.wProj1 w := by rw [wProj1_apply, wFst_apply]
  have e2 : (↑(hyp.wSnd w) : hyp.W) = hyp.wProj2 w := by rw [wProj2_apply, wSnd_apply]
  rw [e1, e2, wProj1_mul_wProj2]

/-- **`omegaProdEquiv.symm` extracts the `W₁`/`W₂`-restrictions**: for any linear `ξ : W →* ℂˣ`,
`omegaProdEquiv.symm ξ = (ξ|_{W₁}, ξ|_{W₂})`.  The §10 (10.6) column-structure argument uses this to
read off the product index `(ρ, κ)` of a transported `ω_{ij}`: each factor of a product character
contributes to exactly one component. -/
theorem omegaProdEquiv_symm_eq (hyp : TICyclicHypothesis G) (ξ : hyp.W →* ℂˣ) :
    hyp.omegaProdEquiv.symm ξ
      = (ξ.comp (hyp.W1.subgroupOf hyp.W).subtype, ξ.comp (hyp.W2.subgroupOf hyp.W).subtype) := by
  conv_lhs => rw [← hyp.omegaProdChar_comp_subtype ξ]
  exact hyp.omegaProdEquiv_symm_omegaProdChar _ _

/-- `σ` on a single linear character: `(ω(ξ))^σ = χ` at the index pair `omegaProdEquiv.symm ξ`. -/
theorem sigma_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) (ξ : hyp.W →* ℂˣ) :
    hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ) := by
  rw [sigma_irreducibleCharacter]
  congr 1
  change hyp.omegaProdEquiv.symm (hyp.omegaEquiv.symm (hyp.omega ξ)) = hyp.omegaProdEquiv.symm ξ
  congr 1
  exact hyp.omegaEquiv.symm_apply_apply ξ

/-- **Peterfalvi (3.2)(b)**: `1_W^σ = 1_G`.  The trivial character is `ω(1)` at index `(1, 1)`,
and `χ_{00} = 1_G` (`chiFam_spec`). -/
theorem sigma_trivial (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp) :
    hyp.sigma hVeq app (trivialClassFunction hyp.W) = trivialClassFunction G := by
  have h1W : trivialClassFunction hyp.W = (hyp.omega 1 : ClassFunction hyp.W ℂ) := by
    ext w; simp
  rw [h1W, sigma_omega,
    show (1 : hyp.W →* ℂˣ) = hyp.omegaProdChar 1 1 from hyp.omegaProdChar_one_one.symm,
    omegaProdEquiv_symm_omegaProdChar, (hyp.chiFam_spec hVeq app).1]

/-- **Peterfalvi (3.2)(a)** on the basis `α_{ij}`: `α_{ij}^σ = Ind_W^G α_{ij}` for `i, j ≥ 1`.
Expand `α_{ij} = ω_{00} - ω_{i0} - ω_{0j} + ω_{ij}` (`alphaCF_eq_omega_combination`), apply `σ`
term-by-term (`sigma_omega`), and recognise the result as the `(3.5)` `Ind` relation
(`chiFam_spec`). -/
theorem sigma_alphaCF (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    (hp : p ≠ 1) (hq : q ≠ 1) :
    hyp.sigma hVeq app (hyp.alphaCF p q) = app.tau.toDadeMap (hyp.alpha hVeq p q) := by
  rw [alphaCF_eq_omega_combination,
    -- normalise each `ω`-argument to `omegaProdChar` form (the product term first, as it is `rfl`)
    show p.comp hyp.wFst * q.comp hyp.wSnd = hyp.omegaProdChar p q from rfl,
    show (1 : hyp.W →* ℂˣ) = hyp.omegaProdChar 1 1 from hyp.omegaProdChar_one_one.symm,
    show p.comp hyp.wFst = hyp.omegaProdChar p 1 from (hyp.omegaProdChar_one_right p).symm,
    show q.comp hyp.wSnd = hyp.omegaProdChar 1 q from (hyp.omegaProdChar_one_left q).symm,
    map_add, map_sub, map_sub, sigma_omega, sigma_omega, sigma_omega, sigma_omega,
    omegaProdEquiv_symm_omegaProdChar, omegaProdEquiv_symm_omegaProdChar,
    omegaProdEquiv_symm_omegaProdChar, omegaProdEquiv_symm_omegaProdChar,
    (hyp.chiFam_spec hVeq app).1]
  exact ((hyp.chiFam_spec hVeq app).2.2.2 p q hp hq).symm

/-- The basis `alphaBasis` evaluated at an index pair: `alphaBasis (p, q) = α_{pq}`
(`coe_basisOfLinearIndependentOfCardEqFinrank` for the family `alphaLinearIndependent`). -/
theorem alphaBasis_apply (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    (pq : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} ×
        {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) :
    hyp.alphaBasis hVeq pq = hyp.alpha hVeq pq.1.1 pq.2.1 := by
  classical
  have : Finite G := Finite.of_fintype G
  let : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  let : Fintype {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := Fintype.ofFinite _
  have := hyp.nonempty_charNeOne hyp.W1_le_W hyp.W1_nontrivial
  have := hyp.nonempty_charNeOne hyp.W2_le_W hyp.W2_nontrivial
  have h : ⇑(hyp.alphaBasis hVeq) = fun p => hyp.alpha hVeq p.1.1 p.2.1 := by
    unfold TICyclicHypothesis.alphaBasis
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact congrFun h pq

/-- `Ind_W^G` packaged as a `ℂ`-linear map `CF(W) →ₗ[ℂ] CF(G)` (linearity from `induce_add` /
`induce_smul`).  Used to phrase (3.2)(a) as an equality of linear maps on the basis `(α_{ij})`. -/
noncomputable def induceLinear (hyp : TICyclicHypothesis G) [Invertible (Nat.card hyp.W : ℂ)] :
    ClassFunction hyp.W ℂ →ₗ[ℂ] ClassFunction G ℂ where
  toFun := ClassFunction.induce hyp.W
  map_add' := ClassFunction.induce_add hyp.W
  map_smul' c θ := ClassFunction.induce_smul hyp.W c θ

@[simp] theorem induceLinear_apply (hyp : TICyclicHypothesis G) [Invertible (Nat.card hyp.W : ℂ)]
    (θ : ClassFunction hyp.W ℂ) :
    hyp.induceLinear θ = ClassFunction.induce hyp.W θ := rfl

/-- **Peterfalvi (3.2)(a)** (full form): on all of `CF(W, V)`, `σ` agrees with the Dade map `τ`,
`α^σ = τ(α) = Ind_W^G α`.  Both `α ↦ σ(↑α)` and `α ↦ Ind_W^G ↑α` are `ℂ`-linear on `CF(W, V)` and
agree on the basis `(α_{ij})` (`alphaBasis`) — LHS by `sigma_alphaCF`, RHS by `tau_eq_induce`
(`τ = Ind`) — hence agree everywhere. -/
theorem sigma_eq_tau (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV ℂ hyp) :
    hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ) = app.tau.toDadeMap α := by
  -- the two `ℂ`-linear maps `CF(W,V) →ₗ CF(G)` (`σ ∘ ↪` and `Ind ∘ ↪`) agree on the basis `α_{ij}`
  have key : ((hyp.sigma hVeq app).comp (Submodule.subtype _) :
        SupportedOnV ℂ hyp →ₗ[ℂ] ClassFunction G ℂ)
      = hyp.induceLinear.comp (Submodule.subtype _) := by
    refine Module.Basis.ext (hyp.alphaBasis hVeq) (fun pq => ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hyp.alphaBasis_apply hVeq,
      induceLinear_apply, hyp.alpha_coe]
    rw [hyp.sigma_alphaCF hVeq app pq.1.1 pq.2.1 pq.1.2 pq.2.2]
    -- LHS `= τ(α_{pq})` (now); RHS `Ind ↑α_{pq} = τ(α_{pq})` by `tau_eq_induce` (`τ = Ind`)
    have h := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq pq.1.1 pq.2.1)
    rw [hyp.alpha_coe] at h
    exact h
  have hα := DFunLike.congr_fun key α
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hα
  rw [hα, induceLinear_apply]
  exact (hyp.tau_eq_induce app.tau.toDadeIsometryData α).symm

/-- **Peterfalvi (3.2)** (virtual characters): `σ` maps `ZIrr(W)` into `ZIrr(G)`.  Each `Irr(W)`
basis vector maps to a member of the `(3.5)` family `χ ∈ ZIrr(G)` (`chiFam_spec`); a `ℤ`-combination
maps to a `ℤ`-combination, which stays in the `ℤ`-submodule `ZIrr(G)` (`span` induction). -/
theorem sigma_mem_ZIrr (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {z : ClassFunction hyp.W ℂ} (hz : z ∈ ZIrr hyp.W) :
    hyp.sigma hVeq app z ∈ ZIrr G := by
  rw [ZIrr_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
      have hx' : hyp.sigma hVeq app x
          = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ⟨x, hx⟩) :=
        hyp.sigma_irreducibleCharacter hVeq app ⟨x, hx⟩
      rw [hx']; exact (hyp.chiFam_spec hVeq app).2.1 _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih => rw [map_zsmul]; exact (ZIrr G).smul_mem a ih

/-- **(1.3)(a) → (3.2) bridge** (vanishing on `V`): a class function `f` on `W` orthogonal to
every `α_{ij}` (`i, j ≥ 1`) vanishes on `V`.  The `α_{ij}` are a basis of `CF(W, V)` ((3.4)), so the
linear functional `⟨·, f⟩` is zero on all of `CF(W, V)`; the (1.3)(a) engine
(`eq_zero_of_mem_of_inner_supported_eq_zero`) then forces `f|_V = 0`.  (`V` is conjugation-closed in
the abelian `W`.) -/
theorem vanishOnV_of_inner_alphaCF (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff)
    {f : ClassFunction hyp.W ℂ}
    (hf : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q) f = 0)
    {v : G} (hv : v ∈ hyp.V) : f ⟨v, hyp.V_subset_W hv⟩ = 0 := by
  classical
  have : IsMulCommutative ↥hyp.W := hyp.isMulCommutative_W
  -- `⟨·, f⟩` is zero on `CF(W, V)`: zero on the basis `α_{ij}` (so on the whole submodule)
  have hL0 : (innerLeftFunctional f).comp (Submodule.subtype
      (ClassFunction.supportedSubmodule (G := ↥hyp.W)
        (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W))) = 0 := by
    refine Module.Basis.ext (hyp.alphaBasis hVeq) (fun pq => ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      innerLeftFunctional_apply, hyp.alphaBasis_apply hVeq, hyp.alpha_coe]
    exact hf pq.1.1 pq.2.1 pq.1.2 pq.2.2
  refine eq_zero_of_mem_of_inner_supported_eq_zero
    (A := OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W) (fun x _ h => ?_)
    (fun φ hφ => ?_) ?_
  · -- `V` is conjugation-closed in the abelian `W`, so `h * x * h⁻¹ = x`
    have hxx : h * x * h⁻¹ = x := by rw [mul_comm' h x, mul_assoc, mul_inv_cancel, mul_one]
    rw [hxx]; assumption
  · -- orthogonal to every `φ ∈ CF(W, V)` via `hL0`
    have := DFunLike.congr_fun hL0 ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
    simpa using this
  · rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hv

open scoped Classical in
/-- **Peterfalvi (3.2)(c)** on a basis character: `ω^σ(v) = ω(v)` for `ω ∈ Irr(W)` and `v ∈ V`.
By the bridge `vanishOnV_of_inner_alphaCF` it suffices that `f = Res_W(ω^σ) - ω ⊥ α_{ij}`; this
holds because `⟨α_{ij}, Res_W(ω^σ)⟩ = ⟨Ind α_{ij}, ω^σ⟩ = ⟨α_{ij}^σ, ω^σ⟩ = ⟨α_{ij}, ω⟩`
(Frobenius `+` (a) `+` isometry). -/
theorem sigma_apply_irreducibleCharacter_of_mem_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) {v : G} (hv : v ∈ hyp.V) :
    hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) v
      = (ω : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := by
  have hkey : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q)
        (ClassFunction.restrict hyp.W (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
          - (ω : ClassFunction hyp.W ℂ)) = 0 := by
    intro p q hp hq
    have hinduce : ClassFunction.induce hyp.W (hyp.alphaCF p q)
        = hyp.sigma hVeq app (hyp.alphaCF p q) := by
      have h1 := hyp.sigma_eq_tau hVeq app (hyp.alpha hVeq p q)
      have h2 := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq p q)
      rw [hyp.alpha_coe] at h1 h2
      exact h2.symm.trans h1.symm
    rw [ClassFunction.inner_sub_right, ← ClassFunction.inner_induce_eq_inner_restrict, hinduce,
      hyp.sigma_inner hVeq app, sub_self]
  have hzero := hyp.vanishOnV_of_inner_alphaCF hVeq hkey hv
  rw [ClassFunction.sub_apply, ClassFunction.restrict_apply] at hzero
  exact sub_eq_zero.mp hzero

open scoped Classical in
/-- **Peterfalvi (3.2)(c)**: `α^σ(x) = α(x)` for every `α ∈ CF(W)` and `x ∈ V`.  Both sides are
`ℂ`-linear in `α`, and they agree on the orthonormal basis `Irr(W)`
(`sigma_apply_irreducibleCharacter_of_mem_V`), hence everywhere. -/
theorem sigma_apply_of_mem_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : ClassFunction hyp.W ℂ) {v : G} (hv : v ∈ hyp.V) :
    hyp.sigma hVeq app α v = α ⟨v, hyp.V_subset_W hv⟩ := by
  classical
  have : Finite hyp.W := Finite.of_fintype _
  have : Finite (IrreducibleCharacter hyp.W) := finite_irreducibleCharacter
  have : Fintype (IrreducibleCharacter hyp.W) := Fintype.ofFinite _
  -- the linear functional `D α = α^σ(v) - α(v)` vanishes on the basis `Irr(W)`, hence is `0`
  let D : ClassFunction hyp.W ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun α => hyp.sigma hVeq app α v - α ⟨v, hyp.V_subset_W hv⟩
      map_add' := fun a b => by
        simp only [map_add, ClassFunction.add_apply]; ring
      map_smul' := fun c a => by
        simp only [map_smul, ClassFunction.smul_apply, RingHom.id_apply, smul_eq_mul]; ring }
  have hD0 : D = 0 := by
    refine Module.Basis.ext (irreducibleCharacterBasis (G := hyp.W)) (fun ω => ?_)
    change hyp.sigma hVeq app (irreducibleCharacterBasis (G := hyp.W) ω) v
        - (irreducibleCharacterBasis (G := hyp.W) ω) ⟨v, hyp.V_subset_W hv⟩ = 0
    rw [irreducibleCharacterBasis_apply,
      hyp.sigma_apply_irreducibleCharacter_of_mem_V hVeq app ω hv, sub_self]
  have hDα : hyp.sigma hVeq app α v - α ⟨v, hyp.V_subset_W hv⟩ = 0 := DFunLike.congr_fun hD0 α
  exact sub_eq_zero.mp hDα

open scoped Classical in
/-- **Peterfalvi (3.2)(d)**: any `χ ∈ CF(G)` orthogonal to every `χ_{ij}` (the images of the basis
`Irr(W)` under `σ`) vanishes on `V`.  Since `σ(α_{ij}) = 1_G - χ_{i0} - χ_{0j} + χ_{ij}` ((3.5)) and
`1_G = χ_{00}`, all four terms are orthogonal to `χ`, so `⟨α_{ij}, Res_W χ⟩ = ⟨σ(α_{ij}), χ⟩ = 0`
(Frobenius `+` (a)); the bridge then gives `χ|_V = 0`.  An irreducible character of `G` not in the
image of `σ` is in particular orthogonal to all `χ_{ij}`, so this is the stated form of (d). -/
theorem eq_zero_of_mem_V_of_inner_chiFam_eq_zero (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ}
    (hχ : ∀ (a : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      ClassFunction.inner χ (hyp.chiFam hVeq app (a, b)) = 0)
    {v : G} (hv : v ∈ hyp.V) : χ v = 0 := by
  -- each `χ_{ij}` is orthogonal to `χ` (conjugate symmetry of the hypothesis)
  have hcf : ∀ (a : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (b : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      ClassFunction.inner (hyp.chiFam hVeq app (a, b)) χ = 0 := fun a b => by
    rw [inner_conj_symm χ (hyp.chiFam hVeq app (a, b)), hχ a b, star_zero]
  have hkey : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 → ClassFunction.inner (hyp.alphaCF p q)
        (ClassFunction.restrict hyp.W χ) = 0 := by
    intro p q hp hq
    have hinduce : ClassFunction.induce hyp.W (hyp.alphaCF p q)
        = hyp.sigma hVeq app (hyp.alphaCF p q) := by
      have h1 := hyp.sigma_eq_tau hVeq app (hyp.alpha hVeq p q)
      have h2 := hyp.tau_eq_induce app.tau.toDadeIsometryData (hyp.alpha hVeq p q)
      rw [hyp.alpha_coe] at h1 h2
      exact h2.symm.trans h1.symm
    rw [← ClassFunction.inner_induce_eq_inner_restrict, hinduce,
      hyp.sigma_alphaCF hVeq app p q hp hq, (hyp.chiFam_spec hVeq app).2.2.2 p q hp hq,
      ClassFunction.inner_add_left, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ← (hyp.chiFam_spec hVeq app).1, hcf 1 1, hcf p 1, hcf 1 q, hcf p q]
    ring
  have hzero := hyp.vanishOnV_of_inner_alphaCF hVeq hkey hv
  rwa [ClassFunction.restrict_apply] at hzero

open scoped Classical in
/-- **Peterfalvi (3.7) support input**: the 4-term combination
`ω_{pq} + ω_{p'q'} − ω_{pq'} − ω_{p'q}` lies in `CF(W, V)`.  On `W₁` the `W₂`-parts (`q`) collapse
to
`1`, on `W₂` the `W₁`-parts (`p`) collapse, so the combination vanishes on `W₁ ∪ W₂`. -/
theorem omegaCombo_mem_supportedSubmodule (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
       - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q)
       : ClassFunction hyp.W ℂ)
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro w hw
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hVeq, mem_Vdiff]
  refine ⟨w.2, fun h1 => (ClassFunction.mem_support.mp hw) ?_,
    fun h2 => (ClassFunction.mem_support.mp hw) ?_⟩
  · -- `↑w ∈ W₁`: the `q`-parts collapse, the four terms cancel
    have hw1 : w ∈ hyp.W1.subgroupOf hyp.W := (Subgroup.mem_subgroupOf).mpr h1
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply, omega_apply,
      TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply,
      hyp.wSnd_eq_one_of_mem_W1 hw1, map_one, mul_one]
    ring
  · -- `↑w ∈ W₂`: the `p`-parts collapse, the four terms cancel
    have hw2 : w ∈ hyp.W2.subgroupOf hyp.W := (Subgroup.mem_subgroupOf).mpr h2
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply, omega_apply,
      TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply,
      hyp.wFst_eq_one_of_mem_W2 hw2, map_one, one_mul]
    ring

/-- The (3.7) test element `ω_{pq} + ω_{p'q'} − ω_{pq'} − ω_{p'q} ∈ CF(W, V)`. -/
noncomputable def omegaCombo (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    SupportedOnV ℂ hyp :=
  ⟨hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
     - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q),
   hyp.omegaCombo_mem_supportedSubmodule hVeq p p' q q'⟩

@[simp] theorem omegaCombo_coe (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.omegaCombo hVeq p p' q q' : ClassFunction hyp.W ℂ)
      = hyp.omega (hyp.omegaProdChar p q) + hyp.omega (hyp.omegaProdChar p' q')
        - hyp.omega (hyp.omegaProdChar p q') - hyp.omega (hyp.omegaProdChar p' q) := rfl

/-- For `α ∈ CF(W, V)` and `ψ ∈ CF(G)` vanishing on `V`, `⟨ψ, α^σ⟩ = 0`.  By (3.2)(a),
`α^σ = Ind_W^G α` is supported on `V^G = conjugatesOfSet V`; the class function `ψ` (vanishing on
`V`) vanishes there too, so the supports are disjoint. -/
theorem inner_sigma_eq_zero_of_vanishOnV (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV ℂ hyp) {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0) :
    ClassFunction.inner ψ (hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ)) = 0 := by
  apply ClassFunction.inner_eq_zero_of_disjoint_support
  rw [Set.disjoint_left]
  intro g hgψ hgσ
  -- `g ∈ Supp(α^σ) ⟹ g ∈ conjugatesOfSet V` (else `α^σ g = τ(α) g = 0`)
  have hgconj : g ∈ Group.conjugatesOfSet hyp.V := by
    by_contra hg
    refine (ClassFunction.mem_support.mp hgσ) ?_
    rw [show hyp.sigma hVeq app (α : ClassFunction hyp.W ℂ) = app.tau.toDadeMap α from
      hyp.sigma_eq_tau hVeq app α]
    exact full_map_eq_zero_of_not_mem_conjugatesOfSet_V app α hg
  -- `g ∈ conjugatesOfSet V ⟹ ψ g = 0` (`ψ` vanishes on `V`, class function)
  obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hgconj
  exact (ClassFunction.mem_support.mp hgψ) ((ψ.of_isConj hconj).symm.trans (hψ v hv))

/-- **Peterfalvi (3.6)**: the `σ`-image coefficient `a_{ij} = ⟨ψ, ω_{ij}^σ⟩` of `ψ ∈ CF(G)`.  As
`{ω_{ij}^σ} = {χ_{ij}}` (`chiFam`) is orthonormal, these are the Fourier coefficients of `ψ` along
`Im σ`, and `β = ψ − ∑ a_{ij} ω_{ij}^σ` is automatically orthogonal to `Im σ`.  Indexed by
`Ĉ₁ × Ĉ₂` (index `(1, 1) = ω_{00} = 1_W`). -/
noncomputable def sigmaCoeff (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ψ : ClassFunction G ℂ)
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) : ℂ :=
  ClassFunction.inner ψ (hyp.chiFam hVeq app pq)

/-- **Peterfalvi (3.6)**: `NC(ψ)` = number of nonzero `σ`-image coefficients of `ψ`. -/
noncomputable def sigmaNC (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ψ : ClassFunction G ℂ) : ℕ :=
  {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0}.ncard

/-- **Peterfalvi (3.7)**: under Hypothesis (3.6) (`ψ` vanishing on `V`), the `σ`-image coefficients
satisfy the additive grid identity `a_{ij} + a_{i'j'} = a_{ij'} + a_{i'j}`.  Apply
`inner_sigma_eq_zero_of_vanishOnV` to `α = ω_{ij} + ω_{i'j'} − ω_{ij'} − ω_{i'j} ∈ CF(W, V)`:
`σ(α) = χ_{ij} + χ_{i'j'} − χ_{ij'} − χ_{i'j}` (σ linear, `sigma_omega`), and `⟨ψ, σ(α)⟩ = 0`. -/
theorem sigmaCoeff_add_eq (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.sigmaCoeff hVeq app ψ (p, q) + hyp.sigmaCoeff hVeq app ψ (p', q')
      = hyp.sigmaCoeff hVeq app ψ (p, q') + hyp.sigmaCoeff hVeq app ψ (p', q) := by
  have hσ : hyp.sigma hVeq app (hyp.omegaCombo hVeq p p' q q' : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (p, q) + hyp.chiFam hVeq app (p', q')
        - hyp.chiFam hVeq app (p, q') - hyp.chiFam hVeq app (p', q) := by
    simp only [omegaCombo_coe, map_add, map_sub, hyp.sigma_omega hVeq app,
      hyp.omegaProdEquiv_symm_omegaProdChar]
  have h0 := hyp.inner_sigma_eq_zero_of_vanishOnV hVeq app (hyp.omegaCombo hVeq p p' q q') hψ
  rw [hσ] at h0
  simp only [ClassFunction.inner_add_right, ClassFunction.inner_sub_right] at h0
  simp only [sigmaCoeff]
  linear_combination h0

/-- **Peterfalvi (3.8) corollary** (`NC` too small for a row or column): if `ψ` vanishes on `V` and
`NC(ψ) < min(w₁, w₂)`, then *all* `σ`-image coefficients of `ψ` vanish — i.e. `ψ = β` is orthogonal
to `Im σ`.  By (3.7) the coefficient grid `a_{ij}` is additively separable; the abstract grid lemma
`grid_eq_zero_of_ncard_support_lt` then forces `a ≡ 0` (a nonzero separable grid fills a whole row
or column, needing `≥ min(w₁, w₂)` nonzeros).  This is the part of (3.8) used by (3.9.a) and most
§6/§7 consumers; the full row/column trichotomy (3.8.b)/(3.8.c) is only needed in §12+. -/
theorem sigmaCoeff_eq_zero_of_sigmaNC_lt (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hNC : hyp.sigmaNC hVeq app ψ < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app ψ pq = 0 := by
  have : Finite G := Finite.of_fintype G
  refine grid_eq_zero_of_ncard_support_lt (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ pq
  rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
  exact hNC

/-- `w₁ = |W₁| ≥ 3`: `|W₁|` is odd (it divides the odd `|W|`) and `> 1` (`W₁` is nontrivial). -/
theorem three_le_card_W1 (hyp : TICyclicHypothesis G) : 3 ≤ Nat.card hyp.W1 := by
  have : Finite G := Finite.of_fintype G
  have hodd : Odd (Nat.card hyp.W1) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W1_le_W)
  have hgt : 1 < Nat.card hyp.W1 :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W1_nontrivial)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- `w₂ = |W₂| ≥ 3`: `|W₂|` is odd (it divides the odd `|W|`) and `> 1` (`W₂` is nontrivial). -/
theorem three_le_card_W2 (hyp : TICyclicHypothesis G) : 3 ≤ Nat.card hyp.W2 := by
  have : Finite G := Finite.of_fintype G
  have hodd : Odd (Nat.card hyp.W2) :=
    hyp.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.W2_le_W)
  have hgt : 1 < Nat.card hyp.W2 :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hyp.W2_nontrivial)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **(3.9)(a) support bound**: a norm-`1` virtual character `χ` (i.e. `χ ∈ ±Irr(G)`) has at most
one nonzero inner product against the orthonormal family `(χ_{ij})`.  By the norm-`1` classifier
`χ = ε • μ`, and any `χ_{pq}` with `⟨χ, χ_{pq}⟩ ≠ 0` equals `±μ`; two distinct such indices would
give `⟨χ_{pq}, χ_{p'q'}⟩ = ±1 ≠ 0`, contradicting the orthonormality of the family. -/
theorem ncard_inner_chiFam_ne_zero_le_one (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ1 : ClassFunction.inner χ χ = 1) :
    {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
      ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}.ncard ≤ 1 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨ε, μ, hε, hχrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hχ hχ1
  -- any index in the support has `χ_{pq} = ±μ`
  have hkey : ∀ pq, ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0 →
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
        hyp.chiFam hVeq app pq = δ • (μ : ClassFunction G ℂ) := by
    intro pq hpq
    have hnorm : ClassFunction.inner (hyp.chiFam hVeq app pq) (hyp.chiFam hVeq app pq) = 1 := by
      rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
    obtain ⟨δ, ν, hδ, hνrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one
      ((hyp.chiFam_spec hVeq app).2.1 pq) hnorm
    refine ⟨δ, hδ, ?_⟩
    have hμν : μ = ν := by
      by_contra hne
      apply hpq
      rw [hχrepr, hνrepr, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        irreducibleCharacter_inner_eq_ite, if_neg hne, mul_zero, mul_zero]
    rw [hνrepr, hμν]
  -- two indices in the support coincide (their `χ`-values are both `±μ`, hence not orthogonal)
  by_cases hempty :
      {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} = ∅
  · rw [hempty]; simp
  · obtain ⟨pq₀, hpq₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨δ₀, hδ₀, hrepr₀⟩ := hkey pq₀ hpq₀
    have hsub : {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} ⊆ {pq₀} := by
      intro pq hpq
      obtain ⟨δ, hδ, hrepr⟩ := hkey pq hpq
      have hinner : ClassFunction.inner (hyp.chiFam hVeq app pq)
          (hyp.chiFam hVeq app pq₀) ≠ 0 := by
        rw [hrepr, hrepr₀, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
          ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          irreducibleCharacter_inner_eq_ite, if_pos rfl, star_intCast, mul_one]
        rcases hδ with rfl | rfl <;> rcases hδ₀ with rfl | rfl <;> norm_num
      rw [(hyp.chiFam_spec hVeq app).2.2.1] at hinner
      by_cases heq : pq = pq₀
      · exact heq
      · rw [if_neg heq] at hinner; exact absurd rfl hinner
    calc {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
          ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}.ncard
        ≤ ({pq₀} : Set _).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton pq₀

/-- **(3.9)(a)-norm-`2` support bound**: a norm-`2` virtual character `χ ∈ ZIrr(G)` has at most two
nonzero `σ`-image coefficients.  By `mem_ZIrr_inner_self_eq_sum_sq` +
`exists_pair_of_sum_sq_eq_two`, `χ = ε_α·α + ε_β·β` for two distinct irreducibles `α, β`; each has
`≤ 1` nonzero inner product against the orthonormal `χ`-family
(`ncard_inner_chiFam_ne_zero_le_one`),
and the coefficient support is contained in `S_α ∪ S_β`.  This is the norm-`2` analogue of
`ncard_inner_chiFam_ne_zero_le_one`, used by the (4.8)/(10.5) Dade-image trichotomy endgames. -/
theorem ncard_sigmaCoeff_ne_zero_le_two (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ2 : ClassFunction.inner χ χ = 2) :
    {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
      hyp.sigmaCoeff hVeq app χ pq ≠ 0}.ncard ≤ 2 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hχ2
  obtain ⟨α, β, hαβ, hs, -, -⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hαZ : α ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨α, hαm⟩ : IrreducibleCharacter G)
  have hβZ : β ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨β, hβm⟩ : IrreducibleCharacter G)
  have hα1 : ClassFunction.inner α α = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ⟨α, hαm⟩
    rwa [if_pos rfl] at this
  have hβ1 : ClassFunction.inner β β = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ⟨β, hβm⟩
    rwa [if_pos rfl] at this
  have hχαβ : χ = (c α : ℂ) • α + (c β : ℂ) • β := by
    rw [hrepr, hs, Finset.sum_pair hαβ]
  refine le_trans (Set.ncard_le_ncard (t :=
    {pq | ClassFunction.inner α (hyp.chiFam hVeq app pq) ≠ 0} ∪
    {pq | ClassFunction.inner β (hyp.chiFam hVeq app pq) ≠ 0})
    ?_ (Set.toFinite _)) (le_trans (Set.ncard_union_le _ _) ?_)
  · intro pq hpq
    simp only [sigmaCoeff, Set.mem_ofPred_eq] at hpq
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    exact hpq (by rw [hχαβ, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, hcon.1, hcon.2, mul_zero, mul_zero, add_zero])
  · exact add_le_add
      (hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hαZ hα1)
      (hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hβZ hβ1)

open scoped Classical in
/-- **Bessel `NC` bound** (general norm): a virtual character `χ ∈ ZIrr(G)` with squared norm `N`
has at most `N` nonzero `σ`-image coefficients, `NC(χ) ≤ N`.  Writing `χ = ∑_a c_a·a` over its
irreducible constituents (`mem_ZIrr_inner_self_eq_sum_sq`), every index `pq` of the `σ`-coefficient
support has some constituent `a` with `⟨a, χ_{pq}⟩ ≠ 0`; the per-constituent supports each have
`≤ 1` element (`ncard_inner_chiFam_ne_zero_le_one`), so `NC(χ) ≤ |supp(c)| ≤ ∑_a c_a² = ‖χ‖² = N`
(each nonzero `c_a` contributes `c_a² ≥ 1`).  The norm-`1` (`…le_one`) and norm-`2` (`…le_two`)
support bounds are special cases; this is the form used by the coherence-free (10.9) `NC < 2w₁`
estimate (`NC ≤ w₁ + 1`). -/
theorem ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} {N : ℕ} (hχ : χ ∈ ZIrr G)
    (hχN : ClassFunction.inner χ χ = (N : ℂ)) :
    hyp.sigmaNC hVeq app χ ≤ N := by
  have : Finite G := Finite.of_fintype G
  have : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  -- `∑_a c_a² = N` as integers.
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = (N : ℤ) := by
    have h : (∑ a ∈ c.support, (c a : ℂ) ^ 2) = (N : ℂ) := hsq.symm.trans hχN
    have hcast : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = (N : ℂ) := by push_cast; exact h
    exact_mod_cast hcast
  rw [TICyclicHypothesis.sigmaNC,
    show {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
        hyp.sigmaCoeff hVeq app χ pq ≠ 0}
      = ↑(Finset.univ.filter (fun pq => hyp.sigmaCoeff hVeq app χ pq ≠ 0)) by
        ext pq
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and],
    Set.ncard_coe_finset]
  calc (Finset.univ.filter (fun pq => hyp.sigmaCoeff hVeq app χ pq ≠ 0)).card
      ≤ (c.support.biUnion (fun a => Finset.univ.filter
            (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0))).card := by
        refine Finset.card_le_card (fun pq hpq => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq
        rw [Finset.mem_biUnion]
        by_contra hcon
        push Not at hcon
        apply hpq
        change ClassFunction.inner χ (hyp.chiFam hVeq app pq) = 0
        rw [hrepr, inner_sum_left]
        refine Finset.sum_eq_zero (fun a ha => ?_)
        have := hcon a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
        rw [ClassFunction.inner_smul_left, this, mul_zero]
    _ ≤ ∑ a ∈ c.support, (Finset.univ.filter
            (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ c.support, 1 := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        have haZ : a ∈ ZIrr G :=
          IrreducibleCharacter.mem_ZIrr (⟨a, hsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter
              G)
        have ha1 : ClassFunction.inner a a = 1 := by
          have := irreducibleCharacter_inner_eq_ite
            (⟨a, hsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter G)
            ⟨a, hsupp (Finset.mem_coe.mpr ha)⟩
          rwa [if_pos rfl] at this
        have hle := hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
        rwa [show {pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) |
            ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0}
          = ↑(Finset.univ.filter (fun pq => ClassFunction.inner a (hyp.chiFam hVeq app pq) ≠ 0))
          by
            ext pq
            simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and], Set.ncard_coe_finset] at hle
    _ = c.support.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ N := by
        have hb : (c.support.card : ℤ) ≤ ∑ a ∈ c.support, c a ^ 2 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_le_sum (fun a ha => ?_)
          have hne : c a ≠ 0 := Finsupp.mem_support_iff.mp ha
          have h0 : (0 : ℤ) ≤ c a ^ 2 := sq_nonneg _
          have hnz : c a ^ 2 ≠ 0 := pow_ne_zero 2 hne
          push_cast; omega
        rw [hsumZ] at hb
        exact_mod_cast hb

/-- **(3.9)(a)-norm-`2` coefficient bound**: the `σ`-image coefficients of a norm-`2` virtual
character `χ ∈ ZIrr(G)` lie in `{0, ±1}`.  Writing `χ = ε_α·α + ε_β·β` (norm-`2` ⟹ two constituents)
and `χ_{pq} = ε·ν` (norm-`1` classifier), the coefficient `⟨χ, χ_{pq}⟩` is `ε_α·ε` if `ν = α`,
`ε_β·ε` if `ν = β`, and `0` otherwise (`α ≠ β`).  Norm-`2` analogue of the norm-`1` support bound,
used by the (4.8)/(10.5) trichotomy endgames to exclude a `±2` row coefficient. -/
theorem sigmaCoeff_eq_zero_or_one_of_inner_self_two (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) (hχ2 : ClassFunction.inner χ χ = 2)
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app χ pq = 0 ∨ hyp.sigmaCoeff hVeq app χ pq = 1 ∨
      hyp.sigmaCoeff hVeq app χ pq = -1 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hχ
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hχ2
  obtain ⟨α, β, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  obtain ⟨ε, ν, hε, hν⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one
    ((hyp.chiFam_spec hVeq app).2.1 pq)
    (by rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl])
  have hαν : ClassFunction.inner α (ν : ClassFunction G ℂ)
      = if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ν
  have hβν : ClassFunction.inner β (ν : ClassFunction G ℂ)
      = if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ν
  have hf : hyp.sigmaCoeff hVeq app χ pq
      = (c α : ℂ) * ((ε : ℂ) * (if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0))
        + (c β : ℂ) * ((ε : ℂ) * (if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0)) := by
    rw [sigmaCoeff, hrepr, hs, Finset.sum_pair hαβ, hν,
      ← Int.cast_smul_eq_zsmul ℂ ε, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hαν, hβν]
  rw [hf]
  by_cases hαe : (⟨α, hαm⟩ : IrreducibleCharacter G) = ν
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · exact absurd (Subtype.ext_iff.mp (hαe.trans hβe.symm)) hαβ
    · rw [if_pos hαe, if_neg hβe]
      simp only [mul_one, mul_zero, add_zero]
      rcases hcα with hcα | hcα <;> rcases hε with hε | hε <;> rw [hcα, hε] <;> norm_num
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · rw [if_neg hαe, if_pos hβe]
      simp only [mul_one, mul_zero, zero_add]
      rcases hcβ with hcβ | hcβ <;> rcases hε with hε | hε <;> rw [hcβ, hε] <;> norm_num
    · rw [if_neg hαe, if_neg hβe]; left; ring

/-- **Peterfalvi (3.9)(a)** (§6 keystone): if `χ ∈ ±Irr(G)` (a virtual character of norm `1`)
agrees with `ω ∈ Irr(W)` on `V`, then `χ = ω^σ`.  The difference `φ = ω^σ − χ` vanishes on `V`
((3.2)(c) + the hypothesis), and its `σ`-coefficient support is contained in
`{index of ω} ∪ {pq | ⟨χ, χ_{pq}⟩ ≠ 0}`, so `NC(φ) ≤ 2 < 3 ≤ min(w₁, w₂)`; the (3.8) corollary
then kills all coefficients of `φ`.  At the `ω`-index this gives `⟨χ, ω^σ⟩ = 1`, whence
`‖χ − ω^σ‖² = 1 − 1 − 1 + 1 = 0` and positive definiteness concludes. -/
theorem eq_sigma_of_apply_eq_on_V (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) {χ : ClassFunction G ℂ}
    (hχ : χ ∈ ZIrr G) (hχ1 : ClassFunction.inner χ χ = 1)
    (hres : ∀ v (hv : v ∈ hyp.V), χ v = (ω : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩) :
    χ = hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) := by
  classical
  have : Finite G := Finite.of_fintype G
  -- the difference `φ = ω^σ − χ` vanishes on `V` ((3.2)(c) + the hypothesis)
  have hφV : ∀ v ∈ hyp.V,
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ) v = 0 := by
    intro v hv
    rw [ClassFunction.sub_apply, hres v hv, hyp.sigma_apply_of_mem_V hVeq app _ hv, sub_self]
  -- `ω^σ` is the family member at the `ω`-index
  have hσωeq : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω) :=
    hyp.sigma_irreducibleCharacter hVeq app ω
  -- `NC(φ) ≤ 2 < 3 ≤ min(w₁, w₂)`
  have hNC : hyp.sigmaNC hVeq app (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ)
      < min (Nat.card hyp.W1) (Nat.card hyp.W2) := by
    have hsub : {pq | hyp.sigmaCoeff hVeq app
          (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ) pq ≠ 0}
        ⊆ insert (hyp.omegaIrrEquiv.symm ω)
            {pq | ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0} := by
      intro pq hpq
      simp only [Set.mem_ofPred_eq, sigmaCoeff] at hpq
      by_cases h0 : pq = hyp.omegaIrrEquiv.symm ω
      · exact Set.mem_insert_iff.mpr (Or.inl h0)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        simp only [Set.mem_ofPred_eq]
        intro hc
        apply hpq
        rw [ClassFunction.inner_sub_left, hc, hσωeq, (hyp.chiFam_spec hVeq app).2.2.1,
          if_neg (fun h => h0 h.symm), sub_zero]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hins := Set.ncard_insert_le (hyp.omegaIrrEquiv.symm ω)
      {pq | ClassFunction.inner χ (hyp.chiFam hVeq app pq) ≠ 0}
    have hone := hyp.ncard_inner_chiFam_ne_zero_le_one hVeq app hχ hχ1
    have h31 := hyp.three_le_card_W1
    have h32 := hyp.three_le_card_W2
    simp only [sigmaNC]
    omega
  -- all `σ`-coefficients of `φ` vanish; at the `ω`-index this gives `⟨χ, ω^σ⟩ = 1`
  have hσσ : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner hVeq app, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  have hinner : ClassFunction.inner χ (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    have h0 : ClassFunction.inner
        (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) - χ)
        (hyp.chiFam hVeq app (hyp.omegaIrrEquiv.symm ω)) = 0 :=
      hyp.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hφV hNC (hyp.omegaIrrEquiv.symm ω)
    rw [← hσωeq, ClassFunction.inner_sub_left, hσσ] at h0
    linear_combination -h0
  -- `‖χ − ω^σ‖² = 0` ⟹ `χ = ω^σ`
  have hfinal : ClassFunction.inner
      (χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hχ1, hinner, hσσ,
      inner_conj_symm χ (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)), hinner, star_one]
    norm_num
  have hsub0 : χ - hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) = 0 :=
    eq_zero_of_inner_self_re_eq_zero (by rw [hfinal]; exact Complex.zero_re)
  exact sub_eq_zero.mp hsub0

/-- **Peterfalvi (3.9)(a)** ("in particular"): `σ` commutes with coefficientwise field
automorphisms on `Irr(W)`: `(ω^σ)^u = (ω^u)^σ` for any `u : ℂ ≃+* ℂ`.  Indeed `(ω^σ)^u` is again
a norm-`1` virtual character (`ω^σ = ±μ` by the norm-`1` classifier, and `u` maps `±Irr(G)` into
`±Irr(G)`), and on `V` it agrees with `ω^u` (apply `u` inside (3.2)(c)); the main part of (3.9)(a)
then identifies it with `(ω^u)^σ`.  No star-commutation hypothesis on `u` is needed. -/
theorem sigma_mapRingEquiv_comm (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (u : ℂ ≃+* ℂ) (ω : IrreducibleCharacter hyp.W) :
    ClassFunction.mapRingEquiv u (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      = hyp.sigma hVeq app
          ((IrreducibleCharacter.galoisMap u ω : IrreducibleCharacter hyp.W) :
            ClassFunction hyp.W ℂ) := by
  classical
  have : Finite G := Finite.of_fintype G
  have hσZ : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr ω.2)
  have hσ1 : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner hVeq app, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  obtain ⟨ε, μ, hε, hrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hσZ hσ1
  refine hyp.eq_sigma_of_apply_eq_on_V hVeq app (IrreducibleCharacter.galoisMap u ω)
    (ClassFunction.mapRingEquiv_mem_ZIrr u hσZ) ?_ ?_
  · -- norm `1`: `(ω^σ)^u = ε • μ^u` with `μ^u ∈ Irr(G)`
    rw [hrepr, ClassFunction.mapRingEquiv_zsmul, ← Int.cast_smul_eq_zsmul ℂ,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      star_intCast, ← IrreducibleCharacter.galoisMap_apply_coe,
      irreducibleCharacter_inner_eq_ite, if_pos rfl, mul_one]
    rcases hε with rfl | rfl <;> norm_num
  · -- values on `V`: `u ((ω^σ)(v)) = u (ω(v)) = (ω^u)(v)` by (3.2)(c)
    intro v hv
    rw [ClassFunction.mapRingEquiv_apply, hyp.sigma_apply_of_mem_V hVeq app _ hv,
      IrreducibleCharacter.galoisMap_apply_apply]

/-- Every linear character of the finite `W` has finite multiplicative order:
`ξ ^ |W| = 1` pointwise. -/
theorem orderOf_char_ne_zero (hyp : TICyclicHypothesis G) [Finite hyp.W]
    (ξ : hyp.W →* ℂˣ) : orderOf ξ ≠ 0 := by
  have : Fintype hyp.W := Fintype.ofFinite _
  have hξpow : ξ ^ Fintype.card hyp.W = 1 := by
    ext w
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
  exact ((isOfFinOrder_iff_pow_eq_one.mpr
    ⟨Fintype.card hyp.W, Fintype.card_pos, hξpow⟩).orderOf_pos).ne'

/-- **Peterfalvi (3.9)(b)**: let `a` be the multiplicative order of the linear character `ξ` of
`W` and let `k` be coprime to `a`.  There is a ring automorphism `u` of `ℂ` such that
`(ω(ξ^k))^σ = (ω(ξ))^{σu}`; moreover `(ω(ξ^k))^σ(g) = (ω(ξ))^σ(g)` for every `g : G` of order
prime to `a`.

The automorphism is `(· ^ k)` on `a`-th roots of unity and the identity on `B`-th roots, where
`B` is the product of the divisors of `|G|` coprime to `a` ((1.9), CRT form
`exists_complexRingEquiv_pow_and_fixed`).  Since `ξ` takes values in the `a`-th roots,
`ω(ξ^k) = (ω(ξ))^u`, and `σ` commutes with `u` by (3.9)(a); at `g` of order prime to `a` the
eigenvalues of `g` are `B`-th roots of unity, which `u` fixes. -/
theorem exists_mapRingEquiv_sigma_omega_pow (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {k : ℕ} (hk : k.Coprime (orderOf ξ)) :
    ∃ u : ℂ ≃+* ℂ,
      hyp.sigma hVeq app (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ)
        = ClassFunction.mapRingEquiv u
            (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)) ∧
      ∀ g : G, (orderOf g).Coprime (orderOf ξ) →
        hyp.sigma hVeq app (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ) g
          = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := by
  classical
  have : Finite G := Finite.of_fintype G
  have ha : orderOf ξ ≠ 0 := hyp.orderOf_char_ne_zero ξ
  -- `B` = product of the divisors of `|G|` coprime to `a`: coprime to `a`, and any
  -- `orderOf g` coprime to `a` divides it
  set B := ((Nat.card G).divisors.filter (fun d => d.Coprime (orderOf ξ))).prod id with hB_def
  have hB : B ≠ 0 :=
    (Finset.prod_pos fun d hd => Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne'
  have hab : (orderOf ξ).Coprime B :=
    Nat.coprime_prod_right_iff.mpr fun d hd =>
      Nat.coprime_comm.mp (Finset.mem_filter.mp hd).2
  obtain ⟨u, hua, huB⟩ := exists_complexRingEquiv_pow_and_fixed ha hB hab hk
  -- the bridge `ω(ξ^k) = (ω(ξ))^u`: the values of `ξ` are `a`-th roots of unity
  have hbridge : (hyp.omega (ξ ^ k) : ClassFunction hyp.W ℂ)
      = (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ) := by
    ext w
    rw [IrreducibleCharacter.galoisMap_apply_apply, omega_apply, omega_apply,
      MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    refine (hua (ξ w : ℂ) ?_).symm
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one ξ,
      MonoidHom.one_apply, Units.val_one]
  refine ⟨u, ?_, ?_⟩
  · rw [hbridge]
    exact (hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ)).symm
  · -- the value part: at `g` of order coprime to `a`, the eigenvalues are `B`-th roots
    intro g hg
    have hdvdB : orderOf g ∣ B := by
      refine Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨?_, hg⟩)
      exact Nat.mem_divisors.mpr ⟨orderOf_dvd_natCard g, Nat.card_pos.ne'⟩
    have hσZ : hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
      hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr (hyp.omega ξ).2)
    have hval := mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hσZ u
      (isOfFinOrder_of_finite g) (k := 1) (fun ζ hζ => by
        rw [pow_one]
        refine huB ζ ?_
        obtain ⟨c, hc⟩ := hdvdB
        rw [hc, pow_mul, hζ, one_pow])
    rw [hbridge, ← hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ), hval, pow_one]

/-- `σ` sends the `(3.3)` product-character basis point to the `(3.5)` family member:
`(ω(χ₁·χ₂))^σ = χ_{(χ₁,χ₂)}`.  Restatement of `sigma_irreducibleCharacter` through
`omegaIrrEquiv_apply`, exposing the product character so the (3.9.b) Galois moves can
compute with powers. -/
theorem sigma_omega_omegaProdChar (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.sigma hVeq app (hyp.omega (hyp.omegaProdChar χ₁ χ₂) : ClassFunction hyp.W ℂ)
      = hyp.chiFam hVeq app (χ₁, χ₂) := by
  have h := hyp.sigma_irreducibleCharacter hVeq app (hyp.omegaIrrEquiv (χ₁, χ₂))
  rw [Equiv.symm_apply_apply] at h
  rw [← h, hyp.omegaIrrEquiv_apply]

/-- **Galois transitivity on the punctured `W₁`-side of the `(3.5)` family** (the (3.9.b)
column-`0` pair-move): when `|W₁|` is prime, any two nontrivial `W₁`-side indices at the trivial
`W₂`-index are Galois conjugate — `∃ u, χ_{(p',1)} = (χ_{(p,1)})^u`.  The `W₂`-side stays at `1`
because the trivial character is a fixed point of every coefficient automorphism (no
`CRT`-fixing is needed).  With the prime-order transitivity `p' = p^k` (`k` coprime to
`|W₁| = orderOf p`), this is `exists_mapRingEquiv_sigma_omega_pow` at the product character
`ξ = ω_{(p,1)}`, read through `sigma_omega_omegaProdChar`.  Peterfalvi (11.9.a) uses this and
its `W₂`-side mirror (`exists_mapRingEquiv_chiFam_right_move`) for the column-`0`/row-`0`
coefficient constancy of the `τ(μ₀ − ζ)` grid (issue 1024 G3). -/
theorem exists_mapRingEquiv_chiFam_left_move (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hprime : (Nat.card hyp.W1).Prime)
    {p p' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hp : p ≠ 1) (hp' : p' ≠ 1) :
    ∃ u : ℂ ≃+* ℂ,
      hyp.chiFam hVeq app (p', 1)
        = ClassFunction.mapRingEquiv u (hyp.chiFam hVeq app (p, 1)) := by
  classical
  have : Finite G := Finite.of_fintype G
  -- the character group has prime order `|W₁|`, so the nontrivial `p` generates
  have hcard : Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W1 :=
    hyp.card_charGroup_subgroupOf hyp.W1_le_W
  have hord : orderOf p = Nat.card hyp.W1 := by
    have hdvd : orderOf p ∣ Nat.card ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := orderOf_dvd_natCard p
    rw [hcard] at hdvd
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hp
    · exact h
  have htop : Subgroup.zpowers p = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  obtain ⟨kz, hkz⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top p')
  -- normalise the exponent to `ℕ`
  have hordpos : 0 < orderOf p := orderOf_pos p
  set k : ℕ := (kz % (orderOf p : ℤ)).toNat with hkdef
  have hkcast : (k : ℤ) = kz % (orderOf p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hordpos.ne'))
  have hp'k : p ^ k = p' := by
    calc
      p ^ k = p ^ (k : ℤ) := (zpow_natCast p k).symm
      _ = p ^ (kz % (orderOf p : ℤ)) := congrArg (p ^ ·) hkcast
      _ = p ^ kz := zpow_mod_orderOf p kz
      _ = p' := hkz
  -- the product character `ξ = ω_{(p,1)}` has the same order as `p` (`wFst` is surjective)
  set ξ : hyp.W →* ℂˣ := hyp.omegaProdChar p 1 with hξdef
  have hξ_eq : ξ = p.comp hyp.wFst := hyp.omegaProdChar_one_right p
  have hsurj : Function.Surjective hyp.wFst := by
    have h1 : Function.Surjective (MonoidHom.fst (↥(hyp.W1.subgroupOf hyp.W))
        (↥(hyp.W2.subgroupOf hyp.W))) := Prod.fst_surjective
    exact h1.comp hyp.wProdEquiv.symm.surjective
  have hpow : ∀ (r : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (n : ℕ),
      (r.comp hyp.wFst) ^ n = (r ^ n).comp hyp.wFst := by
    intro r n
    ext w
    simp [MonoidHom.pow_apply]
  have hordξ : orderOf ξ = orderOf p := by
    rw [hξ_eq]
    refine orderOf_eq_orderOf_iff.mpr fun n => ?_
    rw [hpow p n]
    constructor
    · intro h
      refine (MonoidHom.cancel_right hsurj).mp ?_
      rw [h, MonoidHom.one_comp]
    · intro h
      rw [h, MonoidHom.one_comp]
  -- coprimality: `¬ |W₁| ∣ k`, else `p' = p^k = 1`
  have hk : k.Coprime (orderOf ξ) := by
    rw [hordξ, hord, Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hprime).mpr fun hdvd => ?_
    exact hp' (by rw [← hp'k, ← hord] at *; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  -- realise the move via (3.9)(b) and read both sides through the `(3.5)` family
  obtain ⟨u, hu, -⟩ := hyp.exists_mapRingEquiv_sigma_omega_pow hVeq app ξ hk
  refine ⟨u, ?_⟩
  have hξk : ξ ^ k = hyp.omegaProdChar p' 1 := by
    rw [hξ_eq, hpow p k, hp'k, hyp.omegaProdChar_one_right]
  rw [← hyp.sigma_omega_omegaProdChar hVeq app p' 1, ← hξk, hu, hξdef,
    hyp.sigma_omega_omegaProdChar hVeq app p 1]

/-- **Galois transitivity on the punctured `W₂`-side of the `(3.5)` family** (the (3.9.b)
row-`0` pair-move): the `W₂`-side mirror of `exists_mapRingEquiv_chiFam_left_move` — when
`|W₂|` is prime, `∃ u, χ_{(1,q')} = (χ_{(1,q)})^u` for nontrivial `q, q'`. -/
theorem exists_mapRingEquiv_chiFam_right_move (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (hprime : (Nat.card hyp.W2).Prime)
    {q q' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hq : q ≠ 1) (hq' : q' ≠ 1) :
    ∃ u : ℂ ≃+* ℂ,
      hyp.chiFam hVeq app (1, q')
        = ClassFunction.mapRingEquiv u (hyp.chiFam hVeq app (1, q)) := by
  classical
  have : Finite G := Finite.of_fintype G
  have hcard : Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) = Nat.card hyp.W2 :=
    hyp.card_charGroup_subgroupOf hyp.W2_le_W
  have hord : orderOf q = Nat.card hyp.W2 := by
    have hdvd : orderOf q ∣ Nat.card ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := orderOf_dvd_natCard q
    rw [hcard] at hdvd
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hq
    · exact h
  have htop : Subgroup.zpowers q = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  obtain ⟨kz, hkz⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top q')
  have hordpos : 0 < orderOf q := orderOf_pos q
  set k : ℕ := (kz % (orderOf q : ℤ)).toNat with hkdef
  have hkcast : (k : ℤ) = kz % (orderOf q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hordpos.ne'))
  have hq'k : q ^ k = q' := by
    calc
      q ^ k = q ^ (k : ℤ) := (zpow_natCast q k).symm
      _ = q ^ (kz % (orderOf q : ℤ)) := congrArg (q ^ ·) hkcast
      _ = q ^ kz := zpow_mod_orderOf q kz
      _ = q' := hkz
  set ξ : hyp.W →* ℂˣ := hyp.omegaProdChar 1 q with hξdef
  have hξ_eq : ξ = q.comp hyp.wSnd := hyp.omegaProdChar_one_left q
  have hsurj : Function.Surjective hyp.wSnd := by
    have h1 : Function.Surjective (MonoidHom.snd (↥(hyp.W1.subgroupOf hyp.W))
        (↥(hyp.W2.subgroupOf hyp.W))) := Prod.snd_surjective
    exact h1.comp hyp.wProdEquiv.symm.surjective
  have hpow : ∀ (r : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) (n : ℕ),
      (r.comp hyp.wSnd) ^ n = (r ^ n).comp hyp.wSnd := by
    intro r n
    ext w
    simp [MonoidHom.pow_apply]
  have hordξ : orderOf ξ = orderOf q := by
    rw [hξ_eq]
    refine orderOf_eq_orderOf_iff.mpr fun n => ?_
    rw [hpow q n]
    constructor
    · intro h
      refine (MonoidHom.cancel_right hsurj).mp ?_
      rw [h, MonoidHom.one_comp]
    · intro h
      rw [h, MonoidHom.one_comp]
  have hk : k.Coprime (orderOf ξ) := by
    rw [hordξ, hord, Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hprime).mpr fun hdvd => ?_
    exact hq' (by rw [← hq'k, ← hord] at *; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨u, hu, -⟩ := hyp.exists_mapRingEquiv_sigma_omega_pow hVeq app ξ hk
  refine ⟨u, ?_⟩
  have hξk : ξ ^ k = hyp.omegaProdChar 1 q' := by
    rw [hξ_eq, hpow q k, hq'k, hyp.omegaProdChar_one_left]
  rw [← hyp.sigma_omega_omegaProdChar hVeq app 1 q', ← hξk, hu, hξdef,
    hyp.sigma_omega_omegaProdChar hVeq app 1 q]

end TICyclicHypothesis

omit [Fintype G] in
/-- Virtual-character values are algebraic integers: each irreducible character value is a sum
of roots of unity (`character_isIntegral`), and `IsIntegral ℤ` is closed under the `ℤ`-span
operations. -/
theorem isIntegral_apply_of_mem_ZIrr [Finite G] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) :
    IsIntegral ℤ (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      rw [show x g = ρ.character g from congrFun hchar g]
      exact character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

/-- Every ring automorphism of `ℂ` acts on the `a`-th roots of unity as `(· ^ i)` for some `i`
coprime to `a`: the image of a primitive root `ζ₀` is again a primitive root, hence `ζ₀ ^ i`
with `i` coprime to `a`, and every `a`-th root is a power of `ζ₀`. -/
theorem exists_pow_forall_rootsOfUnity (u : ℂ ≃+* ℂ) {a : ℕ} (ha : a ≠ 0) :
    ∃ i : ℕ, i.Coprime a ∧ ∀ ζ : ℂ, ζ ^ a = 1 → u ζ = ζ ^ i := by
  have : NeZero a := ⟨ha⟩
  have hζ₀ := Complex.isPrimitiveRoot_exp a ha
  have hupow : u (Complex.exp (2 * Real.pi * Complex.I / a)) ^ a = 1 := by
    rw [← map_pow, hζ₀.pow_eq_one, map_one]
  obtain ⟨i, _, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hupow
  have hprim : IsPrimitiveRoot (u (Complex.exp (2 * Real.pi * Complex.I / a))) a :=
    hζ₀.map_of_injective u.injective
  have hcop : i.Coprime a := by
    rw [← hi] at hprim
    exact (hζ₀.pow_iff_coprime (Nat.pos_of_ne_zero ha) i).mp hprim
  refine ⟨i, hcop, fun ζ hζ => ?_⟩
  obtain ⟨m, _, hm⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [← hm, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm i m]

/-- A complex number that is integral over `ℚ` and fixed by every ring automorphism of `ℂ` is
rational.  The subfield `K = ℚ(rootSet p ℂ)` generated by the roots of `p = minpoly ℚ x` is a
splitting field, hence normal over `ℚ`; any root `y` of `p` is then `v x` for some
`v : K ≃ₐ[ℚ] K` (`IsConjRoot.exists_algEquiv`), and extending `v` to `ℂ`
(`exists_complexRingEquiv_extends`) the fixed-point hypothesis forces `y = x`.  So the separable
`p` has a single root in `ℂ`, hence degree `1`. -/
theorem exists_ratCast_of_forall_complexRingEquiv_eq {x : ℂ} (hint : IsIntegral ℚ x)
    (hfix : ∀ u : ℂ ≃+* ℂ, u x = x) : ∃ q : ℚ, x = (q : ℂ) := by
  classical
  have hsplits : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  have : (minpoly ℚ x).IsSplittingField ℚ
      (IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  have : Normal ℚ (IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
    Normal.of_isSplittingField (minpoly ℚ x)
  have hxroot : x ∈ (minpoly ℚ x).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ x⟩
  have hxK : x ∈ IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ) :=
    IntermediateField.subset_adjoin ℚ _ hxroot
  -- every root of `minpoly ℚ x` equals `x`
  have hall : ∀ y ∈ (minpoly ℚ x).rootSet ℂ, y = x := by
    intro y hy
    have hyK : y ∈ IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ) :=
      IntermediateField.subset_adjoin ℚ _ hy
    -- `⟨y⟩` is a conjugate root of `⟨x⟩` in the normal extension `K/ℚ`
    have hminy : minpoly ℚ y = minpoly ℚ x :=
      (isConjRoot_of_aeval_eq_zero hint (Polynomial.mem_rootSet.mp hy).2).symm
    have hconj : IsConjRoot ℚ
        (⟨y, hyK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))
        (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) := by
      change minpoly ℚ _ = minpoly ℚ _
      calc minpoly ℚ (⟨y, hyK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))
          = minpoly ℚ y := IntermediateField.minpoly_eq _
        _ = minpoly ℚ x := hminy
        _ = minpoly ℚ (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ)) :=
            (IntermediateField.minpoly_eq
              (⟨x, hxK⟩ : IntermediateField.adjoin ℚ ((minpoly ℚ x).rootSet ℂ))).symm
    obtain ⟨v, hv⟩ := hconj.exists_algEquiv
    obtain ⟨u, hu⟩ := exists_complexRingEquiv_extends _ v.toRingEquiv
    have hux : u x = y := by
      have h := hu ⟨x, hxK⟩
      rw [show v.toRingEquiv ⟨x, hxK⟩ = v ⟨x, hxK⟩ from rfl, hv] at h
      exact h
    rw [← hux, hfix u]
  -- `minpoly ℚ x` is separable with a single root, hence has degree `1`
  have hone : Fintype.card ((minpoly ℚ x).rootSet ℂ) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨x, hxroot⟩, fun z => Subtype.ext (hall z.1 z.2)⟩
  have hdeg : (minpoly ℚ x).natDegree = 1 := by
    rw [← Polynomial.card_rootSet_eq_natDegree (minpoly.irreducible hint).separable hsplits,
      hone]
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  exact ⟨q, by rw [← hq, eq_ratCast]⟩

namespace TICyclicHypothesis

/-- **Peterfalvi (3.9)(c)**: if `g : G` has order prime to the multiplicative order `a` of the
linear character `ξ` of `W`, then `(ω(ξ))^σ(g) ∈ ℤ`.

The value is an algebraic integer (`isIntegral_apply_of_mem_ZIrr`), and it is fixed by every
ring automorphism `u` of `ℂ`: `u` acts on `a`-th roots of unity as `(· ^ i)` with `i` coprime
to `a` (`exists_pow_forall_rootsOfUnity`), so `(ω(ξ))^{σu} = (ω(ξ^i))^σ` by (3.9)(a), whose
value at `g` is `(ω(ξ))^σ(g)` by the value part of (3.9)(b).  Rationality follows by
`exists_ratCast_of_forall_complexRingEquiv_eq`, and a rational algebraic integer is an
integer. -/
theorem exists_intCast_sigma_omega_apply (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {g : G} (hg : (orderOf g).Coprime (orderOf ξ)) :
    ∃ n : ℤ, hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g = (n : ℂ) := by
  classical
  have : Finite G := Finite.of_fintype G
  have ha : orderOf ξ ≠ 0 := hyp.orderOf_char_ne_zero ξ
  have hσZ : hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr (hyp.omega ξ).2)
  -- the value is fixed by every ring automorphism of `ℂ`
  have hfix : ∀ u : ℂ ≃+* ℂ,
      u (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g)
        = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := by
    intro u
    obtain ⟨i, hicop, hipow⟩ := exists_pow_forall_rootsOfUnity u ha
    -- `(ω(ξ))^u = ω(ξ^i)`: `u` is `(· ^ i)` on the values of `ξ`
    have hbridge : (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ)
        = (hyp.omega (ξ ^ i) : ClassFunction hyp.W ℂ) := by
      ext w
      rw [IrreducibleCharacter.galoisMap_apply_apply, omega_apply, omega_apply,
        MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
      refine hipow (ξ w : ℂ) ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one ξ,
        MonoidHom.one_apply, Units.val_one]
    obtain ⟨_, _, hval⟩ := hyp.exists_mapRingEquiv_sigma_omega_pow hVeq app ξ hicop
    calc u (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g)
        = ClassFunction.mapRingEquiv u
            (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ)) g :=
          (ClassFunction.mapRingEquiv_apply u _ g).symm
      _ = hyp.sigma hVeq app
            (IrreducibleCharacter.galoisMap u (hyp.omega ξ) : ClassFunction hyp.W ℂ) g := by
          rw [hyp.sigma_mapRingEquiv_comm hVeq app u (hyp.omega ξ)]
      _ = hyp.sigma hVeq app (hyp.omega (ξ ^ i) : ClassFunction hyp.W ℂ) g := by
          rw [hbridge]
      _ = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g := hval g hg
  -- algebraic integer and rational, hence an integer
  have hint : IsIntegral ℤ (hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) g) :=
    isIntegral_apply_of_mem_ZIrr hσZ g
  obtain ⟨q, hq⟩ := exists_ratCast_of_forall_complexRingEquiv_eq (hint.tower_top (A := ℚ)) hfix
  obtain ⟨n, hn⟩ := isIntegral_rat_imp_int (hq ▸ hint)
  exact ⟨n, hq.trans hn⟩

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


