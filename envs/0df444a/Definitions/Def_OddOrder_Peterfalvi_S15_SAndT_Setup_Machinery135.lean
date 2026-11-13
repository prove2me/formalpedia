-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:38:45.625696+00:00
-- url     : https://prove2.me/theorems/6d9eabe9-a8bd-48c0-a45b-839c8eb508e1
-- title:
--   Peterfalvi (13.3)–(13.5): machinery for the character-degree analysis
-- statement:
--   Formalizes machinery for Peterfalvi (13.3): reducibility of the $\mu$-column sums, the $\lambda$-free core of the character-degree argument, and the $\lambda$-cluster of (13.3.b).
--
--   Main declarations: `Hypothesis.mu_colSum_not_irreducible` (The `μ`-column sums are reducible); `CharacterDegreeCore` (The λ-free core of Peterfalvi (13.3)); `LambdaClusterData` (The λ-cluster of Peterfalvi (13.3.b)); `Hypothesis.eta_orthonormal` (The `η`-grid is orthonormal).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical in
/-- **The `μ`-column sums are reducible** ((13.3.a) entry condition): `μ_j = ∑_i μ_{ij}` is a
sum of `q ≥ 2` *distinct* irreducible characters (`mu_irreducible`, `mu_col_injective`), so its
norm is `q ≠ 1` — not an irreducible character.  This is the membership shape that puts `μ_j`
among the `p − 1` reducible members of `𝒮(H₀)` in the §9 analysis (Pf (9.8.b)/(9.9.b)). -/
theorem Hypothesis.mu_colSum_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter (∑ i : Fin hyp.q, hyp.mu i j) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro hirr
  set a : Fin hyp.q → OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S :=
    fun i => ⟨hyp.mu i j, hyp.mu_irreducible i j⟩ with ha
  have hcond : ∀ i i' : Fin hyp.q, a i = a i' ↔ i = i' := by
    intro i i'
    constructor
    · intro h
      exact hyp.mu_col_injective j (congrArg
        (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) h)
    · rintro rfl
      rfl
  have hinner : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j)
      (∑ i : Fin hyp.q, hyp.mu i j) = (hyp.q : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ i : Fin hyp.q, ClassFunction.inner (hyp.mu i j) (∑ i' : Fin hyp.q, hyp.mu i' j)
        = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, ClassFunction.inner (hyp.mu i j) (hyp.mu i' j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, if i = i' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
            (a i) (a i')
          rw [ha] at hite
          exact hite.trans (if_congr (hcond i i') rfl rfl)
      _ = ∑ _i : Fin hyp.q, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
      _ = (hyp.q : ℂ) := by simp
  have h1 : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j)
      (∑ i : Fin hyp.q, hyp.mu i j) = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨∑ i : Fin hyp.q, hyp.mu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨∑ i : Fin hyp.q, hyp.mu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
    simpa using hite
  rw [hinner] at h1
  have : hyp.q = 1 := by exact_mod_cast h1
  exact hyp.q_prime.one_lt.ne' this

open scoped FiniteInduce in
/-- **The λ-free core of Peterfalvi (13.3)** (issue 9094 RULING 案 A + issue 2035 更新 #22): the
`τ₁`-maps and the unconditionally-available (13.3.a/c) facts, **without** the λ-cluster (which is
conditional on `𝒮` containing an irreducible `uq`-degree `PC`-induced member — Pf (13.3.b) is a
dichotomy).  Mirrors Coq `PFsection13`'s factoring: the λ-free Section `Thirteen_2_3_5_to_9`
exports these unconditionally, the λ-facts are `Variable`-scoped.

The τ₁-fields carry the **`P ⊄ Ker` guards** (2035 更新 #22): the coherence `IsCoherent` pins
`τ₁` only on `ℤ[𝒮]`, and `Ind_{PC}^S θ ∈ ℤ[𝒮]` requires `P ⊄ Ker θ` ((1.5.a)); Peterfalvi's
(13.5) proof converts `τ₁ ↔ Ind_S^G` only on such `𝒮₁`-members, the `P`-kernel side staying
inside the unknown `α` of (13.5.a).  The unconditional-in-`θ` shapes of the legacy
`CharacterDegreeData` fields are *not suppliable* from the (9.11) coherence.  The `μ`-fields
carry the matching `P ⊄ Ker` **witness** (`mu_j_isIndPC_not_ker`: `μ_j ∈ 𝒮₁`), which is what the
(13.5)-consumers thread into the guards. -/
structure CharacterDegreeCore (hyp : Hypothesis (G := G)) where
  tau1S : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G
  tau1T : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G
  /-- **(13.2.e)+(7.2), τ₁-extension semantics** on `𝒮₁`-differences: `τ₁` agrees with
  `Ind_S^G` on zero-degree differences of `P`-nonkernel `H`-induced irreducibles. -/
  tau1S_apply_induce_sub :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
          - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
        = ClassFunction.induce hyp.S
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
              - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **The τ₁ coherence isometry on the `𝒮₁`-family**. -/
  tau1S_inner_induce :
    haveI := hyp.finiteG
    ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ' →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ') →
      ClassFunction.inner (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ))
          (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ'))
        = ClassFunction.inner (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)
            (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ')
  /-- **τ₁ sends `𝒮₁`-members to virtual characters**. -/
  tau1S_induce_mem_ZIrr :
    haveI := hyp.finiteG
    ∀ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) ∈ ZIrr G
  /-- **(4.1)+(5.3.b): grid orthogonality of τ₁-images of *irreducibly*-induced `𝒮₁`-members**. -/
  tau1S_induce_inner_eta :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (j : Fin hyp.p) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) →
      ClassFunction.inner (hyp.eta i j)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **(4.1)+(5.3.b)+(13.3.c): column-`0` orthogonality for *every* `𝒮₁`-member** (irreducible
  or `μ`-column). -/
  tau1S_induce_inner_eta_col_zero :
    haveI := hyp.finiteG
    ∀ (i : Fin hyp.q) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ →
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) →
      ClassFunction.inner (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
        (tau1S (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) = 0
  /-- **(13.3.a)+(13.3.c), the distinguished `μ`-column** with the `𝒮₁`-membership witness. -/
  mu_col_tau1_eta_col_one :
    haveI := hyp.finiteG
    ∃ (j : Fin hyp.p) (δ : ℤ) (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ),
      j ≠ ⟨0, hyp.p_prime.pos⟩ ∧
      (δ = 1 ∨ δ = -1) ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
      ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
          Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) ∧
      (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
      tau1S (∑ i : Fin hyp.q, hyp.mu i j)
        = (δ : ℂ) • ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩
  /-- **(13.3.a) with the `𝒮₁`-witness**: every nonzero column sum is induced from a linear
  character of `H = PC` with `P ⊄ Ker`. -/
  mu_j_linear_induced :
    haveI := hyp.finiteG
    ∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
          ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
              Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel θ) ∧
          (∑ i : Fin hyp.q, hyp.mu i j) = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ
  /-- **(13.3.c), the `S`-side signs**: the `δ_j` are all `1`.

  δ′-half (`∀ i, hyp.deltaPrime i = 1`) は consumer 0 (issue 2035 #92 実測) につき
  restate-drop; 供給は `deltaPrime_eq_one_T` (`S15_CharacterDegreeEnginesSSide`) に残存、
  T-mirror 消費者が現れたら field として再追加する. -/
  delta_eq_one : ∀ j : Fin hyp.p, hyp.delta j = 1
  /-- **(13.3.c)**: the `τ₁`-images of the nonzero column sums are the `η`-column sums. -/
  mu_tau1_formula :
    (∀ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j) ∨
    (hyp.p = 3 ∧ ∀ j j' : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ →
      j' ≠ ⟨0, hyp.p_prime.pos⟩ → j ≠ j' →
      tau1S (∑ i : Fin hyp.q, hyp.mu i j) = -∑ i : Fin hyp.q, hyp.eta i j')

open scoped FiniteInduce in
/-- **The λ-cluster of Peterfalvi (13.3.b)** (issue 9094 RULING 案 A): the distinguished
irreducible `λ ∈ Irr S` of degree `uq` induced from a linear character of `H = PC` with
`P ⊄ Ker` — the data whose existence is the *conditional* branch of the (13.3.b) dichotomy
("if `𝒮` contains no such character, then (9.7.b) holds with `C = 1`,
`u = (p^q−1)/(p−1)`").  Mirrors Coq's `Variable lambda … Hypotheses (Slam) (irrHlam)`
(`PFsection13:961-962`, Section `Thirteen_10_to_13_15`).  The maps and their (13.3) facts live
in the λ-free `CharacterDegreeCore`. -/
structure LambdaClusterData (hyp : Hypothesis (G := G)) where
  lambda : ClassFunction ↥hyp.S ℂ
  lambda_irreducible : OddOrder.RepresentationTheory.IsIrreducibleCharacter lambda
  lambda_degree : lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ)
  lambda_induced_from_PC_linear :
    haveI := hyp.finiteG
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        lambda = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∧
        ∃ x : ↥(hyp.H.subgroupOf hyp.S), ((x : ↥hyp.S) : G) ∈ hyp.P ∧
          x ∉ OddOrder.Peterfalvi.S03.characterKernel θ

open scoped FiniteInduce in
/-- **The `η`-grid is orthonormal** ((13.1.d) + (3.2)/(3.3), issue 9013 (13.4)-prep): the grid
`η_{ij} = ω_{ij}^{τ₃}` inherits the (3.3) orthonormality of the `ω`-grid through the (3.2)
isometry `τ₃`.  The bookkeeping input of the (13.4) cross-expansion. -/
theorem Hypothesis.eta_orthonormal [Finite G] (hyp : Hypothesis (G := G))
    (i k : Fin hyp.q) (j l : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) (hyp.eta k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]

open scoped FiniteInduce in
/-- **The `μ`-column sum has squared norm `q`** (issue 2035, (13.3.c) pin step 2): the reducible
prime-TI character `μ_j = ∑_i μ_{ij}` is a sum of `q` orthonormal irreducibles (`mu_orthonormal`),
so `⟨μ_j, μ_j⟩ = q`.  Through the coherence isometry (`extension_inner_eq`) this pins
`‖τ₁ μ_j‖² = q`, one of the two positive-definiteness inputs of the (13.3.c) column pin. -/
theorem Hypothesis.muColumn_inner_self [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j) (∑ i : Fin hyp.q, hyp.mu i j)
      = (hyp.q : ℂ) := by
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  have hrow : ∀ i : Fin hyp.q,
      ClassFunction.inner (hyp.mu i j) (∑ k : Fin hyp.q, hyp.mu k j) = (1 : ℂ) := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_single i
        (fun k _ hki => by rw [hyp.mu_orthonormal i k j j, if_neg (fun h => hki h.1.symm)])
        (fun h => absurd (Finset.mem_univ i) h),
      hyp.mu_orthonormal i i j j]
    simp
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

open scoped FiniteInduce in
/-- **The `η`-column sum has squared norm `q`** (issue 2035, (13.3.c) pin step 1): the aligned
grid column `∑_i η_{ij}` is a sum of `q` orthonormal virtual characters (`eta_orthonormal`), so
`⟨∑_i η_{ij}, ∑_i η_{ij}⟩ = q`.  The other positive-definiteness input of the (13.3.c) column
pin `τ₁ μ_j = δ_j·∑_i η_{ij}`. -/
theorem Hypothesis.etaColumn_inner_self [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.eta i j) (∑ i : Fin hyp.q, hyp.eta i j)
      = (hyp.q : ℂ) := by
  rw [OddOrder.RepresentationTheory.inner_sum_left]
  have hrow : ∀ i : Fin hyp.q,
      ClassFunction.inner (hyp.eta i j) (∑ k : Fin hyp.q, hyp.eta k j) = (1 : ℂ) := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_single i
        (fun k _ hki => by rw [hyp.eta_orthonormal i k j j, if_neg (fun h => hki h.1.symm)])
        (fun h => absurd (Finset.mem_univ i) h),
      hyp.eta_orthonormal i i j j]
    simp
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **Peterfalvi (8.5.a)**: `H = PC = F(S)`.  The type-`P` carrier `Sdata` records (8.5.a),
`F(S) = M_F · C_U(M_F) = M_F ⊔ (U ⊓ C_S(M_F))`, as its `fitting_eq` field (`TypePData.fitting_eq`,
whose left side is the ambient realization `(fitting ↥S).map S.subtype = fittingInG S`).
Reconciled through `P = M_F = Sdata.H` (`P_eq_SF`/`Sdata.H_eq`) and `Sdata.U = U` (`Sdata_U_eq`),
the right side is exactly `P ⊔ (U ⊓ C_S(P)) = P ⊔ C = H`.  This §8 identity makes the (13.5)
ρ-machinery unconditional, superseding the σ-structure-gated P-abelian route of issue 4013:
`Sdata.fitting_eq` *is* (8.5.a). -/
theorem Hypothesis.H_eq_fittingInG (hyp : Hypothesis (G := G)) :
    hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := by
  have hPH : hyp.P = hyp.Sdata.H := by rw [hyp.P_eq_SF, hyp.Sdata.H_eq]
  change hyp.P ⊔ hyp.C = OddOrder.BG.Ch2.S08.fittingInG hyp.S
  rw [hyp.C_eq, hPH, ← hyp.Sdata_U_eq]
  exact hyp.Sdata.fitting_eq.symm

/-- **Peterfalvi (8.5.a)/(8.6.a)**: `H^# = (PC)^#` is a TI-subset of `G` with normalizer `S` —
distinct `G`-conjugates of `H^#` meet trivially, and any conjugator landing `H^#` back in `H^#` lies
in `S`.  The §8 structural input to the (13.5) ρ-machinery.

Proof: `H = F(S)` (`H_eq_fittingInG`, the carrier's (8.5.a) `fitting_eq`), and `F(S)^#` is a
TI-subset with normalizer `N_G(F(S)) = S` — BG (15.7)(a), through the type-uniform
`S13.fittingIsTI_of_isTypeNonI`, with
`normalizer_fittingInAmbient_eq_self` pinning the bound to `S`.
Rewriting `H^# = F(S)^#` closes it. -/
theorem H_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.GroupTheory.IsTISubset (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hTI : OddOrder.BG.Ch4.S15.FittingIsTI hyp.S :=
    OddOrder.Peterfalvi.S13.fittingIsTI_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  have hTI0 : OddOrder.GroupTheory.IsTISubset (OddOrder.BG.Ch4.S15.fittingSharp hyp.S)
      (Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G)) := hTI
  rw [hnorm] at hTI0
  -- `H^# = F(S)^#` as sets, so the TI property transfers.
  have hset : OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)
      = OddOrder.BG.Ch4.S15.fittingSharp hyp.S := by
    change (hyp.H : Set G) \ {1}
      = (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) \ {1}
    rw [hHF]
  rw [hset]
  exact hTI0

/-- **Peterfalvi (8.5.a)**: `S` normalizes `H^# = (PC)^#` (the `S`-side of `S = N_G(H^#)`).

Proof: `H = F(S)` (`H_eq_fittingInG`) and `S = N_G(F(S))` (`normalizer_fittingInAmbient_eq_self`),
so every `l ∈ S` normalizes `F(S)`; conjugation keeps `a ∈ F(S)^#` inside `F(S)` and
nonidentity. -/
theorem S_normalizes_H_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.S) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haH, ha1⟩ := ha
  rw [hHF] at haH ⊢
  have hlnorm : (l : G) ∈
      Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haH, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **Peterfalvi (13.5)/(7.1)**: the §4 Dade hypothesis for the TI-subset `(S, H^#)`.  Since `H^#`
is a
TI-subset of `G` with normalizer `S` ((8.5.a)/(8.6.a)), `S04.of_isTISubset` builds the Dade datum
(whose local subgroups `H(a) = ⊥`) whose isometry is the `τ = Ind_S^G` powering the (13.5)
ρ-machinery
((7.7.a) `chiRho_explicit_formula` applied to `(S, H^#)`).  The structural inputs `H^# ⊆ G^#` and
`H = PC ≤ S` (`P = S_F ≤ S`, `C ≤ U ≤ M' = [S,S] ≤ S`) are discharged here; the TI/normalizer
content
is the §8 obligation `H_sharp_isTISubset`/`S_normalizes_H_sharp`.  The Dade foundation of the (13.5)
engine. -/
noncomputable def H_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (S_normalizes_H_sharp hG hyp)
    (H_sharp_isTISubset hG hyp)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hHS (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5)/(7.1)**: the (7.1) ρ-hypothesis for `(S, H^#)`.  Mirrors
`S14.toHypothesis71`:
the Dade isometry `τ` is the `fullDadeIsometryData` of the (13.5) Dade datum
`H_sharp_dadeHypothesis` ((2.4.a) is the theorem `S04.Hypothesis.hConjInvariant`).  This is the
(7.1) datum on which `chiRho` (the `ρ` map) and — once the coherence datum is supplied — the
(7.7.a) `chiRho_explicit_formula` of the (13.5) point formula are evaluated. -/
noncomputable def H_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S :=
  { hyp := H_sharp_dadeHypothesis hG hyp
    τ := ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData).toDadeIsometryData.toDadeMap
    isDadeMap :=
      ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData).toDadeIsometryData.isDadeMap }

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5)/(7.6)**: the (7.6) coherent-family datum for `(S, H^#)`, with its (7.7.a)
certificate.  Built from the (7.1) ρ-hypothesis `H_sharp_hypothesis71` and the Dade-isometry
property
via `S09.hypothesis76OfDade` (issue-1013: the whole `Hypothesis76`, *including* the (7.7.a)
`chiRho_decomp`, is constructible from `(7.1)` data alone — the induced family `{Ind_H^S θ}` is the
`exists_distinct_induced_family` enumeration, the certificate is `chiRho_decomp_induced`). The
normal
subgroup is `H = PC ⊴ S` (`S` normalizes `H^#` ⟹ normalizes `H`).  This is the datum on which the
(13.5.a) point formula `chiRho_explicit_formula` (7.7.a) is read off. -/
noncomputable def H_sharp_hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S :=
        by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeTrivialBase (H_sharp_hypothesis71 hG hyp) ?_
      hyp.H ?_ ?_ rfl
  · exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData).toDadeIsometryData.isDadeIsometry
  · have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  · intro l h hh
    by_cases h1 : h = 1
    · subst h1; simp
    · have hsh : h ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
        OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hh, h1⟩
      exact (OddOrder.Peterfalvi.S04.mem_sharp.mp (S_normalizes_H_sharp hG hyp l hsh)).1

end OddOrder.Peterfalvi.S15


