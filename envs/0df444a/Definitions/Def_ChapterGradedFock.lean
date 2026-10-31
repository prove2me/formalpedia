-- Prove2me | Definitions.Def_ChapterGradedFock
-- name    : ChapterGradedFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:27:04.963086+00:00
-- url     : https://prove2.me/theorems/6db7f149-5a44-4fe5-b687-70892176a4a0
-- title:
--   Chapter GradedFock
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGradedFock.lean`): generated def bundle for ChapterGradedFock. See BookProof/ChapterGradedFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGradedFock.lean

import Definitions.Def_ChapterFermionFock
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA_of_ne
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_annA
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_creA_creA


/-!
# Chapter GradedFock — the graded Fock space `Γˢ ⊗ Γᵃ` and its superalgebra

`CONSOLIDATED_PLAN.md` §10.6.2 item 3 asks for the second quantization on the
**graded** Fock space `Γˢ ⊗ Γᵃ` "with the `ℤ₂`-graded superalgebra and the
fermionic CAR half".  `BookProof.ChapterFermionFock` supplies the fermionic half
`Γᵃ`; `BookProof.ChapterFockSecondQuantization` the bosonic half `Γˢ`; and
`BookProof.ChapterSuperBracket` the *abstract* super-bracket
`⟦a,b⟧ = ab − ε(p,q)·ba` together with the graded Jacobi identity.  This chapter
glues the three: it builds the graded Fock space over a product configuration
space and shows that the bosonic and fermionic creation/annihilation operators
living on it satisfy the book's **single unified graded relation**.

## Deliverables

* `otimes` — the elementary tensor `v ⊗ w` of finitely supported functions, with
  its bilinearity and `otimes_single`;
* `liftFst`, `liftSnd` — the two embeddings `T ↦ T ⊗ 1` and `S ↦ 1 ⊗ S` of the
  operator algebras of the factors into that of the product, together with the
  structural facts that make them algebra maps (`liftFst_mul`, `liftFst_one`,
  `liftFst_add`, `liftFst_sub`, …) and the key
  `liftFst_liftSnd_comm`: **operators on different tensor factors commute**;
* `GConf`, `GradedAlg`, `GFock` — the graded configuration space
  `Conf × FConf`, the algebraic graded Fock space and the Hilbert space
  `ℓ²(Conf × FConf) ≅ Γˢ ⊗ Γᵃ`;
* `bcre`, `bann`, `fcre`, `fann` — the bosonic (even) and fermionic (odd)
  creation and annihilation operators on the graded space;
* `super_canonical` — **the headline**: with the Koszul sign of
  `ChapterSuperBracket`,
  `⟦ a(p,j), a†(q,k) ⟧ = δ_{pq} δ_{jk}`,
  i.e. the *same* formula gives the bosonic **commutator** CCR, the fermionic
  **anticommutator** CAR, and the vanishing of the mixed brackets;
  `super_canonical_cre` and `super_canonical_ann` are its two companions;
* `gradeOp` — the `ℤ₂` grading operator `(−1)^{N_f}`: an involution
  (`gradeOp_involutive`) that commutes with the bosonic operators
  (`gradeOp_bcre`, `gradeOp_bann`) and anticommutes with the fermionic ones
  (`gradeOp_fcre`, `gradeOp_fann`);
* `evenPart`, `oddPart`, `even_add_odd`, `gradeOp_evenPart`, `gradeOp_oddPart` —
  the resulting `ℤ₂` decomposition `Γˢ ⊗ Γᵃ = (Γˢ ⊗ Γᵃ)₊ ⊕ (Γˢ ⊗ Γᵃ)₋`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.GradedFock

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockSecondQuantization BookProof.FermionFock
open BookProof.ChapterSuperBracket

noncomputable section

/-! ## Elementary tensors of finitely supported functions -/

section Tensor

variable {α β : Type*}

/-- The **elementary tensor** `v ⊗ w`, as a finitely supported function on the
product of the index types. -/
def otimes (v : α →₀ ℂ) (w : β →₀ ℂ) : (α × β) →₀ ℂ :=
  Finsupp.onFinset (v.support ×ˢ w.support) (fun p => v p.1 * w p.2) (by
    intro p hp
    rcases mul_ne_zero_iff.mp hp with ⟨h1, h2⟩
    exact Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr h1, Finsupp.mem_support_iff.mpr h2⟩)

@[simp] theorem otimes_apply (v : α →₀ ℂ) (w : β →₀ ℂ) (p : α × β) :
    otimes v w p = v p.1 * w p.2 := rfl

@[simp] theorem otimes_zero_left (w : β →₀ ℂ) : otimes (0 : α →₀ ℂ) w = 0 := by
  ext p; simp

@[simp] theorem otimes_zero_right (v : α →₀ ℂ) : otimes v (0 : β →₀ ℂ) = 0 := by
  ext p; simp

theorem otimes_add_left (v v' : α →₀ ℂ) (w : β →₀ ℂ) :
    otimes (v + v') w = otimes v w + otimes v' w := by
  ext p; simp [add_mul]

theorem otimes_add_right (v : α →₀ ℂ) (w w' : β →₀ ℂ) :
    otimes v (w + w') = otimes v w + otimes v w' := by
  ext p; simp [mul_add]

theorem otimes_neg_left (v : α →₀ ℂ) (w : β →₀ ℂ) :
    otimes (-v) w = - otimes v w := by
  ext p; simp

theorem otimes_neg_right (v : α →₀ ℂ) (w : β →₀ ℂ) :
    otimes v (-w) = - otimes v w := by
  ext p; simp

theorem otimes_smul_left (c : ℂ) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    otimes (c • v) w = c • otimes v w := by
  ext p; simp [mul_assoc]

theorem otimes_smul_right (c : ℂ) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    otimes v (c • w) = c • otimes v w := by
  ext p; simp only [otimes_apply, Finsupp.smul_apply, smul_eq_mul]; ring

theorem otimes_single (a : α) (b : β) (x y : ℂ) :
    otimes (Finsupp.single a x) (Finsupp.single b y) = Finsupp.single (a, b) (x * y) := by
  ext p
  obtain ⟨a', b'⟩ := p
  simp only [otimes_apply]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2]

theorem single_eq_otimes (a : α) (b : β) (c : ℂ) :
    (Finsupp.single (a, b) c : (α × β) →₀ ℂ)
      = otimes (Finsupp.single a c) (Finsupp.single b 1) := by
  rw [otimes_single, mul_one]

/-- Two linear maps out of `(α × β) →₀ ℂ` agree as soon as they agree on the
elementary tensors. -/
theorem prod_linear_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : ((α × β) →₀ ℂ) →ₗ[ℂ] N}
    (h : ∀ (v : α →₀ ℂ) (w : β →₀ ℂ), f (otimes v w) = g (otimes v w)) : f = g := by
  refine LinearMap.ext fun u => ?_
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | single ab c =>
    obtain ⟨a, b⟩ := ab
    rw [single_eq_otimes]
    exact h _ _

/-! ## Operators on one tensor factor -/

/-- `T ↦ T ⊗ 1`: an operator of the first factor, acting on the product. -/
def liftFst (T : (α →₀ ℂ) →ₗ[ℂ] (α →₀ ℂ)) : ((α × β) →₀ ℂ) →ₗ[ℂ] ((α × β) →₀ ℂ) :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (otimes (T (Finsupp.single p.1 1)) (Finsupp.single p.2 (1 : ℂ)))

/-- `S ↦ 1 ⊗ S`: an operator of the second factor, acting on the product. -/
def liftSnd (S : (β →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ)) : ((α × β) →₀ ℂ) →ₗ[ℂ] ((α × β) →₀ ℂ) :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (otimes (Finsupp.single p.1 (1 : ℂ)) (S (Finsupp.single p.2 1)))

theorem liftFst_single (T : (α →₀ ℂ) →ₗ[ℂ] (α →₀ ℂ)) (a : α) (b : β) (c : ℂ) :
    liftFst (β := β) T (Finsupp.single (a, b) c)
      = c • otimes (T (Finsupp.single a 1)) (Finsupp.single b (1 : ℂ)) := by
  rw [liftFst, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem liftSnd_single (S : (β →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ)) (a : α) (b : β) (c : ℂ) :
    liftSnd (α := α) S (Finsupp.single (a, b) c)
      = c • otimes (Finsupp.single a (1 : ℂ)) (S (Finsupp.single b 1)) := by
  rw [liftSnd, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- `T ⊗ 1` acts on the first factor of an elementary tensor. -/
theorem liftFst_otimes (T : (α →₀ ℂ) →ₗ[ℂ] (α →₀ ℂ)) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    liftFst T (otimes v w) = otimes (T v) w := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [otimes_add_left, map_add, hf, hg, map_add, otimes_add_left]
  | single a x =>
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [otimes_add_right, map_add, hf, hg, otimes_add_right]
    | single b y =>
      have hx : (Finsupp.single a x : α →₀ ℂ) = x • Finsupp.single a 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hy : (Finsupp.single b y : β →₀ ℂ) = y • Finsupp.single b 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [otimes_single, liftFst_single, hx, hy, map_smul, otimes_smul_left,
        otimes_smul_right, smul_smul]

/-- `1 ⊗ S` acts on the second factor of an elementary tensor. -/
theorem liftSnd_otimes (S : (β →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ)) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    liftSnd S (otimes v w) = otimes v (S w) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [otimes_add_left, map_add, hf, hg, otimes_add_left]
  | single a x =>
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [otimes_add_right, map_add, hf, hg, map_add, otimes_add_right]
    | single b y =>
      have hx : (Finsupp.single a x : α →₀ ℂ) = x • Finsupp.single a 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hy : (Finsupp.single b y : β →₀ ℂ) = y • Finsupp.single b 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [otimes_single, liftSnd_single, hx, hy, map_smul, otimes_smul_left,
        otimes_smul_right, smul_smul]

section Algebra

variable (T T' : Module.End ℂ (α →₀ ℂ)) (S S' : Module.End ℂ (β →₀ ℂ))

theorem liftFst_mul : (liftFst (β := β) T) * (liftFst T') = liftFst (T * T') := by
  refine prod_linear_ext fun v w => ?_
  rw [Module.End.mul_apply, liftFst_otimes, liftFst_otimes, liftFst_otimes,
    Module.End.mul_apply]

theorem liftSnd_mul : (liftSnd (α := α) S) * (liftSnd S') = liftSnd (S * S') := by
  refine prod_linear_ext fun v w => ?_
  rw [Module.End.mul_apply, liftSnd_otimes, liftSnd_otimes, liftSnd_otimes,
    Module.End.mul_apply]

theorem liftFst_one : liftFst (β := β) (1 : Module.End ℂ (α →₀ ℂ)) = 1 := by
  refine prod_linear_ext fun v w => ?_
  rw [liftFst_otimes]
  rfl

theorem liftSnd_one : liftSnd (α := α) (1 : Module.End ℂ (β →₀ ℂ)) = 1 := by
  refine prod_linear_ext fun v w => ?_
  rw [liftSnd_otimes]
  rfl

theorem liftFst_add : liftFst (β := β) (T + T') = liftFst T + liftFst T' := by
  refine prod_linear_ext fun v w => ?_
  simp only [LinearMap.add_apply, liftFst_otimes, otimes_add_left]

theorem liftSnd_add : liftSnd (α := α) (S + S') = liftSnd S + liftSnd S' := by
  refine prod_linear_ext fun v w => ?_
  simp only [LinearMap.add_apply, liftSnd_otimes, otimes_add_right]

theorem liftFst_neg : liftFst (β := β) (-T) = - liftFst T := by
  refine prod_linear_ext fun v w => ?_
  simp only [LinearMap.neg_apply, liftFst_otimes, otimes_neg_left]

theorem liftSnd_neg : liftSnd (α := α) (-S) = - liftSnd S := by
  refine prod_linear_ext fun v w => ?_
  simp only [LinearMap.neg_apply, liftSnd_otimes, otimes_neg_right]

theorem liftFst_sub : liftFst (β := β) (T - T') = liftFst T - liftFst T' := by
  have h1 : (T - T' : Module.End ℂ (α →₀ ℂ)) = T + -T' := sub_eq_add_neg T T'
  have h2 : liftFst (β := β) T - liftFst (β := β) T' = liftFst (β := β) T + -liftFst (β := β) T' :=
    sub_eq_add_neg (liftFst (β := β) T) (liftFst (β := β) T')
  rw [h1, liftFst_add, liftFst_neg, h2]

theorem liftSnd_sub : liftSnd (α := α) (S - S') = liftSnd S - liftSnd S' := by
  have h1 : (S - S' : Module.End ℂ (β →₀ ℂ)) = S + -S' := sub_eq_add_neg S S'
  have h2 : liftSnd (α := α) S - liftSnd (α := α) S' = liftSnd (α := α) S + -liftSnd (α := α) S' :=
    sub_eq_add_neg (liftSnd (α := α) S) (liftSnd (α := α) S')
  rw [h1, liftSnd_add, liftSnd_neg, h2]

theorem liftFst_zero : liftFst (β := β) (0 : Module.End ℂ (α →₀ ℂ)) = 0 := by
  refine prod_linear_ext fun v w => ?_
  rw [liftFst_otimes]
  simp

theorem liftSnd_zero : liftSnd (α := α) (0 : Module.End ℂ (β →₀ ℂ)) = 0 := by
  refine prod_linear_ext fun v w => ?_
  rw [liftSnd_otimes]
  simp

/-- **Operators acting on different tensor factors commute.** -/
theorem liftFst_liftSnd_comm : (liftFst (β := β) T) * (liftSnd S) = (liftSnd S) * (liftFst T) := by
  refine prod_linear_ext fun v w => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, liftSnd_otimes, liftFst_otimes,
    liftFst_otimes, liftSnd_otimes]

end Algebra

end Tensor

/-! ## The graded Fock space -/

/-- A **graded configuration**: a bosonic occupation-number configuration
together with a fermionic occupied set. -/
abbrev GConf := Conf × FConf

/-- The **algebraic graded Fock space** `Γˢ ⊗ Γᵃ`. -/
abbrev GradedAlg := GConf →₀ ℂ

/-- The **graded Fock space** `ℓ²(Conf × FConf) ≅ Γˢ(ℓ²) ⊗ Γᵃ(ℓ²)`. -/
abbrev GFock := L2I GConf

/-- The bosonic (even) creation operator on the graded Fock space. -/
def bcre (j : ℕ) : Module.End ℂ GradedAlg := liftFst (creA j)

/-- The bosonic (even) annihilation operator on the graded Fock space. -/
def bann (j : ℕ) : Module.End ℂ GradedAlg := liftFst (annA j)

/-- The fermionic (odd) creation operator on the graded Fock space. -/
def fcre (j : ℕ) : Module.End ℂ GradedAlg := liftSnd (creF j)

/-- The fermionic (odd) annihilation operator on the graded Fock space. -/
def fann (j : ℕ) : Module.End ℂ GradedAlg := liftSnd (annF j)

/-! ### The canonical relations of the two factors, as operator identities -/

theorem annA_creA_end (j : ℕ) :
    (annA j) * (creA j) - (creA j) * (annA j) = (1 : Module.End ℂ FockAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply] using
    ccr_annA_creA j u

theorem annA_creA_end_of_ne {j k : ℕ} (h : j ≠ k) :
    (annA j) * (creA k) - (creA k) * (annA j) = (0 : Module.End ℂ FockAlg) := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ccr_annA_creA_of_ne h, sub_self]

theorem annA_annA_end (j k : ℕ) :
    (annA j) * (annA k) - (annA k) * (annA j) = (0 : Module.End ℂ FockAlg) := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ccr_annA_annA j k, sub_self]

theorem creA_creA_end (j k : ℕ) :
    (creA j) * (creA k) - (creA k) * (creA j) = (0 : Module.End ℂ FockAlg) := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ccr_creA_creA j k, sub_self]

theorem annF_creF_end (j : ℕ) :
    (annF j) * (creF j) + (creF j) * (annF j) = (1 : Module.End ℂ FermiAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using
    car_annF_creF_self j u

theorem annF_creF_end_of_ne {j k : ℕ} (h : j ≠ k) :
    (annF j) * (creF k) + (creF k) * (annF j) = (0 : Module.End ℂ FermiAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using
    car_annF_creF_of_ne h u

theorem annF_annF_end (j k : ℕ) :
    (annF j) * (annF k) + (annF k) * (annF j) = (0 : Module.End ℂ FermiAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using
    car_annF_annF j k u

theorem creF_creF_end (j k : ℕ) :
    (creF j) * (creF k) + (creF k) * (creF j) = (0 : Module.End ℂ FermiAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using
    car_creF_creF j k u

/-! ### The unified graded canonical relation -/

/-- The annihilation operator of parity `p` (`false` = bosonic, `true` =
fermionic) and mode `j`. -/
def gAnn : Bool → ℕ → Module.End ℂ GradedAlg
  | false, j => bann j
  | true, j => fann j

/-- The creation operator of parity `p` and mode `j`. -/
def gCre : Bool → ℕ → Module.End ℂ GradedAlg
  | false, j => bcre j
  | true, j => fcre j

/-- Local copies of the Koszul-sign facts: the published
`Def_ChapterSuperBracket` bundle exports only `eps`/`sbracket` themselves
(their lemmas live in the separate `ChapterSuperBracket` theorem nodes), so a
bundle that rewrites with them must carry its own copy. -/
lemma eps_false_left (q : Bool) : eps false q = 1 := by
  simp [eps]

lemma eps_false_right (p : Bool) : eps p false = 1 := by
  simp [eps]

lemma eps_true_true : eps true true = -1 := by
  simp [eps]

lemma sbracket_even_even (a b : Module.End ℂ GradedAlg) :
    sbracket false false a b = a * b - b * a := by
  rw [sbracket, eps_false_left]
  norm_num

lemma sbracket_odd_odd (a b : Module.End ℂ GradedAlg) :
    sbracket true true a b = a * b + b * a := by
  -- The operator-level ring (`Module.End`) has instance paths for `*`/`-`/numerals
  -- that do not match library patterns syntactically, so `rw`/`norm_num`/`simp`
  -- all stall at `(-1 : Module.End) * (b * a)`.  Go pointwise: at the base ring
  -- the standard simp lemmas apply and `simp` closes it.
  refine LinearMap.ext fun u => ?_
  simp only [sbracket, eps_true_true]
  simp

theorem sbracket_even_odd (a b : Module.End ℂ GradedAlg) :
    sbracket false true a b = a * b - b * a := by
  rw [sbracket, eps_false_left]
  norm_num

theorem sbracket_odd_even (a b : Module.End ℂ GradedAlg) :
    sbracket true false a b = a * b - b * a := by
  rw [sbracket, eps_false_right]
  norm_num

/-- **The unified graded canonical relation.**  With the Koszul sign of
`ChapterSuperBracket`, one formula covers all four cases:
`⟦a(p,j), a†(q,k)⟫ = δ_{pq} δ_{jk}` — a **commutator** for two bosonic
operators, an **anticommutator** for two fermionic ones, and a vanishing
(commutator) bracket across the two sectors. -/
theorem super_canonical (p q : Bool) (j k : ℕ) :
    sbracket p q (gAnn p j) (gCre q k) = if p = q ∧ j = k then 1 else 0 := by
  cases p <;> cases q <;>
    simp only [gAnn, gCre, bann, bcre, fann, fcre, sbracket_even_even,
      sbracket_even_odd, sbracket_odd_even, sbracket_odd_odd]
  · -- bosonic / bosonic
    rcases eq_or_ne j k with rfl | h
    · rw [liftFst_mul, liftFst_mul, ← liftFst_sub, annA_creA_end, liftFst_one,
        if_pos (by simp)]
    · rw [liftFst_mul, liftFst_mul, ← liftFst_sub, annA_creA_end_of_ne h, liftFst_zero,
        if_neg (by simp [h])]
  · -- bosonic / fermionic
    rw [liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · -- fermionic / bosonic
    rw [← liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · -- fermionic / fermionic
    rcases eq_or_ne j k with rfl | h
    · rw [liftSnd_mul, liftSnd_mul, ← liftSnd_add, annF_creF_end, liftSnd_one,
        if_pos (by simp)]
    · rw [liftSnd_mul, liftSnd_mul, ← liftSnd_add, annF_creF_end_of_ne h, liftSnd_zero,
        if_neg (by simp [h])]

/-- The graded bracket of two creation operators vanishes. -/
theorem super_canonical_cre (p q : Bool) (j k : ℕ) :
    sbracket p q (gCre p j) (gCre q k) = 0 := by
  cases p <;> cases q <;>
    simp only [gCre, bcre, fcre, sbracket_even_even, sbracket_even_odd,
      sbracket_odd_even, sbracket_odd_odd]
  · rw [liftFst_mul, liftFst_mul, ← liftFst_sub, creA_creA_end, liftFst_zero]
  · rw [liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · rw [← liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · rw [liftSnd_mul, liftSnd_mul, ← liftSnd_add, creF_creF_end, liftSnd_zero]

/-- The graded bracket of two annihilation operators vanishes. -/
theorem super_canonical_ann (p q : Bool) (j k : ℕ) :
    sbracket p q (gAnn p j) (gAnn q k) = 0 := by
  cases p <;> cases q <;>
    simp only [gAnn, bann, fann, sbracket_even_even, sbracket_even_odd,
      sbracket_odd_even, sbracket_odd_odd]
  · rw [liftFst_mul, liftFst_mul, ← liftFst_sub, annA_annA_end, liftFst_zero]
  · rw [liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · rw [← liftFst_liftSnd_comm]
    exact @sub_self (Module.End ℂ GradedAlg) _ _
  · rw [liftSnd_mul, liftSnd_mul, ← liftSnd_add, annF_annF_end, liftSnd_zero]

/-! ### The `ℤ₂` grading -/

theorem parityF_end_sq : (parityF) * (parityF) = (1 : Module.End ℂ FermiAlg) := by
  refine LinearMap.ext fun u => ?_
  simpa only [Module.End.mul_apply, Module.End.one_apply] using parityF_involutive u

theorem parityF_creF_end (j : ℕ) :
    (parityF) * (creF j) = - ((creF j) * (parityF)) := by
  refine LinearMap.ext fun u => ?_
  simpa only [Module.End.mul_apply, LinearMap.neg_apply] using parityF_creF j u

theorem parityF_annF_end (j : ℕ) :
    (parityF) * (annF j) = - ((annF j) * (parityF)) := by
  refine LinearMap.ext fun u => ?_
  simpa only [Module.End.mul_apply, LinearMap.neg_apply] using parityF_annF j u

/-- **The `ℤ₂` grading operator** `(−1)^{N_f}` of the graded Fock space: it acts
as the fermion-number parity on the antisymmetric factor and trivially on the
symmetric one. -/
def gradeOp : Module.End ℂ GradedAlg := liftSnd parityF

/-- The grading operator is an involution. -/
theorem gradeOp_involutive : gradeOp * gradeOp = 1 := by
  rw [gradeOp, liftSnd_mul, parityF_end_sq, liftSnd_one]

/-- The bosonic creation operator is **even**. -/
theorem gradeOp_bcre (j : ℕ) : gradeOp * bcre j = bcre j * gradeOp := by
  rw [gradeOp, bcre, ← liftFst_liftSnd_comm]

/-- The bosonic annihilation operator is **even**. -/
theorem gradeOp_bann (j : ℕ) : gradeOp * bann j = bann j * gradeOp := by
  rw [gradeOp, bann, ← liftFst_liftSnd_comm]

/-- The fermionic creation operator is **odd**. -/
theorem gradeOp_fcre (j : ℕ) : gradeOp * fcre j = - (fcre j * gradeOp) := by
  rw [gradeOp, fcre, liftSnd_mul, liftSnd_mul, parityF_creF_end, liftSnd_neg]

/-- The fermionic annihilation operator is **odd**. -/
theorem gradeOp_fann (j : ℕ) : gradeOp * fann j = - (fann j * gradeOp) := by
  rw [gradeOp, fann, liftSnd_mul, liftSnd_mul, parityF_annF_end, liftSnd_neg]

/-- The even part of a graded state. -/
def evenPart (u : GradedAlg) : GradedAlg := (2 : ℂ)⁻¹ • (u + gradeOp u)

/-- The odd part of a graded state. -/
def oddPart (u : GradedAlg) : GradedAlg := (2 : ℂ)⁻¹ • (u - gradeOp u)

/-- **The `ℤ₂` decomposition** `Γˢ ⊗ Γᵃ = (Γˢ ⊗ Γᵃ)₊ ⊕ (Γˢ ⊗ Γᵃ)₋`. -/
theorem even_add_odd (u : GradedAlg) : evenPart u + oddPart u = u := by
  rw [evenPart, oddPart, ← smul_add]
  have h : u + gradeOp u + (u - gradeOp u) = (2 : ℂ) • u := by
    rw [two_smul]; abel
  rw [h, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

theorem gradeOp_evenPart (u : GradedAlg) : gradeOp (evenPart u) = evenPart u := by
  have hsq : gradeOp (gradeOp u) = u := by
    have := congrArg (fun T : Module.End ℂ GradedAlg => T u) gradeOp_involutive
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  rw [evenPart, map_smul, map_add, hsq, add_comm]

theorem gradeOp_oddPart (u : GradedAlg) : gradeOp (oddPart u) = - oddPart u := by
  have hsq : gradeOp (gradeOp u) = u := by
    have := congrArg (fun T : Module.End ℂ GradedAlg => T u) gradeOp_involutive
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  rw [oddPart, map_smul, map_sub, hsq, ← smul_neg]
  congr 1
  abel

end

end BookProof.GradedFock


