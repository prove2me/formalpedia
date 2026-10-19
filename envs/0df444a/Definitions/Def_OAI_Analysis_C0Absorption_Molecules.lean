-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Molecules
-- name    : OAI_Analysis_C0Absorption_Molecules
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:51:02.820785+00:00
-- url     : https://prove2.me/theorems/49bcc8b0-6759-4cc5-88a2-d13be0a52f92
-- title:
--   Molecules, admissible test lists and square-sum seminorms
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes.
--
--   1. **Molecules.** For a set $S$, $\mathrm{Mol}(S)$ is the space of finitely supported $m:S\to\mathbb R$ with $\sum_sm(s)=0$. A function $f$ pairs with $m$ by $\langle f,m\rangle=\sum_sm(s)f(s)$, so that $\langle f,\delta_s-\delta_t\rangle=f(s)-f(t)$, and every molecule is a combination of the basic molecules $\delta_s-\delta_o$.
--   2. **Admissible lists.** For a class $L$ of functions on a metric space and $C\ge0$, an admissible list is a finite list $f_1,\dots,f_k\in L$ such that every signed sum $\sum_i\varepsilon_if_i$ with $|\varepsilon_i|=1$ is $C$-Lipschitz.
--   3. **List seminorms.**
--   $$
--   \sigma_{L,C,p}(m)=\sup_{\text{admissible lists}}\Bigl(\sum_i|\langle f_i,m\rangle|^p\Bigr)^{1/p},
--   $$
--   which satisfies $\sigma(\delta_s-\delta_t)\le C\,d(s,t)$.
--   4. **Square sums.** For seminorms $q_n$ with $\sum_nq_n(x)^2<\infty$, the square seminorm is $\bigl(\sum_nq_n(x)^2\bigr)^{1/2}$, the $\ell^2$ norm of the vector $(q_n(x))_n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Molecules.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Molecules.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Molecules

variable (S : Type*)

def MoleculeSpace : Submodule ℝ (S →₀ ℝ) :=
  (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))).ker

abbrev Molecule := MoleculeSpace S

noncomputable def pairing (f : S → ℝ) : Molecule S →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ f).comp (MoleculeSpace S).subtype

variable {S}

noncomputable def molecule (s t : S) : Molecule S :=
  ⟨Finsupp.single s 1 - Finsupp.single t 1, by
    simp [MoleculeSpace, LinearMap.mem_ker]⟩

@[simp] theorem pairing_molecule (f : S → ℝ) (s t : S) :
    pairing S f (molecule s t) = f s - f t := by
  simp [pairing, molecule]

@[simp] theorem pairing_const (c : ℝ) (m : Molecule S) :
    pairing S (fun _ => c) m = 0 := by
  have hm := m.property
  change (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))) m.val = 0 at hm
  simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_one] at hm
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul]
  rw [← Finsupp.sum_mul, hm, zero_mul]

theorem molecule_decomposition (m : Molecule S) (o : S) :
    m = ∑ s ∈ m.val.support, m.val s • molecule s o := by
  classical
  have hm := m.property
  change (Finsupp.linearCombination ℝ (fun _ : S => (1 : ℝ))) m.val = 0 at hm
  simp only [Finsupp.linearCombination_apply, smul_eq_mul, mul_one,
    Finsupp.sum] at hm
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, molecule, smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hm, zero_smul, sub_zero]
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using (Finsupp.sum_single m.val).symm

@[simp] theorem molecule_self (s : S) : molecule s s = 0 := by
  apply Subtype.ext
  simp [molecule]

theorem molecule_sub_molecule (s t o : S) : molecule s o - molecule t o = molecule s t := by
  apply Subtype.ext
  change (Finsupp.single s 1 - Finsupp.single o 1) -
    (Finsupp.single t 1 - Finsupp.single o 1) = Finsupp.single s 1 - Finsupp.single t 1
  abel

end Molecules

section TestLists

variable {S : Type*} [MetricSpace S]

structure AdmissibleList (L : Set (S → ℝ)) (C : ℝ≥0) where
  length : ℕ
  test : Fin length → S → ℝ
  mem : ∀ i, test i ∈ L
  signed_lipschitz : ∀ ε : Fin length → ℝ, (∀ i, |ε i| = 1) →
    LipschitzWith C (fun s => ∑ i, ε i * test i s)

def AdmissibleList.empty (L : Set (S → ℝ)) (C : ℝ≥0) : AdmissibleList L C where
  length := 0
  test := Fin.elim0
  mem i := Fin.elim0 i
  signed_lipschitz ε hε := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Fin.sum_univ_zero, dist_self]
    positivity

instance (L : Set (S → ℝ)) (C : ℝ≥0) : Nonempty (AdmissibleList L C) :=
  ⟨AdmissibleList.empty L C⟩

theorem AdmissibleList.sum_abs_sub_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (s t : S) :
    ∑ i, |l.test i s - l.test i t| ≤ C * dist s t := by
  classical
  let ε : Fin l.length → ℝ := fun i => if 0 ≤ l.test i s - l.test i t then 1 else -1
  have hε : ∀ i, |ε i| = 1 := by
    intro i
    dsimp [ε]
    split <;> norm_num
  have heq : ∀ i, ε i * (l.test i s - l.test i t) =
      |l.test i s - l.test i t| := by
    intro i
    dsimp [ε]
    split
    · simp [abs_of_nonneg, *]
    · simp [abs_of_neg (lt_of_not_ge ‹¬ 0 ≤ l.test i s - l.test i t›)]
  have h := (l.signed_lipschitz ε hε).dist_le_mul s t
  rw [Real.dist_eq, ← Finset.sum_sub_distrib] at h
  simp_rw [← mul_sub, heq] at h
  rwa [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h

theorem finite_lp_norm_le_sum {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : PiLp p (fun _ : ι => ℝ)) : ‖f‖ ≤ ∑ i, |f i| := by
  classical
  have heq : f = ∑ i, PiLp.single p (β := fun _ : ι => ℝ) i (f i) := by
    apply PiLp.ext
    intro j
    simp [← WithLp.toLp_sum, PiLp.single, Function.update, Pi.single]
  calc
    ‖f‖ = ‖∑ i, PiLp.single p (β := fun _ : ι => ℝ) i (f i)‖ := congrArg norm heq
    _ ≤ ∑ i, ‖PiLp.single p (β := fun _ : ι => ℝ) i (f i)‖ := norm_sum_le _ _
    _ = ∑ i, |f i| := by simp [PiLp.norm_single, Real.norm_eq_abs]

def AdmissibleList.eval {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) :
    Molecule S →ₗ[ℝ] PiLp p (fun _ : Fin l.length => ℝ) :=
  (WithLp.linearEquiv p ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => pairing S (l.test i))

@[simp] theorem AdmissibleList.eval_apply {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) (m : Molecule S) (i : Fin l.length) :
    (l.eval p m) i = pairing S (l.test i) m := rfl

def AdmissibleList.seminorm {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Seminorm ℝ (Molecule S) :=
  (normSeminorm ℝ (PiLp p (fun _ : Fin l.length => ℝ))).comp (l.eval p)

@[simp] theorem AdmissibleList.seminorm_apply {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : Molecule S) :
    l.seminorm p m = ‖l.eval p m‖ := rfl

theorem AdmissibleList.seminorm_molecule_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (s t : S) :
    l.seminorm p (molecule s t) ≤ C * dist s t := by
  calc
    l.seminorm p (molecule s t) ≤ ∑ i, |(l.eval p (molecule s t)) i| :=
      finite_lp_norm_le_sum p _
    _ = ∑ i, |l.test i s - l.test i t| := by simp
    _ ≤ C * dist s t := l.sum_abs_sub_le s t

theorem AdmissibleList.seminorm_le {L : Set (S → ℝ)} {C : ℝ≥0}
    (l : AdmissibleList L C) (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    l.seminorm p m ≤ C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  classical
  conv_lhs => rw [molecule_decomposition m o]
  simp only [AdmissibleList.seminorm_apply, map_sum, map_smul]
  calc
    ‖∑ s ∈ m.val.support, m.val s • l.eval p (molecule s o)‖
        ≤ ∑ s ∈ m.val.support, |m.val s| * ‖l.eval p (molecule s o)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        norm_sum_le m.val.support (fun s => m.val s • l.eval p (molecule s o))
    _ ≤ ∑ s ∈ m.val.support, |m.val s| * (C * dist s o) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (l.seminorm_molecule_le p s o) (abs_nonneg _)
    _ = C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

def sigma (L : Set (S → ℝ)) (C : ℝ≥0) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Seminorm ℝ (Molecule S) :=
  ⨆ l : AdmissibleList L C, l.seminorm p

theorem list_seminorms_bddAbove (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) :
    BddAbove (Set.range fun l : AdmissibleList L C => l.seminorm p) := by
  rw [Seminorm.bddAbove_range_iff]
  intro m
  refine ⟨C * ∑ s ∈ m.val.support, |m.val s| * dist s o, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact l.seminorm_le p o m

theorem sigma_apply (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    sigma L C p m = ⨆ l : AdmissibleList L C, ‖l.eval p m‖ := by
  exact Seminorm.iSup_apply (list_seminorms_bddAbove L C p o)

theorem sigma_molecule_le (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (s t : S) :
    sigma L C p (molecule s t) ≤ C * dist s t := by
  rw [sigma_apply L C p s]
  exact ciSup_le fun l => l.seminorm_molecule_le p s t

theorem list_le_sigma (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (l : AdmissibleList L C) :
    l.seminorm p ≤ sigma L C p :=
  le_ciSup (list_seminorms_bddAbove L C p o) l

theorem sigma_le (L : Set (S → ℝ)) (C : ℝ≥0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (o : S) (m : Molecule S) :
    sigma L C p m ≤ C * ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  rw [sigma_apply L C p o]
  exact ciSup_le fun l => l.seminorm_le p o m

end TestLists

section SquareSum

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (q : ℕ → Seminorm ℝ M)
variable (hq : ∀ x, Summable (fun n => (q n x) ^ 2))

def squareVector (x : M) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => q n x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      using hq x)⟩

@[simp] theorem squareVector_apply (x : M) (n : ℕ) :
    squareVector q hq x n = q n x := rfl

def squareSeminorm : Seminorm ℝ M :=
  Seminorm.of (fun x => ‖squareVector q hq x‖)
    (by
      intro x y
      calc
        ‖squareVector q hq (x + y)‖ ≤ ‖squareVector q hq x + squareVector q hq y‖ := by
          apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          intro n
          change ‖q n (x + y)‖ ≤ ‖q n x + q n y‖
          rw [Real.norm_of_nonneg (apply_nonneg _ _),
            Real.norm_of_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))]
          exact map_add_le_add _ _ _
        _ ≤ ‖squareVector q hq x‖ + ‖squareVector q hq y‖ := norm_add_le _ _)
    (by
      intro a x
      have h : squareVector q hq (a • x) = ‖a‖ • squareVector q hq x := by
        apply lp.ext
        funext n
        change q n (a • x) = ‖a‖ * q n x
        exact map_smul_eq_mul _ _ _
      rw [h, norm_smul, norm_norm])

@[simp] theorem squareSeminorm_apply (x : M) :
    squareSeminorm q hq x = ‖squareVector q hq x‖ := rfl

theorem squareSeminorm_sq (x : M) :
    (squareSeminorm q hq x) ^ 2 = ∑' n, (q n x) ^ 2 := by
  simpa only [squareSeminorm_apply, ENNReal.toReal_ofNat, Real.rpow_two,
    Real.norm_eq_abs, sq_abs, squareVector_apply] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (squareVector q hq x)

theorem coordinate_le_squareSeminorm (n : ℕ) (x : M) :
    q n x ≤ squareSeminorm q hq x := by
  simpa only [squareSeminorm_apply, squareVector_apply,
    Real.norm_of_nonneg (apply_nonneg _ _)] using
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (squareVector q hq x) n

theorem seminorm_abs_sub_le (r : Seminorm ℝ M) (x y : M) :
    |r x - r y| ≤ r (x - y) := by
  have hxy := map_add_le_add r (x - y) y
  have hyx := map_add_le_add r (y - x) x
  rw [sub_add_cancel] at hxy hyx
  have hn : r (y - x) = r (x - y) := by rw [← neg_sub x y, map_neg_eq_map]
  rw [hn] at hyx
  apply abs_le.mpr
  constructor <;> linarith

theorem squareVector_sub_norm_le (x y : M) :
    ‖squareVector q hq x - squareVector q hq y‖ ≤ squareSeminorm q hq (x - y) := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖q n x - q n y‖ ≤ ‖q n (x - y)‖
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (apply_nonneg _ _)]
  exact seminorm_abs_sub_le _ _ _

end SquareSum

end
end C0Absorption

end OAI


