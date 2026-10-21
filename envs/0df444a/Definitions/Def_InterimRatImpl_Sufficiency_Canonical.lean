-- Prove2me | Definitions.Def_InterimRatImpl_Sufficiency_Canonical
-- name    : InterimRatImpl_Sufficiency_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:27.276457+00:00
-- url     : https://prove2.me/theorems/30842344-7291-4e4c-ae51-6cabd2d80a5a
-- title:
--   Proof of Theorem 6.3 — canonical message spaces and outcome rules
-- statement:
--   Fix a social choice function $\hat f$, a countable dense set $\Delta^*(A)$ of lotteries, a designated type $t_i^*$ for each agent, a full-support baseline lottery $\bar\alpha$, and a full-support mixture $y_i^{t_i,\hat f}$ of the challenge functions in $Y_i^*[t_i,\hat f]$.
--
--   Agent $i$ sends a complete type report, a positive integer $m_i^2$, one challenge function for every type, and a pure outcome. Rule 1 applies when every integer is one. Rule 2 applies when exactly one agent's integer exceeds one; it mixes that agent's challenge with the full-support mixture using weights $m_i^2/(m_i^2+1)$ and $1/(m_i^2+1)$. Rule 3 uses the announced pure outcomes with weights $m_j^2/((1+m_j^2)|I|)$ and assigns the remaining probability to $\bar\alpha$.
--
--   This is the countable mechanism used in the sufficiency proof. The file also defines the deception of Step 2 and the truthful message correspondence of Step 3.
--
--   **Formalization Note** The finite outcome lottery is represented as a standard simplex. The paper's geometric-series notation for full-support mixtures need not normalize on finite enumerations, so the definition takes normalized full-support mixtures as parameters.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), pp. 18–20 (PDF 19–21), $Y_i^*$ and Rules 1–3 in the proof of Theorem 6.3

import Definitions.Def_InterimRatImpl_Sufficiency_Model

noncomputable section

namespace InterimRatImpl.Sufficiency

universe u v w

variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- A countable dense subset of the finite-outcome simplex. -/
structure DenseLotteries (A : Type w) [Fintype A] where
  carrier : Set (A → ℝ)
  subset_simplex : carrier ⊆ stdSimplex ℝ A
  countable : carrier.Countable
  dense : stdSimplex ℝ A ⊆ closure carrier

def Ystar (Dstar : DenseLotteries A) (E : Env I T A) (i : I) (ti : T i)
    (f : SCF T A) : Set (Others T i → Lottery A) :=
  {y | (∀ s, (y s).1 ∈ Dstar.carrier ∨ ∃ t'i : T i, y s = f (join i t'i s)) ∧
       InYw E i ti f y}

/-- Strictly positive weights on every member of each countable challenge set,
whose coordinatewise barycentre is `ybar`. -/
def FullSupportYbar (Dstar : DenseLotteries A) (E : Env I T A)
    (f : SCF T A) (ybar : ∀ i, T i → Others T i → Lottery A) : Prop :=
  ∀ i ti, ∃ weight : {y // y ∈ Ystar Dstar E i ti f} → ℝ,
    (∀ y, 0 < weight y) ∧ HasSum weight 1 ∧
    (∀ s a, HasSum (fun y => weight y * (y.1 s).1 a) ((ybar i ti s).1 a))

structure CanonParams (E : Env I T A) (fhat : SCF T A) where
  Dstar : DenseLotteries A
  tstar : ∀ i, T i
  abar : Lottery A
  abar_pos : ∀ a, 0 < abar.1 a
  ybar : ∀ i, T i → Others T i → Lottery A
  ybar_full : FullSupportYbar Dstar E fhat ybar

/-- The four components of a canonical message on p. 19–20. -/
structure CanonMsg (E : Env I T A) (fhat : SCF T A)
    (Dstar : DenseLotteries A) (i : I) where
  report : Profile T
  level : ℕ+
  challenge : ∀ ti : T i, {y // y ∈ Ystar Dstar E i ti fhat}
  action : A

def selfReports {E : Env I T A} {fhat : SCF T A} {Dstar : DenseLotteries A}
    (m : Profile (CanonMsg E fhat Dstar)) : Profile T := fun j => (m j).report j

def otherSelfReports {E : Env I T A} {fhat : SCF T A} {Dstar : DenseLotteries A}
    (i : I) (m : Profile (CanonMsg E fhat Dstar)) : Others T i :=
  others i (selfReports m)

/-- A finite-outcome point mass. -/
def diracLottery (a : A) : Lottery A :=
  ⟨Pi.single a 1, single_mem_stdSimplex ℝ a⟩

/-- Convex mixture of two lotteries, with the first receiving weight `r`. -/
def mixLottery (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (p q : Lottery A) : Lottery A :=
  ⟨fun a => r * p.1 a + (1 - r) * q.1 a, by
    have h : r • p.1 + (1-r) • q.1 ∈ stdSimplex ℝ A :=
      (convex_stdSimplex ℝ A) p.2 q.2 hr.1 (sub_nonneg.mpr hr.2) (by ring)
    simpa [stdSimplex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h⟩

/-- The weight assigned to agent `j`'s named outcome by Rule 3. -/
def rule3Weight {E : Env I T A} {fhat : SCF T A} {Dstar : DenseLotteries A}
    (m : Profile (CanonMsg E fhat Dstar)) (j : I) : ℝ :=
  ((m j).level : ℝ) / ((1 + (m j).level : ℝ) * (Fintype.card I : ℝ))

/-- A finite weighted mixture, with the unused weight assigned to a base lottery. -/
def weightedLottery (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (hsum : ∑ j, weight j ≤ 1) (p : I → Lottery A) (base : Lottery A) : Lottery A :=
  ⟨fun a => (∑ j, weight j * (p j).1 a) + (1 - ∑ j, weight j) * base.1 a, by
    change (∀ a, 0 ≤ (∑ j, weight j * (p j).1 a) +
      (1 - ∑ j, weight j) * base.1 a) ∧
      (∑ a : A, ((∑ j, weight j * (p j).1 a) +
        (1 - ∑ j, weight j) * base.1 a)) = 1
    constructor
    · intro a
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg (hw j) ((p j).2.1 a)
      · exact mul_nonneg (sub_nonneg.mpr hsum) (base.2.1 a)
    · calc
        ∑ a, ((∑ j, weight j * (p j).1 a) +
          (1 - ∑ j, weight j) * base.1 a)
            = (∑ j, weight j * ∑ a, (p j).1 a) +
                (1 - ∑ j, weight j) * ∑ a, base.1 a := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                  congr 1
                  calc
                    ∑ a, ∑ j, weight j * (p j).1 a =
                        ∑ j, ∑ a, weight j * (p j).1 a := Finset.sum_comm
                    _ = ∑ j, weight j * ∑ a, (p j).1 a := by
                      simp only [Finset.mul_sum]
        _ = 1 := by
          have hp : ∀ j, ∑ a, (p j).1 a = 1 := fun j => (p j).2.2
          simp_rw [hp, base.2.2, mul_one]
          ring⟩

def rule3Lottery (E : Env I T A) (fhat : SCF T A) (P : CanonParams E fhat)
    (m : Profile (CanonMsg E fhat P.Dstar)) : Lottery A := by
  let weight : I → ℝ := rule3Weight m
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hw : ∀ j, 0 ≤ weight j := by
    intro j
    dsimp [weight, rule3Weight]
    positivity
  have hle : ∀ j, weight j ≤ 1 / (Fintype.card I : ℝ) := by
    intro j
    dsimp [weight, rule3Weight]
    have hl : (0 : ℝ) ≤ ((m j).level : ℝ) := by positivity
    have hd : (0 : ℝ) < (1 + ((m j).level : ℝ)) * (Fintype.card I : ℝ) := by
      exact mul_pos (by linarith) hn
    apply (div_le_div_iff₀ hd hn).2
    nlinarith
  have hsum : ∑ j, weight j ≤ 1 := by
    calc
      ∑ j, weight j ≤ ∑ _ : I, (1 : ℝ) / Fintype.card I :=
        Finset.sum_le_sum (fun j _ => hle j)
      _ = 1 := by simp [div_eq_mul_inv, hn.ne']
  exact weightedLottery weight hw hsum (fun j => diracLottery (m j).action) P.abar

/-- The canonical outcome function: Rules 1, 2-1, 2-2, and 3. -/
def canonG (E : Env I T A) (fhat : SCF T A) (P : CanonParams E fhat)
    (m : Profile (CanonMsg E fhat P.Dstar)) : Lottery A := by
  classical
  if h1 : ∀ i, (m i).level = 1 then
    exact fhat (selfReports m)
  else if h2 : ∃ i, 1 < (m i).level ∧ ∀ j, j ≠ i → (m j).level = 1 then
    let i := Classical.choose h2
    let ti : T i := if h : ∃ ti : T i, ∀ j, j ≠ i → (m j).report i = ti
      then Classical.choose h else P.tstar i
    let r : ℝ := ((m i).level : ℝ) / (((m i).level : ℝ) + 1)
    have hr : 0 ≤ r ∧ r ≤ 1 := by
      dsimp [r]
      constructor
      · positivity
      · apply (div_le_iff₀ (by positivity)).2
        nlinarith
    exact mixLottery r hr (((m i).challenge ti).1 (otherSelfReports i m))
      (P.ybar i ti (otherSelfReports i m))
  else
    exact rule3Lottery E fhat P m

/-- The deception extracted from rationalizable self-reports in Step 2. -/
def canonDeception (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) : Deception T where
  β i ti := {t'i | t'i = ti ∨ ∃ mi ∈ SGamma E (canonG E fhat P) i ti,
    mi.report i = t'i}
  self_mem _ _ := Or.inl rfl

/-- The truthful-level-one correspondence of Step 3. -/
def truthMessages (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) : MsgCorr T (CanonMsg E fhat P.Dstar) :=
  fun i ti => {mi | mi.report i = ti ∧ mi.level = 1}

end InterimRatImpl.Sufficiency


