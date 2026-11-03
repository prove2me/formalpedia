-- Prove2me | Definitions.Def_BeliefDominance_vaccineProblem
-- name    : BeliefDominance_vaccineProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:48.334721+00:00
-- url     : https://prove2.me/theorems/7c7ee9fb-2a60-426a-bfb8-d72df4de8ebf
-- title:
--   The vaccine problem of §2: Table 1 and the number of effective vaccines
-- statement:
--   There are two virus strains $A,B$ and three vaccines $\alpha,\beta,\gamma$. A laboratory researches one vaccine in each of two months, and learns the strain after the first month. Both periods may choose any vaccine, so a strategy is a triplet $(x_1,x_{2,A},x_{2,B})$, and there are 27 of them.
--
--   Two virologists hold the beliefs of Table 1:
--
--   | | one month | two months |
--   |---|---|---|
--   | strain A | $0.9$ / $0.1$ | |
--   | against A: $\alpha$ | $0.6$ / $0.4$ | $0.85$ / $0.80$ |
--   | against A: $\beta$ | $0.2$ / $0.1$ | $0.40$ / $0.55$ |
--   | against A: $\gamma$ | $0.1$ / $0.2$ | $0.30$ / $0.80$ |
--   | against B: $\alpha$ | $0.1$ / $0$ | $0.40$ / $0.10$ |
--   | against B: $\beta$ | $0.3$ / $0.5$ | $0.80$ / $0.65$ |
--   | against B: $\gamma$ | $0.4$ / $0.2$ | $0.65$ / $0.80$ |
--
--   An outcome is $z=(s,b)$ with $s$ the strain and $b\in\{0,1\}^{12}$ recording whether each of the six research efforts is effective against each strain. The belief of virologist $i$ gives mass
--
--   $$
--   \pi_i(y)\,\mathbf 1[s=y]\prod_{e}\bigl(b(e)\,q_i(e)+(1-b(e))(1-q_i(e))\bigr)
--   $$
--
--   to the signal $y$ and the outcome $(s,b)$, where $\pi_i$ and $q_i$ are the entries of Table 1. The utility is the number of effective vaccines: for $x_1=x_2$ it is $b(s,\text{two }x_1)$, and otherwise $b(s,\text{one }x_1)+b(s,\text{one }x_2)$.
--
--   This is the paper's illustrative example, and it witnesses fallible inconsistency under belief dominance.
--
--   **Formalization Note** The utility $U(x_1,x_2,z)$ of §3 does not see the signal, whereas the count $N(x,Y,Z)$ of Appendix A does. So the strain is also recorded in $z$, and each belief puts mass $0$ on $s\ne y$. Table 1 fixes only marginals, and independence of the strain and of all 12 entries is the choice made here; the paper's text makes different vaccines independent. Every statement of the mission depends on the beliefs only through the marginals of Table 1. The module also defines the strategy notation `strat` and the conditional value `conditionalValue`.
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, §2, Table 1, p.3; Appendix A, p.11

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace BeliefDominance

/-- The two virus strains A and B (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic
Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, §2, p.3 (PDF p.4)). -/
inductive Strain
  | A
  | B
  deriving DecidableEq

/-- The three vaccines α, β, γ (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §2,
p.3 (PDF p.4)). -/
inductive Vaccine
  | α
  | β
  | γ
  deriving DecidableEq

/-- A research effort of Table 1: one or two months on a vaccine (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, Table 1, p.3 (PDF p.4)). -/
inductive Effort
  | one (v : Vaccine)
  | two (v : Vaccine)
  deriving DecidableEq

instance : Fintype Strain :=
  ⟨{.A, .B}, fun x => by cases x <;> simp⟩

instance : Fintype Vaccine :=
  ⟨{.α, .β, .γ}, fun x => by cases x <;> simp⟩

instance : Fintype Effort :=
  ⟨{.one .α, .one .β, .one .γ, .two .α, .two .β, .two .γ}, fun x => by
    rcases x with (_ | _ | _) | (_ | _ | _) <;> simp⟩

/-- The two virologists, whose beliefs are the columns of Table 1 (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, p.3 (PDF p.4)). -/
inductive Virologist
  | v1
  | v2
  deriving DecidableEq

/-- The strain probabilities: the top row of Table 1, `P(strain A) = 90% / 10%` (Ekholm–Baker,
Management Science, doi:10.1287/mnsc.2020.3908, p.3 (PDF p.4)). -/
noncomputable def strainProb : Virologist → Strain → ℝ
  | .v1, .A => 9 / 10
  | .v1, .B => 1 / 10
  | .v2, .A => 1 / 10
  | .v2, .B => 9 / 10

/-- The probability that a research effort yields a vaccine effective against a strain: the bottom
12 rows of Table 1 (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, p.3 (PDF p.4)). -/
noncomputable def effectiveProb : Virologist → Strain → Effort → ℝ
  | .v1, .A, .one .α => 60 / 100
  | .v1, .A, .one .β => 20 / 100
  | .v1, .A, .one .γ => 10 / 100
  | .v1, .A, .two .α => 85 / 100
  | .v1, .A, .two .β => 40 / 100
  | .v1, .A, .two .γ => 30 / 100
  | .v1, .B, .one .α => 10 / 100
  | .v1, .B, .one .β => 30 / 100
  | .v1, .B, .one .γ => 40 / 100
  | .v1, .B, .two .α => 40 / 100
  | .v1, .B, .two .β => 80 / 100
  | .v1, .B, .two .γ => 65 / 100
  | .v2, .A, .one .α => 40 / 100
  | .v2, .A, .one .β => 10 / 100
  | .v2, .A, .one .γ => 20 / 100
  | .v2, .A, .two .α => 80 / 100
  | .v2, .A, .two .β => 55 / 100
  | .v2, .A, .two .γ => 80 / 100
  | .v2, .B, .one .α => 0 / 100
  | .v2, .B, .one .β => 50 / 100
  | .v2, .B, .one .γ => 20 / 100
  | .v2, .B, .two .α => 10 / 100
  | .v2, .B, .two .β => 65 / 100
  | .v2, .B, .two .γ => 80 / 100

/-- The outcome `z = (s, b)` of the vaccine problem: the strain `s`, and the vector
`b ∈ {0,1}¹²` of Appendix A (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, p.11
(PDF p.12)), with `b (s, e)` saying that research effort `e` is effective against strain `s`.

**Formalization Note** The utility `U(x₁, x₂, z)` of §3 does not see the signal `y`, while the count
`N(x, Y, Z)` of Appendix A does. To keep `U` as printed, the strain is also recorded in `z`, and
every belief puts mass 0 on `s ≠ y`. -/
abbrev VaccineOutcome : Type := Strain × (Strain × Effort → Bool)

/-- The mass of a virologist's belief at signal `y` and outcome `(s, b)`:
`π(y) · 1[s = y] · ∏ₑ (b e ? q(e) : 1 − q(e))`.

**Formalization Note** Table 1 fixes only the marginals, and p.3 says that the effectiveness of
different vaccines is independent. This definition takes the strain and all 12 entries of `b`
independent under each belief. `V` depends only on the marginals of Table 1, so no statement of the
mission depends on this choice. -/
noncomputable def vaccineWeight (i : Virologist) (ω : Strain × VaccineOutcome) : ℝ :=
  strainProb i ω.1 * (if ω.2.1 = ω.1 then 1 else 0) *
    ∏ e : Strain × Effort, if ω.2.2 e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2

private lemma effectiveProb_mem (i : Virologist) (e : Strain × Effort) :
    0 ≤ effectiveProb i e.1 e.2 ∧ effectiveProb i e.1 e.2 ≤ 1 := by
  obtain ⟨s, t⟩ := e
  rcases i with _ | _ <;> rcases s with _ | _ <;> rcases t with (_ | _ | _) | (_ | _ | _) <;>
    norm_num [effectiveProb]

private lemma strainProb_nonneg (i : Virologist) (s : Strain) : 0 ≤ strainProb i s := by
  rcases i with _ | _ <;> rcases s with _ | _ <;> norm_num [strainProb]

private lemma vaccineWeight_nonneg (i : Virologist) (ω : Strain × VaccineOutcome) :
    0 ≤ vaccineWeight i ω := by
  refine mul_nonneg (mul_nonneg (strainProb_nonneg i _) (by split_ifs <;> norm_num)) ?_
  refine Finset.prod_nonneg fun e _ => ?_
  have h := effectiveProb_mem i e
  split_ifs
  · exact h.1
  · linarith [h.2]

private lemma sum_prod_effective (i : Virologist) :
    ∑ b : Strain × Effort → Bool, ∏ e : Strain × Effort,
      (if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Strain × Effort => (Finset.univ : Finset Bool))
    (fun e c => if c then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

private lemma sum_vaccineWeight (i : Virologist) :
    ∑ ω : Strain × VaccineOutcome, vaccineWeight i ω = 1 := by
  have key : ∀ y s : Strain, ∑ b : Strain × Effort → Bool, vaccineWeight i (y, s, b) =
      strainProb i y * if s = y then 1 else 0 := by
    intro y s
    simp only [vaccineWeight]
    exact (Finset.mul_sum _ _ _).symm.trans (by rw [sum_prod_effective i, mul_one])
  have hU : ∀ g : Strain → ℝ, ∑ s, g s = g .A + g .B := fun g => by
    rw [show (Finset.univ : Finset Strain) = {Strain.A, Strain.B} from rfl,
      Finset.sum_pair (by decide)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, key, hU]
  have hBA : Strain.B ≠ Strain.A := by decide
  rcases i with _ | _ <;> norm_num [strainProb, hBA, hBA.symm]

/-- The belief of virologist `i` on `Strain × VaccineOutcome` (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, Table 1, p.3, and Appendix A, p.11). -/
noncomputable def belief (i : Virologist) : PMF (Strain × VaccineOutcome) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (vaccineWeight i ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => vaccineWeight_nonneg i ω, sum_vaccineWeight]
    simp)

/-- The number `N` of effective vaccines (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, Appendix A, p.11 (PDF p.12)), read from the outcome `(s, b)`: if
`x₁ = x₂` it counts the two-month effort on `x₁`, otherwise the one-month efforts on `x₁` and on
`x₂`, against the strain `s`. -/
noncomputable def vaccineUtility (x₁ x₂ : Vaccine) (z : VaccineOutcome) : ℝ :=
  if x₁ = x₂ then (if z.2 (z.1, .two x₁) then 1 else 0)
  else (if z.2 (z.1, .one x₁) then 1 else 0) + (if z.2 (z.1, .one x₂) then 1 else 0)

/-- The vaccine problem of §2 (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, pp.3–4
and Appendix A, p.11): both periods choose any of the three vaccines, the signal is the strain, and
`Φ` holds the beliefs of the two virologists. -/
noncomputable def vaccineProblem : Problem Vaccine Vaccine Strain VaccineOutcome where
  space := { X₁ := Set.univ, X₂ := fun _ _ => Set.univ }
  U := vaccineUtility
  Φ := {belief .v1, belief .v2}

/-- The strategy written `(x₁, x₂,A, x₂,B)` in the paper (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §2, p.3 (PDF p.4)). -/
def strat (x₁ xA xB : Vaccine) : Vaccine × (Strain → Vaccine) :=
  (x₁, fun s => match s with
    | .A => xA
    | .B => xB)

/-- The expected number of effective vaccines given strain `s` when `x₁` and `x₂` are researched
(Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, Appendix A, p.11 (PDF p.12)):
the two-month probability if `x₁ = x₂`, and the sum of the two one-month probabilities otherwise. -/
noncomputable def conditionalValue (i : Virologist) (s : Strain) (x₁ x₂ : Vaccine) : ℝ :=
  if x₁ = x₂ then effectiveProb i s (.two x₁)
  else effectiveProb i s (.one x₁) + effectiveProb i s (.one x₂)

end BeliefDominance


