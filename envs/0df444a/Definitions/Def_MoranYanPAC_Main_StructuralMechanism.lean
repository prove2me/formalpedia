-- Prove2me | Definitions.Def_MoranYanPAC_Main_StructuralMechanism
-- name    : MoranYanPAC_Main_StructuralMechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:45.379049+00:00
-- url     : https://prove2.me/theorems/2b56b278-e546-4f2b-8a34-d38f469b4c7c
-- title:
--   Algorithm 1 and the four structural axioms
-- statement:
--   Fix an arbitrary record type $Z$, an output universe $Y$, a nonnegative integer rank $\rho:Y\to\mathbb N$, arbitrary real scores $q_S$, and a finite nonempty candidate set $\operatorname{Out}(S)$ for each list $S$. Define $R_S$ as its largest rank minus its smallest rank and $q_S^*$ as its maximum score. For parameters $\varepsilon,\delta,\Delta,B$, Algorithm 1 has
--
--   $$\lambda=\Delta+\frac{2\Delta}{\varepsilon}\log\frac{8B}{\delta},\qquad A(S)(h)=\frac{\exp\{\frac{\varepsilon}{2\Delta}[q_S(h)+\lambda\rho(h)]\}}{\sum_{g\in\operatorname{Out}(S)}\exp\{\frac{\varepsilon}{2\Delta}[q_S(g)+\lambda\rho(g)]\}}$$
--
--   on $\operatorname{Out}(S)$, and zero elsewhere. The definition constructs the normalized PMF using a finite subtype, with a proof that its exponential-weight sum is positive and finite.
--
--   The structural-axiom predicate requires a map $F_{S,T}$ for each ordered neighboring pair. Fixed-output scores have sensitivity at most $\Delta$; common outputs are fixed and disappearing outputs strictly increase rank; each positive gap $t$ has at most $B^t$ preimages of any image; and mapped scores differ by at most $\Delta$. The gap is written $\rho(g)+t=\rho(h)$, avoiding truncated natural subtraction. There is no bound on the global rank height and no binary-loss restriction. The axioms are separate from the data and are hypotheses of Theorem 2, not certificates used to define the rule.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Section 2.2, setup, Equation (1), Algorithm 1 and Theorem 2, pp. 4–5 (PDF pp. 4–5)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_PrivateLaw

set_option autoImplicit false

open scoped ENNReal

namespace MoranYanPAC.Main

/-- The setup on pp. 4–5. The rank has no global height bound and scores are real. -/
structure StructuralData (Z Y : Type*) where
  out : List Z → Finset Y
  nonempty : ∀ S, (out S).Nonempty
  rank : Y → ℕ
  score : List Z → Y → ℝ

/-- Algorithm 1: the rank-bonus coefficient, in original score units. -/
noncomputable def rankBonus (ε δ Δ B : ℝ) : ℝ :=
  Δ + (2 * Δ / ε) * Real.log (8 * B / δ)

/-- A finite Gibbs law with its actual normalized exponential weights. -/
noncomputable def finiteGibbs {Y : Type*} (out : Finset Y) (hne : out.Nonempty)
    (f : Y → ℝ) : PMF Y := by
  classical
  let w : {h // h ∈ out} → ℝ≥0∞ := fun h => ENNReal.ofReal (Real.exp (f h))
  have hw0 : (∑' h, w h) ≠ 0 := by
    obtain ⟨h, hh⟩ := hne
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.exp_pos (f h)))
      (ENNReal.le_tsum (f := w) ⟨h, hh⟩))
  have hwt : (∑' h, w h) ≠ ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  exact (PMF.normalize w hw0 hwt).map Subtype.val

/-- Algorithm 1, p. 5. This is a genuine probability law on every input, including []. -/
noncomputable def structuralMechanism {Z Y : Type*} (M : StructuralData Z Y)
    (ε δ Δ B : ℝ) (S : List Z) : PMF Y :=
  finiteGibbs (M.out S) (M.nonempty S)
    (fun h => (ε / (2 * Δ)) * (M.score S h + rankBonus ε δ Δ B * M.rank h))

/-- Equation (1), p. 5. The finite nonempty maximum minus minimum rank. -/
noncomputable def rankRange {Z Y : Type*} (M : StructuralData Z Y) (S : List Z) : ℕ :=
  (M.out S).sup' (M.nonempty S) M.rank - (M.out S).inf' (M.nonempty S) M.rank

/-- The maximum unregularized score over the actual nonempty candidates. -/
noncomputable def bestScore {Z Y : Type*} (M : StructuralData Z Y) (S : List Z) : ℝ :=
  (M.out S).sup' (M.nonempty S) (M.score S)

/-- The four axioms of Theorem 2, p. 5. Rank gaps are encoded by addition,
so gaps exceeding the image rank never acquire spurious truncated preimages. -/
def StructuralAxioms {Z Y : Type*} (M : StructuralData Z Y) (Δ B : ℝ) : Prop :=
  ∀ S T : List Z, PrivLittlestone.IsInsDelNeighbor S T →
    (∀ h : Y, |M.score S h - M.score T h| ≤ Δ) ∧
    ∃ F : {g // g ∈ M.out S} → {h // h ∈ M.out T},
      (∀ g, (g.val ∈ M.out T → (F g).val = g.val) ∧
        (g.val ∉ M.out T → M.rank g.val < M.rank (F g).val)) ∧
      (∀ h : {h // h ∈ M.out T}, ∀ t : ℕ, 1 ≤ t →
        (({g : {g // g ∈ M.out S} | (F g).val = h.val ∧
            M.rank g.val + t = M.rank h.val}).encard : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ t)) ∧
      (∀ g, |M.score S g.val - M.score T (F g).val| ≤ Δ)

end MoranYanPAC.Main


