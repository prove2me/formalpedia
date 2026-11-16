-- Prove2me | solution 1 for APFB07b.infinite_of_unique_minimum_changes_explicit
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:29:40.426249+00:00
-- url     : https://prove2.me/submissions/562fb885-b94e-4ee9-950d-12223d4b4ba8

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFB07b_unique_minimum_symmetry_and_variation
title: A unique cost minimum is fixed by every map that keeps admissibility and cost, so it has no side on a distinction such a map turns over; and over finitely many configurations a unique minimum cannot change as cost varies continuously
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a (A2, "Realization is the minimum-cost admissible configuration") and B07b
 (BW, the unique minimum) in their declared Lean forms APFB07a.A2Selection and APFB07b.BWUniqueMinimum.
 B07b's own header: no "result about A2 measuring or resolving ties is assumed". The archive's
 LawsOfForm.oscillation (read as a statement, not imported): a single crossing has no fixed Boolean value.
 The author, 2026-11-14 18:21 HST: "If Spencer brown shows the marks are in super position, we should be
 able to derive that a2 measures a continuum! DERIVE from first principals!!!". Codebank apf/plec.py, found
 after this file was first written (its first header said nothing was found, three other modules having
 been searched): check_Regime_R (the selector is well posed where cost is smooth, R1, and the admissible
 continuations form a connected path space, R3); check_Regime_exit_Type_II (minimizer nonuniqueness under a
 symmetric cost); check_T_trivial_alignment_is_Type_II. The symmetry theorems here are the ledger form of
 Type II; the hypotheses of the variation theorems are R1 and R3.
consumes_inputs: B07a and B07b, in the two wrapper theorems, as hypotheses in their declared Lean forms. The
 formal fidelity of A2 is NOT CERTIFIED (FOUNDATION_INPUTS), so these carry that caveat. The other theorems
 are ordinary mathematics on IsMinimum.
named_hypotheses: for the symmetry theorems, a map sigma of configurations that keeps admissibility (hadm)
 and cost (hcost); for the turn-over corollaries, a two-valued reading d of configurations that sigma turns
 over (hflip). For the variation theorems, a family of interfaces indexed by a connected space, ONE
 admissible set for the whole family, and cost continuous along the family (hcont). None of these is a
 declared input: the declared B07b speaks of each interface alone and puts no topology on interfaces.
statement: (unique_minimum_fixed_by_symmetry) a map that keeps admissibility and cost fixes the unique
 minimum. (no_unique_minimum_of_moving_symmetry) so if such a map moves every admissible configuration,
 there is no unique minimum. (unique_minimum_has_no_side) if such a map turns over a two-valued reading d,
 the hypotheses are contradictory: no unique minimum exists among configurations that all have a side on d.
 (B07b_excludes_turnover_symmetry) the same with B07b in its declared form at one interface.
 (unique_minimum_locally_constant, unique_minimum_constant_of_finite) over finitely many configurations,
 with cost continuous along a connected family and a unique minimum at every member, the minimum is the
 same configuration at every member. (infinite_of_unique_minimum_changes) so if it differs at two members,
 the configurations are infinitely many. (B07_realized_constant_of_finite) the same with B07a and B07b in
 their declared forms.
not_claimed: that any admitted move keeps the cost of configurations; that interfaces form a connected
 family; that cost varies continuously; that the configurations A2 ranges over are states. Infinitely many
 is not a continuum: the sharper classical statement (a closed set in a Euclidean space has a unique nearest
 point to every point exactly when it is convex) is not typed. No lane. No claim that the transfer is
 forced, that the carrier gap is closed or narrowed, or that Born is derived.
-/
import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
namespace APFB07b

section symmetry
variable {Configuration : Type*}

/-- A map of configurations that keeps admissibility and cost fixes the unique minimum. -/
theorem unique_minimum_fixed_by_symmetry (adm : Configuration → Prop) (cost : Configuration → ℝ)
    (sigma : Configuration → Configuration)
    (hadm : ∀ G, adm G → adm (sigma G)) (hcost : ∀ G, cost (sigma G) = cost G)
    (G : Configuration) (hmin : IsMinimum adm cost G)
    (huniq : ∀ H, IsMinimum adm cost H → H = G) : sigma G = G :=
  huniq (sigma G) ⟨hadm G hmin.1, fun H hH => by rw [hcost G]; exact hmin.2 H hH⟩

/-- If a map that keeps admissibility and cost moves every admissible configuration, there is no
unique minimum. -/
theorem no_unique_minimum_of_moving_symmetry (adm : Configuration → Prop)
    (cost : Configuration → ℝ) (sigma : Configuration → Configuration)
    (hadm : ∀ G, adm G → adm (sigma G)) (hcost : ∀ G, cost (sigma G) = cost G)
    (hmove : ∀ G, adm G → sigma G ≠ G) :
    ¬ ∃ G, IsMinimum adm cost G ∧ ∀ H, IsMinimum adm cost H → H = G := by
  rintro ⟨G, hmin, huniq⟩
  exact hmove G hmin.1
    (unique_minimum_fixed_by_symmetry adm cost sigma hadm hcost G hmin huniq)

/-- If a map that keeps admissibility and cost turns over a two-valued reading `d`, no unique
minimum exists: every configuration has a side on `d`, and the unique minimum would have none. -/
theorem unique_minimum_has_no_side (adm : Configuration → Prop) (cost : Configuration → ℝ)
    (sigma : Configuration → Configuration)
    (hadm : ∀ G, adm G → adm (sigma G)) (hcost : ∀ G, cost (sigma G) = cost G)
    (d : Configuration → Bool) (hflip : ∀ G, d (sigma G) = !d G) :
    ¬ ∃ G, IsMinimum adm cost G ∧ ∀ H, IsMinimum adm cost H → H = G := by
  refine no_unique_minimum_of_moving_symmetry adm cost sigma hadm hcost (fun G _ hfix => ?_)
  have h := hflip G
  rw [hfix] at h
  cases hd : d G <;> rw [hd] at h <;> exact absurd h (by decide)

/-- B07b in its declared form, at one interface: it excludes a map that keeps admissibility and
cost and turns over a two-valued reading of the configurations. -/
theorem B07b_excludes_turnover_symmetry {Interface : Type*} {Config : Interface → Type*}
    (originalAdmissible : (i : Interface) → Config i → Prop)
    (totalCost : (i : Interface) → Config i → ℝ)
    (hB : BWUniqueMinimum originalAdmissible totalCost) (i : Interface)
    (sigma : Config i → Config i)
    (hadm : ∀ G, originalAdmissible i G → originalAdmissible i (sigma G))
    (hcost : ∀ G, totalCost i (sigma G) = totalCost i G)
    (d : Config i → Bool) (hflip : ∀ G, d (sigma G) = !d G) : False :=
  unique_minimum_has_no_side (originalAdmissible i) (totalCost i) sigma hadm hcost d hflip (hB i)

end symmetry

section variation
variable {Lam Configuration : Type*} [TopologicalSpace Lam]

/-- Over finitely many configurations, with cost continuous along the family and a unique minimum
at every member, the minimum does not change near any member. -/
theorem unique_minimum_locally_constant [Finite Configuration] (adm : Configuration → Prop)
    (cost : Lam → Configuration → ℝ) (hcont : ∀ G, Continuous (fun t => cost t G))
    (realized : Lam → Configuration)
    (hmin : ∀ t, IsMinimum adm (cost t) (realized t))
    (huniq : ∀ t H, IsMinimum adm (cost t) H → H = realized t) (t : Lam) :
    ∃ U : Set Lam, IsOpen U ∧ t ∈ U ∧ ∀ s ∈ U, realized s = realized t := by
  classical
  refine ⟨⋂ H : Configuration,
    {s | (adm H ∧ H ≠ realized t) → cost s (realized t) < cost s H}, ?_, ?_, ?_⟩
  · refine isOpen_iInter_of_finite (fun H => ?_)
    by_cases hH : adm H ∧ H ≠ realized t
    · have hset : {s | (adm H ∧ H ≠ realized t) → cost s (realized t) < cost s H} =
          {s | cost s (realized t) < cost s H} := by
        ext s
        exact ⟨fun h => h hH, fun h _ => h⟩
      rw [hset]
      exact isOpen_lt (hcont (realized t)) (hcont H)
    · have hset : {s | (adm H ∧ H ≠ realized t) → cost s (realized t) < cost s H} =
          Set.univ := by
        ext s
        exact ⟨fun _ => Set.mem_univ s, fun _ h => absurd h hH⟩
      rw [hset]
      exact isOpen_univ
  · refine Set.mem_iInter.mpr (fun H hH => ?_)
    refine lt_of_le_of_ne ((hmin t).2 H hH.1) (fun heq => hH.2 ?_)
    exact huniq t H ⟨hH.1, fun K hK => by rw [← heq]; exact (hmin t).2 K hK⟩
  · intro s hs
    have hs' := Set.mem_iInter.mp hs
    have hm : IsMinimum adm (cost s) (realized t) :=
      ⟨(hmin t).1, fun H hH => by
        by_cases he : H = realized t
        · rw [he]
        · exact (hs' H ⟨hH, he⟩).le⟩
    exact (huniq s (realized t) hm).symm

/-- Over finitely many configurations, with cost continuous along a connected family and a unique
minimum at every member, the minimum is the same configuration at every member. -/
theorem unique_minimum_constant_of_finite [PreconnectedSpace Lam] [Finite Configuration]
    (adm : Configuration → Prop)
    (cost : Lam → Configuration → ℝ) (hcont : ∀ G, Continuous (fun t => cost t G))
    (realized : Lam → Configuration)
    (hmin : ∀ t, IsMinimum adm (cost t) (realized t))
    (huniq : ∀ t H, IsMinimum adm (cost t) H → H = realized t) (s t : Lam) :
    realized s = realized t := by
  have hloc := unique_minimum_locally_constant adm cost hcont realized hmin huniq
  have hopen : IsOpen {u : Lam | realized u = realized t} := by
    refine isOpen_iff_forall_mem_open.mpr (fun u hu => ?_)
    obtain ⟨U, hU, huU, hconst⟩ := hloc u
    exact ⟨U, fun v hv => (hconst v hv).trans hu, hU, huU⟩
  have hclosed : IsClosed {u : Lam | realized u = realized t} := by
    refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr (fun u hu => ?_))
    obtain ⟨U, hU, huU, hconst⟩ := hloc u
    exact ⟨U, fun v hv hv' => hu ((hconst v hv).symm.trans hv'), hU, huU⟩
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with hempty | huniv
  · have ht : t ∈ {u : Lam | realized u = realized t} := rfl
    rw [hempty] at ht
    exact absurd ht (Set.notMem_empty t)
  · have hs : s ∈ {u : Lam | realized u = realized t} := by rw [huniv]; exact Set.mem_univ s
    exact hs

/-- So if the unique minimum differs at two members of a connected family along which cost is
continuous, the configurations are infinitely many. -/
theorem infinite_of_unique_minimum_changes [PreconnectedSpace Lam] (adm : Configuration → Prop)
    (cost : Lam → Configuration → ℝ) (hcont : ∀ G, Continuous (fun t => cost t G))
    (realized : Lam → Configuration)
    (hmin : ∀ t, IsMinimum adm (cost t) (realized t))
    (huniq : ∀ t H, IsMinimum adm (cost t) H → H = realized t)
    (s t : Lam) (hne : realized s ≠ realized t) : Infinite Configuration := by
  by_contra hfin
  have : Finite Configuration := not_infinite_iff_finite.mp hfin
  exact hne (unique_minimum_constant_of_finite adm cost hcont realized hmin huniq s t)

/-- The same with B07a and B07b in their declared forms: along a connected family of interfaces
with one admissible set, finitely many configurations and continuous cost, the realized
configuration is the same at every interface. -/
theorem B07_realized_constant_of_finite [PreconnectedSpace Lam] [Finite Configuration]
    (adm : Configuration → Prop)
    (cost : Lam → Configuration → ℝ) (hcont : ∀ G, Continuous (fun t => cost t G))
    (realized : Lam → Configuration)
    (hA2 : APFB07a.A2Selection (Interface := Lam) (Configuration := fun _ => Configuration)
      (fun _ => adm) cost realized)
    (hB : BWUniqueMinimum (Interface := Lam) (Configuration := fun _ => Configuration)
      (fun _ => adm) cost) (s t : Lam) : realized s = realized t := by
  have hmin : ∀ u, IsMinimum adm (cost u) (realized u) := fun u => hA2 u
  have huniq : ∀ u H, IsMinimum adm (cost u) H → H = realized u := by
    intro u H hH
    obtain ⟨G, _, hu⟩ := hB u
    exact (hu H hH).trans (hu (realized u) (hmin u)).symm
  exact unique_minimum_constant_of_finite adm cost hcont realized hmin huniq s t

end variation

end APFB07b

#print axioms APFB07b.unique_minimum_fixed_by_symmetry
#print axioms APFB07b.no_unique_minimum_of_moving_symmetry
#print axioms APFB07b.unique_minimum_has_no_side
#print axioms APFB07b.B07b_excludes_turnover_symmetry
#print axioms APFB07b.unique_minimum_locally_constant
#print axioms APFB07b.unique_minimum_constant_of_finite
#print axioms APFB07b.infinite_of_unique_minimum_changes
#print axioms APFB07b.B07_realized_constant_of_finite


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Lam : Type apfNative_u_1} {Configuration : Type apfNative_u_2} [inst : TopologicalSpace.{apfNative_u_1} Lam]
  [@PreconnectedSpace.{apfNative_u_1} Lam inst] (adm : Configuration → Prop) (cost : Lam → Configuration → Real)
  (hcont :
    ∀ (G : Configuration),
      @Continuous.{apfNative_u_1, 0} Lam Real inst
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        fun (t : Lam) => cost t G)
  (realized : Lam → Configuration)
  (hmin : ∀ (t : Lam), @APFB07b.IsMinimum.{apfNative_u_2} Configuration adm (cost t) (realized t))
  (huniq :
    ∀ (t : Lam) (H : Configuration),
      @APFB07b.IsMinimum.{apfNative_u_2} Configuration adm (cost t) H →
        @Eq.{apfNative_u_2 + 1} Configuration H (realized t))
  (s t : Lam) (hne : @Ne.{apfNative_u_2 + 1} Configuration (realized s) (realized t)),
  Infinite.{apfNative_u_2 + 1} Configuration := by
  exact @APFB07b.infinite_of_unique_minimum_changes
