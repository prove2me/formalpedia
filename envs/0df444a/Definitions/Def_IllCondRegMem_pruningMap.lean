-- Prove2me | Definitions.Def_IllCondRegMem_pruningMap
-- name    : IllCondRegMem_pruningMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:56.659076+00:00
-- url     : https://prove2.me/theorems/141357e1-7ce1-46a7-8943-a7eabb356c96
-- title:
--   The pruning map $\Psi(\cdot;D,G)$ of §5.1
-- statement:
--   Fix a subspace $G$, a distribution $D$ over $\mathrm{Gr}(d_E,G^\perp)$, a failure probability $p_f$ and pruning parameters $(d_0,\delta_{\max})$. The **pruning procedure** run on a subspace $E$ is:
--
--   1. set $R_0=\mathrm{Gr}(d_E,G^\perp)$;
--   2. at step $j\ge0$: if $D(R_j)<p_f$, output FAIL; otherwise, if the conditional law $D_j=D(\cdot\mid R_j)$ is $(d_0,\delta_{\max})$-pruned on $G^\perp$, output PRUNED; otherwise select a witness pair $(w_j,\delta_j)\in(S^{d-1}\cap G^\perp)\times(0,\delta_{\max}]$ with $D_j\{\|P_{E'}w_j\|<\delta_j\}>\delta_j^{d_0}$, with $\delta_j$ within a factor $1/2$ of the supremum of such witness margins;
--   3. if $\|P_Ew_j\|<\delta_j$, output $(w_j,\delta_j)$; otherwise set $R_{j+1}=R_j\cap\{E':\|P_{E'}w_j\|\ge\delta_j\}$ and continue;
--   4. after infinitely many rejections, output PRUNED.
--
--   The map $E\mapsto\Psi(E;D,G)\in\{\mathrm{FAIL},\mathrm{PRUNED}\}\cup(S^{d-1}\cap G^\perp)\times(0,\delta_{\max}]$ either certifies that the remaining distribution is pruned or exhibits a direction nearly orthogonal to $E$. The masked adversary uses it to grow the explored subspace.
--
--   **Formalization Note** $D$ is the law of a random subspace $E$ on $(\Omega,\mathbb P)$ and $D(\cdot\mid R)$ is `ProbabilityTheory.cond`. The witness selection is an arbitrary **rule** mapping each region to a pair; it is admissible (`IsSelectionRule`) when, on every region reached with $D(R)\ge p_f$ and non-pruned conditional law, it returns a witness whose margin is at least half of every witness margin. The map returns the witness of the first accepting step before the procedure stops, else FAIL/PRUNED according to the stop (FAIL tested first), else PRUNED. $R_0$ is the set of all subspaces, which has the same $D$-mass as $\mathrm{Gr}(d_E,G^\perp)$.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §5.1 "Pruning procedure construction", p.20 (PDF p.21)

import Mathlib
import Definitions.Def_IllCondRegMem_IsPrunedOn

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- The outputs of the pruning map: `FAIL`, `PRUNED`, or a vector/margin pair `(w, δ)`. -/
inductive PruneOut (d : ℕ)
  | fail : PruneOut d
  | pruned : PruneOut d
  | witness (w : Vec d) (δ : ℝ) : PruneOut d

/-- `(w, δ)` **witnesses that the law of `E` under `Q` is not `(d₀, δ_max)`-pruned on `G⊥`**
(Definition 4, p.8, negated): `w ∈ S^{d−1} ∩ G⊥`, `δ ∈ (0, δ_max]` and
`Q{‖P_E w‖ < δ} > δ^{d₀}`. -/
def IsPruneWitness {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (Q : Measure Ω)
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (d₀ : ℕ) (δmax : ℝ)
    (w : Vec d) (δ : ℝ) : Prop :=
  ‖w‖ = 1 ∧ w ∈ Gᗮ ∧ 0 < δ ∧ δ ≤ δmax ∧
    ENNReal.ofReal (δ ^ d₀) < Q {ω | ‖(E ω).starProjection w‖ < δ}

/-- **Admissible witness selection rule** of the pruning procedure (§5.1, p.20): whenever the
procedure reaches a region `R` (a set of subspaces) with `D(R) ≥ p_f` whose conditional law
`D(· | R)` is not `(d₀, δ_max)`-pruned on `G⊥`, the rule returns a witness pair `(w, δ)` for
`D(· | R)` with `δ` "within a factor 1/2 of the supremum of such witness margins", i.e. every
witness margin is at most `2δ`.

**Formalization Note.** The rule is a function of the region; any deterministic choice of
witness satisfying these two properties is allowed (the lemmas about the pruning map hold for
every admissible rule). `D` is the law of the random subspace `E` under `P`, and `D(· | R)` is
`ProbabilityTheory.cond P (E ⁻¹' R)`. -/
def IsSelectionRule {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (pf : ℝ) (d₀ : ℕ) (δmax : ℝ)
    (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ) : Prop :=
  ∀ R : Set (Submodule ℝ (Vec d)), ENNReal.ofReal pf ≤ P (E ⁻¹' R) →
    ¬ IsPrunedOn (cond P (E ⁻¹' R)) E G d₀ δmax →
      IsPruneWitness (cond P (E ⁻¹' R)) E G d₀ δmax (rule R).1 (rule R).2 ∧
      ∀ w δ, IsPruneWitness (cond P (E ⁻¹' R)) E G d₀ δmax w δ → δ ≤ 2 * (rule R).2

/-- The regions `R_j` of the pruning procedure: `R₀` is the whole space and
`R_{j+1} = R_j ∩ {E′ : ‖P_{E′} w_j‖ ≥ δ_j}` with `(w_j, δ_j) = rule(R_j)`. -/
noncomputable def pruneRegion {d : ℕ} (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ) :
    ℕ → Set (Submodule ℝ (Vec d))
  | 0 => Set.univ
  | j + 1 => pruneRegion rule j ∩
      {E' | (rule (pruneRegion rule j)).2 ≤ ‖E'.starProjection (rule (pruneRegion rule j)).1‖}

/-- The procedure stops at step `j` when `D(R_j) < p_f` (FAIL) or `D(· | R_j)` is
`(d₀, δ_max)`-pruned on `G⊥` (PRUNED). -/
def pruneStops {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (pf : ℝ) (d₀ : ℕ) (δmax : ℝ)
    (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ) (j : ℕ) : Prop :=
  P (E ⁻¹' pruneRegion rule j) < ENNReal.ofReal pf ∨
    IsPrunedOn (cond P (E ⁻¹' pruneRegion rule j)) E G d₀ δmax

/-- **Pruning map** `Ψ(·; D, G)` (§5.1, p.20).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §5.1
"Pruning procedure construction", p.20: "The procedure first initializes R₀ := Gr(d_E, G⊥) as the
entire space. On step j ≥ 0, if D(R_j) < p_f the procedure terminates and outputs FAIL.
Otherwise we define D_j = D(· | R_j) … and check whether D_j is (d₀, δ_max)-pruned on G⊥. If so,
the procedure returns PRUNED and terminates. If the conditional distribution is not pruned …
[it] deterministically selects such a witness pair (w_j, δ_j), taking δ_j within a factor 1/2 of
the supremum of such witness margins. To decide the next iteration, we now consult E: if
‖P_E w_j‖ < δ_j, we return (w_j, δ_j). Otherwise, we reject it and refine the region
R_{j+1} = R_j ∩ {E′ : ‖P_{E′} w_j‖ ≥ δ_j}. In the final case when there are infinitely many
rejections, the procedure successfully returns PRUNED."

`pruningMap P E G pf d₀ δmax rule E'` runs the procedure on the subspace `E'`, where `D` is the
law of the random subspace `E` under `P` and `rule` selects the witnesses.

**Formalization Note.** With `J` the first stopping step (if any): if `E'` accepts a witness at
some step `j < J` (resp. some step `j`, when the procedure never stops), the output is the
witness of the first such step; otherwise the output is FAIL or PRUNED according to the stop at
`J` (FAIL is tested first, as in the procedure), and PRUNED if there is no stop. `R₀` is the set
of all subspaces, which has the same `D`-mass as `Gr(d_E, G⊥)` when `D` is supported there. -/
noncomputable def pruningMap {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (pf : ℝ) (d₀ : ℕ) (δmax : ℝ)
    (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ) (E' : Submodule ℝ (Vec d)) : PruneOut d := by
  classical
  exact
    if hJ : ∃ j, pruneStops P E G pf d₀ δmax rule j then
      if hA : ∃ j, j < Nat.find hJ ∧
          ‖E'.starProjection (rule (pruneRegion rule j)).1‖ < (rule (pruneRegion rule j)).2 then
        PruneOut.witness (rule (pruneRegion rule (Nat.find hA))).1
          (rule (pruneRegion rule (Nat.find hA))).2
      else if P (E ⁻¹' pruneRegion rule (Nat.find hJ)) < ENNReal.ofReal pf then PruneOut.fail
      else PruneOut.pruned
    else
      if hA : ∃ j,
          ‖E'.starProjection (rule (pruneRegion rule j)).1‖ < (rule (pruneRegion rule j)).2 then
        PruneOut.witness (rule (pruneRegion rule (Nat.find hA))).1
          (rule (pruneRegion rule (Nat.find hA))).2
      else PruneOut.pruned

end IllCondRegMem


