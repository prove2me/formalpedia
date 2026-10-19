-- Prove2me | Definitions.Def_MKVLimit_Value_Particle
-- name    : MKVLimit_Value_Particle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:35.871793+00:00
-- url     : https://prove2.me/theorems/89e4c096-7dec-4c5c-a30c-bd9a6da41818
-- title:
--   The $N$-player common-noise control value $V_S^N$
-- statement:
--   For each positive player count $N$, initial states have product law $\nu^1\otimes\cdots\otimes\nu^N$, the players have separate Brownian motions $W^i$, and all share $B$. Every control $\alpha^i$ is predictable for the full particle filtration and has finite integrated $p$th-moment cost. In equation (2.16), the coefficients for particle $i$ use the empirical laws of these same particles,
--
--   $$\varphi_t^N=\frac1N\sum_{i=1}^N\delta_{(X^i_{t\wedge\cdot},\alpha_t^i)},\qquad \varphi_t^{N,X}=\frac1N\sum_{i=1}^N\delta_{X^i_{t\wedge\cdot}}.$$
--
--   The particle value $V_S^N$ is the supremum of the average expected running and terminal rewards (2.17). The definition also supplies the average initial law $N^{-1}\sum_i\nu^i$ used in the goal.
--
--   **Formalization Note** $N$ is a positive natural number; `Fin N` index zero denotes the paper's player one. Empirical laws and averages are uniform mixtures. The canonical particle law has product initial distribution and independent Brownian noises. As in the strong problem, solutions are measurable continuous paths adapted to the completed filtration, with Itô integrals certified entrywise. The empirical law is constructed from the solution being tested.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 11, §2.4, equations (2.16)–(2.17)

import Definitions.Def_MKVLimit_Value_Strong

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

variable {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
variable [MetricSpace U] [MeasurableSpace U]

abbrev OmegaN (T : ℝ≥0) (n d ℓ N : ℕ) :=
  (Fin N → Rn n) × (Fin N → Cpath T d) × Cpath T ℓ

/-- Uniform empirical probability measure on a positive number of atoms. -/
noncomputable def empirical {E : Type*} [MeasurableSpace E]
    (N : ℕ+) (z : Fin N → E) : ProbabilityMeasure E := by
  letI : Nonempty (Fin N) := ⟨⟨0, N.pos⟩⟩
  exact ⟨((PMF.uniformOfFintype (Fin N)).map z).toMeasure, inferInstance⟩

/-- N⁻¹Σᵢνⁱ, with Lean index 0 representing the paper's ν¹. -/
noncomputable def avgLaw {E : Type*} [MeasurableSpace E]
    (N : ℕ+) (ν : ℕ → ProbabilityMeasure E) : ProbabilityMeasure E := by
  letI : Nonempty (Fin N) := ⟨⟨0, N.pos⟩⟩
  let m : Measure (Fin N) := (PMF.uniformOfFintype (Fin N)).toMeasure
  let f : Fin N → Measure E := fun i => (ν i : Measure E)
  exact ⟨m.bind f,
    isProbabilityMeasure_bind ((measurable_of_finite f).aemeasurable) (Filter.Eventually.of_forall (fun _ => inferInstance))⟩

private theorem measurable_particle_coord (N : ℕ+) (s : ℝ≥0) :
    Measurable (fun ω : OmegaN T n d ℓ N =>
      (ω.1, (fun i : Fin N => pathAt (ω.2.1 i) s), pathAt ω.2.2 s)) := by
  refine Measurable.prodMk measurable_fst (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ (fun i =>
      ((continuous_eval_const _).measurable).comp
        (measurable_pi_apply i |>.comp (measurable_fst.comp measurable_snd)))
  · exact ((continuous_eval_const _).measurable).comp (measurable_snd.comp measurable_snd)

/-- Raw particle filtration from all initial states, all idiosyncratic noises, and B. -/
noncomputable def FsN (T : ℝ≥0) (n d ℓ : ℕ) (N : ℕ+) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaN T n d ℓ N)) where
  seq t := ⨆ s ≤ t, MeasurableSpace.comap
    (fun ω : OmegaN T n d ℓ N =>
      (ω.1, (fun i : Fin N => pathAt (ω.2.1 i) s), pathAt ω.2.2 s)) inferInstance
  mono' _ _ hst := iSup₂_le fun s hs => le_iSup₂
    (f := fun s (_ : s ≤ _) => MeasurableSpace.comap
      (fun ω : OmegaN T n d ℓ N =>
        (ω.1, (fun i : Fin N => pathAt (ω.2.1 i) s), pathAt ω.2.2 s)) inferInstance)
    s (hs.trans hst)
  le' _ := iSup₂_le fun s _ => (measurable_particle_coord N s).comap_le

/-- Particle canonical law: product initial states and jointly independent Brownian noises. -/
def IsParticleLaw (N : ℕ+) (ν : Fin N → ProbabilityMeasure (Rn n))
    (P : Measure (OmegaN T n d ℓ N)) : Prop :=
  IsProbabilityMeasure P ∧
  Measure.map (fun ω : OmegaN T n d ℓ N => ω.1) P =
    Measure.pi (fun i : Fin N => (ν i : Measure (Rn n))) ∧
  (∀ i : Fin N, IsFBrownian (FsN T n d ℓ N) P T
    (fun s ω => pathAt (ω.2.1 i) s)) ∧
  IsFBrownian (FsN T n d ℓ N) P T (fun s ω => pathAt ω.2.2 s) ∧
  Measure.map (fun ω : OmegaN T n d ℓ N => (ω.2.1, ω.2.2)) P =
    Measure.prod
      (Measure.pi (fun i : Fin N => Measure.map
        (fun ω : OmegaN T n d ℓ N => ω.2.1 i) P))
      (Measure.map (fun ω : OmegaN T n d ℓ N => ω.2.2) P) ∧
  ∀ s u, s ≤ u → u ≤ T →
    Indep (MeasurableSpace.comap
      (fun ω : OmegaN T n d ℓ N =>
        ((fun i : Fin N => pathAt (ω.2.1 i) u - pathAt (ω.2.1 i) s),
          pathAt ω.2.2 u - pathAt ω.2.2 s)) inferInstance)
      (FsN T n d ℓ N s) P

/-- Each player's control is predictable and has finite p-moment cost. -/
def IsAdmissibleN (M : Model T n d ℓ U) (p : ℝ)
    (N : ℕ+) (P : Measure (OmegaN T n d ℓ N))
    (α : Fin N → ℝ≥0 → OmegaN T n d ℓ N → U) : Prop :=
  ∀ i : Fin N,
    Measurable[predictableOf (FsN T n d ℓ N)]
      (fun z : ℝ≥0 × OmegaN T n d ℓ N => α i z.1 z.2) ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (T : ℝ),
      edist (α i s.toNNReal ω) M.a₀ ^ p ∂volume ∂P < ⊤

/-- The empirical state-control law φᴺₜ from the same particles and controls. -/
noncomputable def phiN (N : ℕ+)
    (X : Fin N → OmegaN T n d ℓ N → Cpath T n)
    (α : Fin N → ℝ≥0 → OmegaN T n d ℓ N → U)
    (t : ℝ≥0) (ω : OmegaN T n d ℓ N) :
    ProbabilityMeasure (Cpath T n × U) :=
  empirical N (fun i => (stopPath t (X i ω), α i t ω))

noncomputable def phiNX (N : ℕ+)
    (X : Fin N → OmegaN T n d ℓ N → Cpath T n)
    (t : ℝ≥0) (ω : OmegaN T n d ℓ N) :
    ProbabilityMeasure (Cpath T n) :=
  empirical N (fun i => stopPath t (X i ω))

/-- Equation (2.16) for every player, with the law φᴺ of these very players. -/
def IsParticleSolution (M : Model T n d ℓ U) (p : ℝ)
    (N : ℕ+) (P : Measure (OmegaN T n d ℓ N))
    (α : Fin N → ℝ≥0 → OmegaN T n d ℓ N → U)
    (X : Fin N → OmegaN T n d ℓ N → Cpath T n) : Prop :=
  ∀ i : Fin N,
    Measurable (X i) ∧
    (∀ t, t ≤ T → Measurable[EthierKurtz.completedSDEPast P (FsN T n d ℓ N) t]
      (fun ω => pathAt (X i ω) t)) ∧
    (∫⁻ ω, ENNReal.ofReal (‖X i ω‖ ^ p) ∂P) < ⊤ ∧
    SDEEquation M P (FsN T n d ℓ N) (fun ω => ω.1 i) (X i)
      (fun ω => ω.2.1 i) (fun ω => ω.2.2) (α i)
      (phiN N X α)

/-- Jᴺ of (2.17), the average of the players' expected rewards. -/
noncomputable def particleReward (M : Model T n d ℓ U)
    (N : ℕ+) (P : Measure (OmegaN T n d ℓ N))
    (α : Fin N → ℝ≥0 → OmegaN T n d ℓ N → U)
    (X : Fin N → OmegaN T n d ℓ N → Cpath T n) : EReal :=
  (((1 / (N : ℝ) : ℝ) : EReal) *
    ∑ i : Fin N, eExp P (fun ω =>
      timeInt 0 T (fun t =>
        (M.L t (stopPath t (X i ω)) (phiN N X α t ω) (α i t ω) : EReal)) +
      (M.g (X i ω) (phiNX N X T ω) : EReal)))

/-- N-player value Vᴺ_S of (2.17). -/
noncomputable def VSN (M : Model T n d ℓ U) (p : ℝ)
    (N : ℕ+) (P : Measure (OmegaN T n d ℓ N)) : EReal :=
  ⨆ (α : Fin N → ℝ≥0 → OmegaN T n d ℓ N → U),
  ⨆ (_ : IsAdmissibleN M p N P α),
  ⨆ (X : Fin N → OmegaN T n d ℓ N → Cpath T n),
  ⨆ (_ : IsParticleSolution M p N P α X), particleReward M N P α X

end MKVLimit.Value


