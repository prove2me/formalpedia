-- Prove2me | Definitions.Def_ProcessingNetworks_TaskAllocation_ProcessFamily
-- name    : ProcessingNetworks_TaskAllocation_ProcessFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:41:04.040273+00:00
-- url     : https://prove2.me/theorems/d412058f-7811-40ec-8804-75c51aacbeeb
-- title:
--   The raw process family, fluid limit paths, and fluid limit stability (Section 11.7)
-- statement:
--   Restated from mission III's `FluidStability` apparatus (Section 6.3, Definitions 6.1/6.6),
--   adapted to the task allocation model of Sections 11.3–11.7: an augmented basic SPN with
--   $I = LK$ classes $(\ell, k)$, single-server pools $b = 1$ (11.1), FCFS non-idling service at
--   each server, alternate routing with immediate commitment of the tasks of the Markovian arrival
--   process $U$, and i.i.d. service times $v_{\ell k}$ per class. `TaskAllocationProcessFamily`
--   bundles, for each initial state $x$ of the ambient chain (mission I's `MarkovRepresentation` on
--   the flat class index), the residual service times of the tasks present at time $0$ (drawn from a
--   finite pool independent of $(U, v)$), the routed-arrival, start, completion, open-service,
--   effort and buffer-content processes $E^x, S^x, D^x, N^x, T^x, Z^x$, and the relations that
--   define the model: $\sum_k E^x_{\ell k} = U_\ell$ (11.9), $Z = Z(0) + E - D$ (11.10),
--   $N = N(0) + S - D$ (2.7), at most one task in service per server, no idling while a server has
--   tasks, full-speed service $T = \int N$ (2.22), the key relationship (6.51) between effort,
--   completions and the class's delayed random walk, and the identification $Z^x(t) \sim Z(t) \mid
--   X(0) = x$ of the version for $x$ with the chain started in $x$. `FluidLimitPathAt fam ω xseq`
--   is convergence of the fluid-scaled raw processes, u.o.c., to a continuous $(\hat E,\hat D,\hat Z)$
--   along the sample point $\omega$ and a sequence of initial states with $|x_n|\to\infty$;
--   `FluidLimitPath` (Definition 6.6) is such convergence along some $(\omega, \{x_n\})$;
--   `TaskAllocationFluidLimitStable` (Definition 6.1) is uniform attraction of every fluid limit
--   path to the origin.
--
--   **Formalization note.** Carrying the model's actual relations (rather than three bare real
--   processes with a balance identity) is what makes Theorem 11.4 true: the existence of fluid
--   limits and the equations (11.12), (11.15) rest on the routing identity (11.9) with the shared
--   arrival process, on the single-server non-idling service mechanism and on (6.51), none of which
--   a bare family supplies. $E^x, D^x, Z^x$ are integer-valued as in the book and cast to
--   $\mathbb{R}$ in the scaling (6.37).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 217, Section 11.7; p. 106-116, Definitions 6.1, 6.6 (mission III, restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_AmbientChain

namespace ProcessingNetworks.TaskAllocation

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Uniform convergence on compact sets ("u.o.c.", Definition A.6), for a doubly-indexed
`(ℓ,k)`-family of functions — the mode of convergence in (11.17)/(6.39). A straightforward
generalization of mission III's `UOCConverges` (restated, not imported, per this series'
convention) from a singly-indexed family to the doubly-indexed `Fin L × Fin K`-shaped processes
this chapter's classes carry. -/
def UOCConverges2 {L K : ℕ} (f : ℕ → ℝ → Fin L → Fin K → ℝ) (g : ℝ → Fin L → Fin K → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
    ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ℓ k, |f n t ℓ k - g t ℓ k| < ε

/-- Section 6.3's "standard setup," restated for the task allocation model (Sections 11.3–11.7):
the model is an augmented basic SPN with `I = LK` classes `(ℓ, k)`, single-server pools `b = 1`
(11.1), FCFS non-idling service at each server, alternate routing with immediate commitment
(Section 4.2) of the tasks of the Markovian arrival process `U`, and i.i.d. service times
`v ℓ k` for class `(ℓ, k)`. One version of the model per initial state `x` of the ambient chain
`Mrep` (mission I's `MarkovRepresentation` for the flat class index `idx`) is built on a common
probability space from the shared core elements `U`, `v` and an `x`-dependent set of residual
service times `Psi x` of the tasks present at time `0`, drawn from a finite pool independent of
`(U, v)` (Assumption 3.8, (6.36)). For each `x`: `E^x` are the routed arrivals (`∑_k E^x_{ℓk} =
U_ℓ`, (11.9)), `S^x` service starts, `D^x` completions (`= F`), `N^x` open services, `T^x`
cumulative effort, `Z^x` buffer contents ((11.10) and (2.7)), with `(N^x(0), Z^x(0)) = f(x)`; a
server serves at most one task at a time, never idles while it has tasks, works at full speed
((2.22): `T = ∫ N`), and its completions obey the key relationship (6.51) with the class's delayed
random walk; and `Z^x(t)` has the law of `Z(t)` under `P_x = ℙ[|{X(0) = x}]`. -/
structure TaskAllocationProcessFamily {Xstate : Type*} [Countable Xstate] {Ω : Type*}
    [MeasureSpace Ω] {L K : ℕ} (dat : TaskAllocationData L K)
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    (Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z)
    (U : Fin L → ℝ → Ω → ℕ) (v : Fin L → Fin K → ℕ → Ω → ℝ) : Type _ where
  Psi : Xstate → Fin L → Fin K → ℕ → Ω → ℝ
  E : Xstate → ℝ → Ω → Fin L → Fin K → ℕ
  S : Xstate → ℝ → Ω → Fin L → Fin K → ℕ
  D : Xstate → ℝ → Ω → Fin L → Fin K → ℕ
  Nx : Xstate → ℝ → Ω → Fin L → Fin K → ℕ
  T : Xstate → ℝ → Ω → Fin L → Fin K → ℝ
  Zx : Xstate → ℝ → Ω → Fin L → Fin K → ℕ
  N_init : ∀ x ω ℓ k, Nx x 0 ω ℓ k = (Mrep.f x).1 (idx ℓ k)
  Z_init : ∀ x ω ℓ k, Zx x 0 ω ℓ k = (Mrep.f x).2 (idx ℓ k)
  E_init : ∀ x ω ℓ k, E x 0 ω ℓ k = 0
  E_mono : ∀ x ω ℓ k, Monotone fun t => E x t ω ℓ k
  routing : ∀ x ω (t : ℝ) ℓ, 0 ≤ t → ∑ k, E x t ω ℓ k = U ℓ t ω
  S_init : ∀ x ω ℓ k, S x 0 ω ℓ k = 0
  S_mono : ∀ x ω ℓ k, Monotone fun t => S x t ω ℓ k
  D_init : ∀ x ω ℓ k, D x 0 ω ℓ k = 0
  D_mono : ∀ x ω ℓ k, Monotone fun t => D x t ω ℓ k
  counts : ∀ x ω (t : ℝ) ℓ k, 0 ≤ t → Nx x t ω ℓ k + D x t ω ℓ k = Nx x 0 ω ℓ k + S x t ω ℓ k
  balance : ∀ x ω (t : ℝ) ℓ k, 0 ≤ t → Zx x t ω ℓ k + D x t ω ℓ k = Zx x 0 ω ℓ k + E x t ω ℓ k
  availability : ∀ x ω (t : ℝ) ℓ k, 0 ≤ t → Nx x t ω ℓ k ≤ Zx x t ω ℓ k
  single_server : ∀ x ω (t : ℝ) k, 0 ≤ t → ∑ ℓ, Nx x t ω ℓ k ≤ 1
  nonidling : ∀ x ω (t : ℝ) k, 0 ≤ t → 0 < ∑ ℓ, Zx x t ω ℓ k → ∑ ℓ, Nx x t ω ℓ k = 1
  effort : ∀ x ω (t : ℝ) ℓ k, 0 ≤ t → T x t ω ℓ k = ∫ u in (0 : ℝ)..t, (Nx x u ω ℓ k : ℝ)
  effort_completions : ∀ x ω (t : ℝ) ℓ k, 0 ≤ t →
    taWalk ((Mrep.f x).1 (idx ℓ k)) (Psi x ℓ k) (v ℓ k) (D x t ω ℓ k) ω -
        Nx x t ω ℓ k *
          taMax ((Mrep.f x).1 (idx ℓ k)) (Psi x ℓ k) (v ℓ k) (D x t ω ℓ k + Nx x t ω ℓ k) ω ≤
      T x t ω ℓ k ∧
    T x t ω ℓ k ≤
      taWalk ((Mrep.f x).1 (idx ℓ k)) (Psi x ℓ k) (v ℓ k) (D x t ω ℓ k + Nx x t ω ℓ k) ω
  pool : Finset (Ω → ℝ)
  Psi_mem_pool : ∀ x ℓ k n, n < (Mrep.f x).1 (idx ℓ k) → (fun ω => Psi x ℓ k n ω) ∈ pool
  pool_indep :
    Indep (MeasurableSpace.comap (fun ω => fun p : {p // p ∈ pool} => p.1 ω) inferInstance)
      (MeasurableSpace.comap (fun ω => (fun ℓ t => U ℓ t ω, fun ℓ k n => v ℓ k n ω)) inferInstance)
      ℙ
  initial_support : ∀ x, ℙ {ω | Mrep.X 0 ω = x} ≠ 0
  law : ∀ x (t : ℝ) (z : Fin L → Fin K → ℕ), 0 ≤ t →
    ℙ {ω | ∀ ℓ k, Zx x t ω ℓ k = z ℓ k} =
      (ℙ[|{ω | Mrep.X 0 ω = x}]) {ω | ∀ ℓ k, Z t ω (idx ℓ k) = z ℓ k}

/-- A fluid limit path of the task allocation model along an explicit sample point `ω` and
sequence of initial states `xseq` with `|xseq n| → ∞` (`|x| = Mrep.size x`): a triple
`(Ê, D̂, Ẑ)` of continuous functions to which the fluid-scaled raw processes (6.37)/(11.17)
converge u.o.c. (`Ŵ` is determined from `Ẑ` via (11.14)/(11.21)). -/
def FluidLimitPathAt {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {L K : ℕ} {dat : TaskAllocationData L K}
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    {Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z}
    {U : Fin L → ℝ → Ω → ℕ} {v : Fin L → Fin K → ℕ → Ω → ℝ}
    (fam : TaskAllocationProcessFamily dat Mrep U v) (ω : Ω) (xseq : ℕ → Xstate)
    (Eh Dh Zh : ℝ → Fin L → Fin K → ℝ) : Prop :=
  Continuous Eh ∧ Continuous Dh ∧ Continuous Zh ∧
  Tendsto (fun n => Mrep.size (xseq n)) atTop atTop ∧
  UOCConverges2 (fun n t ℓ k =>
    (Mrep.size (xseq n))⁻¹ * (fam.E (xseq n) (Mrep.size (xseq n) * t) ω ℓ k : ℝ)) Eh ∧
  UOCConverges2 (fun n t ℓ k =>
    (Mrep.size (xseq n))⁻¹ * (fam.D (xseq n) (Mrep.size (xseq n) * t) ω ℓ k : ℝ)) Dh ∧
  UOCConverges2 (fun n t ℓ k =>
    (Mrep.size (xseq n))⁻¹ * (fam.Zx (xseq n) (Mrep.size (xseq n) * t) ω ℓ k : ℝ)) Zh

/-- Definition 6.6 (fluid limit path), restated for this model: `(Ê, D̂, Ẑ)` is a fluid limit
path if it is one along some sample point and some sequence of initial states. -/
def FluidLimitPath {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {L K : ℕ}
    {dat : TaskAllocationData L K}
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    {Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z}
    {U : Fin L → ℝ → Ω → ℕ} {v : Fin L → Fin K → ℕ → Ω → ℝ}
    (fam : TaskAllocationProcessFamily dat Mrep U v)
    (Eh Dh Zh : ℝ → Fin L → Fin K → ℝ) : Prop :=
  ∃ (ω : Ω) (xseq : ℕ → Xstate), FluidLimitPathAt fam ω xseq Eh Dh Zh

/-- Definition 6.1 (fluid limit stability), restated for this model: there is `γ > 0` such that
every fluid limit path `(Ê,D̂,Ẑ)` reaches `Ẑ = 0` by time `γ|Ẑ(0)|`. This, not
`WWTAFluidModelSolution`'s stability, is the hypothesis of Theorem 11.5 (the bridge from fluid
behaviour to the original stochastic model) — the same distinction mission III draws between
`FluidLimitStable` and `FluidModelStable`. -/
def TaskAllocationFluidLimitStable {Xstate : Type*} [Countable Xstate] {Ω : Type*}
    [MeasureSpace Ω] {L K : ℕ} {dat : TaskAllocationData L K}
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    {Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z}
    {U : Fin L → ℝ → Ω → ℕ} {v : Fin L → Fin K → ℕ → Ω → ℝ}
    (fam : TaskAllocationProcessFamily dat Mrep U v) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Eh Dh Zh : ℝ → Fin L → Fin K → ℝ),
    FluidLimitPath fam Eh Dh Zh → ∀ t : ℝ, γ * (∑ ℓ, ∑ k, Zh 0 ℓ k) ≤ t → Zh t = fun _ _ => 0

end ProcessingNetworks.TaskAllocation


