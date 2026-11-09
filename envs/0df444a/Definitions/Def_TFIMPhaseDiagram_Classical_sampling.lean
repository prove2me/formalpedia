-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_sampling
-- name    : TFIMPhaseDiagram_Classical_sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:47.215868+00:00
-- url     : https://prove2.me/theorems/5b51e344-4a67-4173-9579-1cfa1c2312ec
-- title:
--   Cycle sampler interfaces and explicit mixing/counting budgets
-- statement:
--   A cycle input is either an arbitrary real coupling vector or the source's parity family, including its zero-field limit. Its external fields are finite values or pinning flags. Validity says precisely that the parity rate is nonnegative and the remaining weighted support has positive mass. A bound by $K_M(\eta)$ is expressed directly for positive $\eta$ and as the source's infinite upper bound at $\eta=0$.
--
--   The system law is $\pi=\bigotimes_i\pi_i$ and $\mu_\lambda=T_{\lambda W}\pi$, where
--   $$W(s)=\frac1{2M}\sum_{i,j}J_{ij}\sum_k s_{i,k}s_{j,k}.$$
--   Sampling contracts read Boolean vectors from actual RAM output cells, require measurable outputs, and compare their push-forward laws with the specified target. Exact sampling is TV error zero. Integer budgets use $1+\lceil2Cn\log(L/\epsilon)\rceil$ Glauber steps, a uniform $anM$ cost per step, and the explicit annealing sample counts.
--
--   The interfaces contain no correctness or runtime assumption as model data; those are conclusions of the theorem items.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, Definition 6, p.6; Theorem 12, p.8; Proposition 15, p.9; proofs, pp.9,28–30

import Definitions.Def_TFIMPhaseDiagram_Classical_entropy
import Definitions.Def_TFIMPhaseDiagram_Classical_ram

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

/-- The ordinary cycle and the source's parity-cycle family, with its explicit zero-field limit. -/
inductive CycleParameters (M : ℕ) where
  | ordinary (K : Fin M → ℝ)
  | parity (η : ℝ) (p : Bool)

def specWeight {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : Spins M → ℝ :=
  match K with
  | .ordinary k => cycleWeight k w
  | .parity η p => pathCycleWeight η p w

def specProb {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : Spins M → ℝ :=
  normalize (specWeight K w)
def specLaw {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : Measure (Spins M) :=
  finiteLaw (specProb K w)
def ValidCycle {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : Prop :=
  (match K with | .ordinary _ => True | .parity η _ => 0 ≤ η) ∧
    0 < ∑ s, specWeight K w s

def BoundedCycle {M : ℕ} (η : ℝ) (K : CycleParameters M) : Prop :=
  match K with
  | .ordinary k => η = 0 ∨ ∀ j, |k j| ≤ coupling M η
  | .parity a _ => η ≤ a

def fieldCode : Field → List ℝ
  | .finite a => [0,a] | .plus => [1,0] | .minus => [-1,0]
def specCode {M : ℕ} : CycleParameters M → List ℝ
  | .ordinary k => [0] ++ MatMulTimeLP.vecToList k
  | .parity η p => [1,η,if p then 1 else 0]
def cycleInput {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : List ℝ :=
  [(M : ℝ)] ++ specCode K ++ (List.finRange M).flatMap (fun k => fieldCode (w k))
def spinsOutput (P : RAMProgram) (input : List ℝ) (b M : ℕ) (ω : MatMulTimeLP.Tape) : Spins M :=
  fun k => decide ((ramState P input ω b).R (input.length+k.val) < 0)
def vectorOutput (P : RAMProgram) (input : List ℝ) (b n M : ℕ) (ω : MatMulTimeLP.Tape) : Fin n → Spins M :=
  fun i k => decide ((ramState P input ω b).R (input.length+i.val*M+k.val) < 0)
def SamplesCycle (P : RAMProgram) (b : ℕ) {M : ℕ} (K : CycleParameters M) (w : Fin M → Field) : Prop :=
  let input := cycleInput K w
  let out := spinsOutput P input b M
  HaltsWithin P input b ∧ Measurable out ∧ MatMulTimeLP.tapeLaw.map out = specLaw K w

def systemInput {n M : ℕ} (K : Fin n → CycleParameters M) (w : Fin n → Fin M → Field)
    (J : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  [(n : ℝ),(M : ℝ)] ++ MatMulTimeLP.matToList J ++
    (List.finRange n).flatMap (fun i => specCode (K i) ++
      (List.finRange M).flatMap (fun k => fieldCode (w i k)))
def systemBase {n M : ℕ} (K : Fin n → CycleParameters M) (w : Fin n → Fin M → Field) :=
  Measure.pi (fun i => specLaw (K i) (w i))
def systemTilt {n M : ℕ} (K : Fin n → CycleParameters M) (w : Fin n → Fin M → Field)
    (J : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :=
  tilt (systemBase K w) (fun s => lam * cycleInteraction J s)
def systemRun {n M : ℕ} (K : Fin n → CycleParameters M) (w : Fin n → Fin M → Field)
    (J : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (ρ : Measure (Fin n → Spins M)) (t : ℕ) :=
  glauberRun (fun i => specLaw (K i) (w i)) (fun s => lam*cycleInteraction J s) ρ t

def mixingBudget (a n M : ℕ) (C L ε : ℝ) : ℕ :=
  a*n*M*(1+⌈2*C*n*Real.log (L/ε)⌉₊)
def countingBudget (a n M L : ℕ) (C ε δ : ℝ) : ℕ :=
  mixingBudget a n M C L (1/(8*(baseSamples L (ε/2) : ℝ))) * totalSamples L (ε/2) δ

def SamplesSystem (P : RAMProgram) (b n M : ℕ) (input : List ℝ)
    (μ : Measure (Fin n → Spins M)) (ε : ℝ) : Prop :=
  let out := vectorOutput P input b n M
  HaltsWithin P input b ∧ Measurable out ∧ tv (MatMulTimeLP.tapeLaw.map out) μ ≤ ε
end TFIMPhaseDiagram.Classical


