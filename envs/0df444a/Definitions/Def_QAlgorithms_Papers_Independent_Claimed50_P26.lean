-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26
-- name    : QAlgorithms_Papers_Independent_Claimed50_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:55:36.39088+00:00
-- url     : https://prove2.me/theorems/f07b894b-bd29-4579-9688-7b0a5516e187
-- title:
--   Definitions for A strong converse for classical channel coding using entangled inputs
-- statement:
--   The objects the formalized statements of *A strong converse for classical channel coding using entangled inputs* (arXiv:0903.2838) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ensemblePowerRoot`: PDF p.7 II.6: zeta includes the outer 1/alpha spectral power.
--   - `ensembleRenyiCenter`: PDF p.7 II.6: the constructed center, never an unconstrained comparison state. For a normalized ensemble and alpha>1 its trace denominator is strictly positive.
--   - `ensembleRenyiInformation`: PDF pp.2–3 (6),(11): finite-ensemble alpha-Holevo value, ordinary Holevo at 1.
--   - `cqComparison`: PDF p.7: rho_X tensor sigma, on the same classical register as the accepted cq state.
--   - `channelChi`: PDF pp.2–3 (5),(11): optimize over normalized finite INPUT ensembles. On nonzero finite-dimensional channels, alpha>=1 values lie in [0,log2 d_out], so this real supremum has no empty/unbounded default.
--   - `regularizedChi`: PDF p.2 (4), p.3: positive-block regularization. The normalized sequence is bounded and has a limit on channels at the orders used; limsup denotes that value.
--   - `minOutput`: PDF pp.3,5 (9),(B): the minimum output entropy is constructed from Phi. The density domain is compact nonempty and entropy is continuous for alpha>0.
--   - `LocalEntropyAdditive`: PDF p.5 (B), p.4 n.31: self-tensor additivity only, locally above order 1.
--   - `LocalChiAdditive`: PDF p.5 I.2: local self-tensor additivity of the alpha-Holevo quantity.
--   - `CovariantIrreducible`: PDF p.5 (A): compact (possibly infinite) group, continuous unitary representations, covariance on every density matrix, and no nontrivial invariant output subspace. The input representation is NOT required to be irreducible.
--   - `messages`: PDF p.5 (14): integer message count ceil(2^(nR)), at least one even at R=0.
--   - `negLogSuccess`: PDF p.5 (14): minus-log success, explicitly infinite at success zero.
--   - `unassistedCodingExponent`: PDF p.5 (14): the exponent of optimal unassisted codes, not an arbitrary code. Positive block lengths avoid division by zero; rounding does not change the rate.
--   - `UnassistedExponentialConverse`: PDF pp.2,5: one exponent for every code with rate at least each fixed R>C. Constants can depend on Phi,R, but precede n,M and both code/decoder choices.
--   - `worstDistance`: PDF p.5 I.3: extended worst distance, including singular comparison states.
--   - `outputRadius`: PDF p.5 (15): output-state information radius, in extended reals.
--   - `imageRadius`: PDF p.5 (15): radius with the center restricted to the actual channel image.
--   - `RadiiAttained`: PDF p.5 I.3: both outer minima and every inner maximum are attained. This is a conclusion for compact channel images, not an assumed continuity axiom.
--   - `adjoin`: PDF p.8 II.8: adjoin a new orthogonal classical symbol (index zero). Fin(size+1) is Unit plus Fin(size), so the old classical Hilbert space is enlarged.
--   - `setChi`: PDF p.8: supremum over finite A-ensembles. For nonempty A and alpha>1, values are in [0,log2 d]. II.9 supplies nonemptiness by a maximizing ensemble.
--   - `HasEigenvalues`: PDF p.9 IV.11: a complete eigenvalue list, including multiplicities, with arbitrary order.
--   - `ListedChannel`: PDF pp.1–2: the three named application classes, including the full CP range of the depolarizing parameter; the map acts on every operator, not only states.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, https://arxiv.org/abs/0903.2838v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

/-!
Statements from Koenig and Wehner, arXiv:0903.2838v1, PDF pages 1–9.
Imports outside Defs are pinned accepted libraries, not unreviewed chunks.
All logarithms are in bits. Source corrections: the missing logarithm in
S_alpha (p.3), reversed support inclusion (p.4 n.33), local order scope in
I.4 (p.6), and the enlarged classical register in II.8 (p.8).
II.10 is deferred: its arbitrary-set extrema have no attainment hypotheses.
Density hypotheses reuse IsDensityMatrix directly. Accepted renyiEntropy and petz
supply the positive-order normalized entropy and Petz divergence; cqState fixes
classical-first register order. The remaining ensemble and coding definitions
have paper-specific names: unrelated frozen algebra centers, trace invariants,
composite-testing exponents, and assisted converses are not substituted.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology
open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)
open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)
open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.7 II.6: zeta includes the outer 1/alpha spectral power. -/
def ensemblePowerRoot {I : Type} [Fintype I] [DecidableEq I] (alpha : ℝ) (e : Ensemble I) :
    Matrix I I ℂ :=
  supportPower (∑ x, (e.prob x : ℂ) • supportPower (e.state x) alpha) (1/alpha)

/-- PDF p.7 II.6: the constructed center, never an unconstrained comparison state.
For a normalized ensemble and alpha>1 its trace denominator is strictly positive. -/
def ensembleRenyiCenter {I : Type} [Fintype I] [DecidableEq I] (alpha : ℝ) (e : Ensemble I) :
    Matrix I I ℂ := ((ensemblePowerRoot alpha e).trace)⁻¹ • ensemblePowerRoot alpha e

/-- PDF pp.2–3 (6),(11): finite-ensemble alpha-Holevo value, ordinary Holevo at 1. -/
def ensembleRenyiInformation {I : Type} [Fintype I] [DecidableEq I] (alpha : ℝ) (e : Ensemble I) : ℝ :=
  if alpha = 1 then vnEntropy (ensembleAverage e) - ∑ x, e.prob x * vnEntropy (e.state x)
  else alpha/(alpha-1) * Real.logb 2 (ensemblePowerRoot alpha e).trace.re

/-- PDF p.7: rho_X tensor sigma, on the same classical register as the accepted cq state. -/
def cqComparison {I : Type} [Fintype I] (e : Ensemble I) (sigma : Matrix I I ℂ) :
    Matrix (Fin e.size × I) (Fin e.size × I) ℂ :=
  cqState e.prob (fun _ => sigma)

/-- PDF pp.2–3 (5),(11): optimize over normalized finite INPUT ensembles.
On nonzero finite-dimensional channels, alpha>=1 values lie in [0,log2 d_out],
so this real supremum has no empty/unbounded default. -/
def channelChi {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : ℝ :=
  sSup {v | ∃ e : Ensemble I,
    v = if alpha = 1 then vnEntropy (Phi (ensembleAverage e)) -
      ∑ x, e.prob x * vnEntropy (Phi (e.state x))
    else alpha/(alpha-1) * Real.logb 2
      (supportPower (∑ x, (e.prob x : ℂ) • supportPower (Phi (e.state x)) alpha)
        (1/alpha)).trace.re}

/-- PDF p.2 (4), p.3: positive-block regularization. The normalized sequence is
bounded and has a limit on channels at the orders used; limsup denotes that value. -/
def regularizedChi {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : ℝ :=
  Filter.limsup (fun k : ℕ => channelChi alpha (channelPower Phi (k+1)) / (k+1 : ℕ)) atTop

/-- PDF pp.3,5 (9),(B): the minimum output entropy is constructed from Phi.
The density domain is compact nonempty and entropy is continuous for alpha>0. -/
def minOutput {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : ℝ :=
  sInf {v | ∃ rho : {rho : Matrix I I ℂ // IsDensityMatrix rho}, v = renyiEntropy alpha (Phi rho.1)}

/-- PDF p.5 (B), p.4 n.31: self-tensor additivity only, locally above order 1. -/
def LocalEntropyAdditive {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) : Prop :=
  ∃ beta : ℝ, 1 < beta ∧ ∀ alpha : ℝ, 1 ≤ alpha → alpha < beta →
    ∀ n : ℕ, 0 < n → minOutput alpha (channelPower Phi n) = (n : ℝ) * minOutput alpha Phi

/-- PDF p.5 I.2: local self-tensor additivity of the alpha-Holevo quantity. -/
def LocalChiAdditive {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) : Prop :=
  ∃ beta : ℝ, 1 < beta ∧ ∀ alpha : ℝ, 1 < alpha → alpha < beta →
    ∀ n : ℕ, 0 < n → channelChi alpha (channelPower Phi n) = (n : ℝ) * channelChi alpha Phi

/-- PDF p.5 (A): compact (possibly infinite) group, continuous unitary representations,
covariance on every density matrix, and no nontrivial invariant output subspace.
The input representation is NOT required to be irreducible. -/
def CovariantIrreducible {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) : Prop :=
  ∃ (G : Type) (gG : Group G) (tG : TopologicalSpace G),
    letI : Group G := gG
    letI : TopologicalSpace G := tG
    ∃ (_ : IsTopologicalGroup G) (_ : CompactSpace G) (_ : T2Space G) (U : G →* Matrix.unitaryGroup I ℂ)
    (V : G →* Matrix.unitaryGroup J ℂ),
    Continuous (fun g => (U g : Matrix I I ℂ)) ∧
    Continuous (fun g => (V g : Matrix J J ℂ)) ∧
    (∀ g, ∀ rho : {rho : Matrix I I ℂ // IsDensityMatrix rho},
      Phi ((U g : Matrix I I ℂ) * rho.1 * (U g : Matrix I I ℂ)ᴴ) =
        (V g : Matrix J J ℂ) * Phi rho.1 * (V g : Matrix J J ℂ)ᴴ) ∧
    (∀ S : Submodule ℂ (J → ℂ),
      (∀ g, ∀ v ∈ S, Matrix.mulVec (V g : Matrix J J ℂ) v ∈ S) → S = ⊥ ∨ S = ⊤)

/-- PDF p.5 (14): integer message count ceil(2^(nR)), at least one even at R=0. -/
def messages (n : ℕ) (R : ℝ) : ℕ := max 1 (Nat.ceil (Real.rpow 2 ((n : ℝ)*R)))

/-- PDF p.5 (14): minus-log success, explicitly infinite at success zero. -/
def negLogSuccess (p : ℝ) : EReal := if 0 < p then (-Real.logb 2 p : ℝ) else ⊤

/-- PDF p.5 (14): the exponent of optimal unassisted codes, not an arbitrary code.
Positive block lengths avoid division by zero; rounding does not change the rate. -/
def unassistedCodingExponent {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Phi : Superop I J) (R : ℝ) : EReal :=
  Filter.liminf (fun k : ℕ =>
    ((1 / (k+1 : ℕ) : ℝ) : EReal) *
      negLogSuccess (uaSuccess (channelPower Phi (k+1)) (messages (k+1) R))) atTop

/-- PDF pp.2,5: one exponent for every code with rate at least each fixed R>C.
Constants can depend on Phi,R, but precede n,M and both code/decoder choices. -/
def UnassistedExponentialConverse {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) : Prop :=
  ∀ R : ℝ, ordinaryClassicalCapacity Phi < R →
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ M : ℕ, 0 < M → (n : ℝ)*R ≤ Real.logb 2 M →
        ∀ K : UACode (Fin n → I) (Fin n → J) M,
          uaCodeSuccess (channelPower Phi n) K ≤ Real.rpow 2 (-(c*(n : ℝ)))

/-- PDF p.5 I.3: extended worst distance, including singular comparison states. -/
def worstDistance {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) (sigma : Matrix J J ℂ) : EReal :=
  ⨆ rho : {rho : Matrix I I ℂ // IsDensityMatrix rho}, petz alpha (Phi rho.1) sigma

/-- PDF p.5 (15): output-state information radius, in extended reals. -/
def outputRadius {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : EReal :=
  ⨅ sigma : {rho : Matrix J J ℂ // IsDensityMatrix rho}, worstDistance alpha Phi sigma.1

/-- PDF p.5 (15): radius with the center restricted to the actual channel image. -/
def imageRadius {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : EReal :=
  ⨅ sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho}, worstDistance alpha Phi (Phi sigma.1)

/-- PDF p.5 I.3: both outer minima and every inner maximum are attained.
This is a conclusion for compact channel images, not an assumed continuity axiom. -/
def RadiiAttained {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (alpha : ℝ) (Phi : Superop I J) : Prop :=
  (∃ sigma : {rho : Matrix J J ℂ // IsDensityMatrix rho}, worstDistance alpha Phi sigma.1 = outputRadius alpha Phi) ∧
  (∃ sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho}, worstDistance alpha Phi (Phi sigma.1) = imageRadius alpha Phi) ∧
  (∀ sigma : {rho : Matrix J J ℂ // IsDensityMatrix rho}, ∃ rho : {rho : Matrix I I ℂ // IsDensityMatrix rho},
    petz alpha (Phi rho.1) sigma.1 = worstDistance alpha Phi sigma.1)

/-- PDF p.8 II.8: adjoin a new orthogonal classical symbol (index zero).
Fin(size+1) is Unit plus Fin(size), so the old classical Hilbert space is enlarged. -/
def adjoin {I : Type} [Fintype I] (e : Ensemble I) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : Ensemble I where
  size := e.size + 1
  prob := Fin.cases eta (fun x => (1-eta)*e.prob x)
  state := Fin.cases rho e.state
  nonneg := by
    intro i
    exact Fin.cases h0 (fun x => mul_nonneg (sub_nonneg.mpr h1) (e.nonneg x)) i
  total := by
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    rw [← Finset.mul_sum, e.total]
    ring
  density := by
    intro i
    exact Fin.cases hrho e.density i

/-- PDF p.8: supremum over finite A-ensembles. For nonempty A and alpha>1,
values are in [0,log2 d]. II.9 supplies nonemptiness by a maximizing ensemble. -/
def setChi {I : Type} [Fintype I] [DecidableEq I]
    (alpha : ℝ) (A : Set (Matrix I I ℂ)) : ℝ :=
  sSup {v | ∃ e : Ensemble I, (∀ x, e.state x ∈ A) ∧ v = ensembleRenyiInformation alpha e}

/-- PDF p.9 IV.11: a complete eigenvalue list, including multiplicities, with arbitrary order. -/
def HasEigenvalues {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (lambda : I → ℝ) : Prop :=
  ∃ V : Matrix.unitaryGroup I ℂ,
    A = (V : Matrix I I ℂ) * Matrix.diagonal (fun i => (lambda i : ℂ)) *
      (V : Matrix I I ℂ)ᴴ

/-- PDF pp.1–2: the three named application classes, including the full CP range
of the depolarizing parameter; the map acts on every operator, not only states. -/
def ListedChannel {d : ℕ} (Phi : Superop (Fin d) (Fin d)) : Prop :=
  (d = 2 ∧ Phi ((d : ℂ)⁻¹ • 1) = (d : ℂ)⁻¹ • 1) ∨
  (2 ≤ d ∧ ∃ r : ℝ, -1/((d : ℝ)^2-1) ≤ r ∧ r ≤ 1 ∧
    Phi = depolarizing d (1-r)) ∨
  (2 ≤ d ∧ Phi = wernerHolevo d)

/-- Sanity: the Umegaki branch never uses division by alpha-1. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    petz 1 rho sigma = relative rho sigma := by simp [petz]

/-- Sanity: log(0) in the operational exponent is not Lean's real log default. -/
example : negLogSuccess 0 = ⊤ := by simp [negLogSuccess]

/-- Sanity: the new symbol receives exactly eta, including eta=0 and eta=1. -/
example {I : Type} [Fintype I] (e : Ensemble I) (rho : Matrix I I ℂ)
    (h : IsDensityMatrix rho) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (adjoin e rho h eta h0 h1).prob ⟨0, Nat.zero_lt_succ e.size⟩ = eta := rfl

/-- Sanity: distinct classical labels have zero off-diagonal cq blocks. -/
example {I : Type} [Fintype I] (e : Ensemble I) (x y : Fin e.size)
    (h : x ≠ y) (i j : I) : cqState e.prob e.state (x,i) (y,j) = 0 := by simp [cqState, h]

end QAlgorithms.Papers.Independent.Claimed50.P26


