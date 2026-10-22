-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25
-- name    : QAlgorithms_Papers_Independent_Gap48_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:38:02.784364+00:00
-- url     : https://prove2.me/theorems/9b8d2b2a-39e2-4085-bb38-00ff7bc6af6b
-- title:
--   Definitions for The Security of Practical Quantum Key Distribution
-- statement:
--   The objects the formalized statements of *The Security of Practical Quantum Key Distribution* (arXiv:0802.4155) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhotonLaw`: Normalized photon-number law, IV.A.1, PDF pp.26–27.
--   - `vacuumLaw`: Vacuum law, IV.A.1, PDF p.27.
--   - `classicalMI`: Classical mutual information, I.B.5, PDF p.5.
--   - `IRRecord`: Eve's record: none if untouched, otherwise (basis match, outcome). Actual basis labels are independent public randomness. I.B.5, PDF p.5.
--   - `irLaw`: Sifted joint law of uniform BB84 bits for the specified attack. The wrong-basis outcomes are fair, as in the BB84 Born table. I.B.5, PDF p.5.
--   - `irError`: Error event in the same sifted experiment, I.B.5, PDF p.5.
--   - `irAE`: Alice–Eve marginal, I.B.5, PDF p.5.
--   - `irBE`: Bob–Eve marginal, I.B.5, PDF p.5.
--   - `sourceReplacementVector`: Eq.(4), PDF p.8, on an arbitrary Hilbert signal space. The finite direct sum is canonically the tensor product of the label register with that space. This is a preparation vector, distinct from Dependency50.P32.replacement, which constructs the Choi matrix of a replacement channel.
--   - `replacementBlock`: Actual unnormalized conditional signal operator, Eq.(4), PDF p.8.
--   - `replacementReduction`: Partial trace over the orthonormal label register in the direct-sum model, Eq.(4), PDF p.8. No finite cutoff is placed on the signal space H.
--   - `lossPattern`: Independent photon survival pattern probability, IV.A.1, PDF p.27.
--   - `survivorLaw`: Exactly k survivors in the actual independent experiment, IV.A.1, PDF p.27.
--   - `thinned`: Mixture of the photon-loss experiments, IV.A.1, PDF p.27.
--   - `signedRate`: Signed bookkeeping (25), PDF p.28. This definition alone asserts no security.
--   - `zeroProxy`: Zero-error weak-pulse quadratic proxy, IV.B.4, PDF p.29; not a Poisson law.
--   - `noDecoyF`: F(Q) in (36)–(37), PDF p.29; there is one h(Q) term.
--   - `noDecoyProxy`: Quadratic proxy using 2Q only inside entropy, Eqs.(36)–(37), PDF p.29.
--   - `noDecoyOptimizer`: Optimizer of that quadratic proxy, Eq.(37), PDF p.29.
--   - `decoyProxy`: Proxy replacing exp(-mu) by 1-mu, Eqs.(38)–(39), PDF pp.29–30.
--   - `decoyOptimizer`: Optimizer of the decoy proxy, Eq.(39), PDF p.30.
--   - `MixedSignal`: A countable convex mixture of unit vectors on the full signal Hilbert space, IV.A.1, PDF pp.26–27. Every normalized trace-class state admits such a representation; no orthogonality or finite support is imposed.
--   - `signalExpectation`: Born expectation of an effect in the actual signal mixture, Eq.(32), PDF p.29.
--   - `decoyComponent`: Frequency-weighted component rate from setting-independent conditional states and one receiver effect, Eqs.(27),(32), PDF pp.28–29.
--   - `decoyWrong`: Wrong-detection rate from a subeffect W of the same instrument, Eq.(32), PDF p.29; linear in g_n, not separately in epsilon_n.
--   - `calibratedPhoton`: Calibrated photon rate, Eq.(46), PDF p.31.
--   - `calibratedDark`: Calibrated dark rate, Eq.(47), PDF p.31. The model uses 2p_d exactly.
--   - `calibratedTotal`: Total calibrated detection rate, Eq.(44), PDF p.31.
--   - `calibratedFraction`: Photon fraction in IV.C's notation, distinct from IV.A's fractions, PDF p.31.
--   - `sargAccepted`: Equal Bob-basis branches, with other-basis minus probability 1/2 as required by footnote 58; Eq.(53), PDF p.32.
--   - `sargWrong`: Wrong same-basis branch, Eqs.(53)–(54), PDF p.32.
--   - `networkCount`: Continuous device count with free trusted stations, Eq.(79), PDF p.40.
--   - `networkCost`: Continuous network cost, Eq.(79), PDF p.40.
--   - `directLaw`: Three independent Bernoulli factors: total propagation t and two endpoint detections eta. Appendix B, Eq.(B1), PDF p.46.
--   - `directRate`: Coincidence rate in the noiseless direct-link toy model, Eq.(B1), PDF p.46.
--   - `geometricRound`: Geometric waiting law on positive rounds, footnote 75, PDF p.46.
--   - `twoLinkWaiting`: Maximum of two independent waiting times, computed from their product law. Footnote 75, PDF p.46.
--   - `waitingMean`: Exact footnote-75 mean, PDF p.46; used only for 0<x<=1.
--   - `modeSuccess`: Multimode success per round, footnote 75, PDF p.46.
--   - `cycleTime`: Exact-mean cycle time, Eq.(B2) and footnote 75, PDF p.46.
--   - `repeaterRate`: Mean-cutoff toy rate, Eq.(B2), PDF pp.46–47. Equality at the lifetime cuts the rate to zero; random memory-expiration histories are not modelled.
--   - `bellLaw`: Depolarized Bell measurement: index 0 desired; index 1 has the same key correlations. Appendix B, PDF pp.46–47.
--   - `bellError`: Two wrong Bell outcomes reverse the key correlation, Eq.(B3), PDF p.47.
--   - `repeaterKey`: Assigned signed one-way perfect-EC yield of the mean-cycle toy model, Eq.(B3), PDF p.47.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, https://arxiv.org/abs/0802.4155v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

/-! Statements from arXiv:0802.4155v3. Deferred operational security results are
listed in HARD.md and GAPS.json. Exact model calculations do not assert error
bounds for their physical approximations. Compilation is pending batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate
open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Normalized photon-number law, IV.A.1, PDF pp.26–27. -/
structure PhotonLaw where
  mass : ℕ → ℝ
  nonnegative : ∀ n, 0 ≤ mass n
  normalized : HasSum mass 1

/-- Vacuum law, IV.A.1, PDF p.27. -/
def vacuumLaw : PhotonLaw where
  mass n := if n = 0 then 1 else 0
  nonnegative n := by split_ifs <;> norm_num
  normalized := by simpa using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))

/-- Classical mutual information, I.B.5, PDF p.5. -/
def classicalMI {X Y : Type} [Fintype X] [Fintype Y] (p : X × Y → ℝ) : ℝ := by
  classical
  exact classicalEntropy (fun x => ∑ y, p (x,y)) +
    classicalEntropy (fun y => ∑ x, p (x,y)) - classicalEntropy p

/-- Eve's record: none if untouched, otherwise (basis match, outcome).
Actual basis labels are independent public randomness. I.B.5, PDF p.5. -/
abbrev IRRecord := Option (Bool × Bool)

/-- Sifted joint law of uniform BB84 bits for the specified attack. The wrong-basis
outcomes are fair, as in the BB84 Born table. I.B.5, PDF p.5. -/
def irLaw (p : ℝ) (a b : Bool) : IRRecord → ℝ
  | none => if a = b then (1-p)/2 else 0
  | some (true,e) => if a = b ∧ a = e then p/4 else 0
  | some (false,_) => p/16

/-- Error event in the same sifted experiment, I.B.5, PDF p.5. -/
def irError (p : ℝ) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, ∑ e : IRRecord, if a ≠ b then irLaw p a b e else 0

/-- Alice–Eve marginal, I.B.5, PDF p.5. -/
def irAE (p : ℝ) (z : Bool × IRRecord) : ℝ := ∑ b : Bool, irLaw p z.1 b z.2

/-- Bob–Eve marginal, I.B.5, PDF p.5. -/
def irBE (p : ℝ) (z : Bool × IRRecord) : ℝ := ∑ a : Bool, irLaw p a z.1 z.2

/-- Eq.(4), PDF p.8, on an arbitrary Hilbert signal space. The finite direct
sum is canonically the tensor product of the label register with that space.
This is a preparation vector, distinct from Dependency50.P32.replacement,
which constructs the Choi matrix of a replacement channel. -/
def sourceReplacementVector {S H : Type*} [Fintype S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (psi : S → H) : PiLp 2 (fun _ : S => H) :=
  WithLp.toLp 2 (fun s => ((Real.sqrt (Fintype.card S : ℝ))⁻¹ : ℂ) • psi s)

/-- Actual unnormalized conditional signal operator, Eq.(4), PDF p.8. -/
def replacementBlock {S H : Type*} [Fintype S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (psi : S → H) (s : S) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ (sourceReplacementVector psi s) (sourceReplacementVector psi s)

/-- Partial trace over the orthonormal label register in the direct-sum model,
Eq.(4), PDF p.8. No finite cutoff is placed on the signal space H. -/
def replacementReduction {S H : Type*} [Fintype S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (psi : S → H) : H →L[ℂ] H := ∑ s, replacementBlock psi s

/-- Independent photon survival pattern probability, IV.A.1, PDF p.27. -/
def lossPattern (n : ℕ) (t : ℝ) (b : Fin n → Bool) : ℝ :=
  ∏ i, if b i then t else 1-t

/-- Exactly k survivors in the actual independent experiment, IV.A.1, PDF p.27. -/
def survivorLaw (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ b : Fin n → Bool, if (Finset.univ.filter fun i => b i = true).card = k
    then lossPattern n t b else 0

/-- Mixture of the photon-loss experiments, IV.A.1, PDF p.27. -/
def thinned (p : PhotonLaw) (t : ℝ) (k : ℕ) : ℝ := ∑' n, p.mass n * survivorLaw n t k

/-- Signed bookkeeping (25), PDF p.28. This definition alone asserts no security. -/
def signedRate (R leak info : ℝ) : ℝ := R * (1-leak-info)

/-- Zero-error weak-pulse quadratic proxy, IV.B.4, PDF p.29; not a Poisson law. -/
def zeroProxy (s mu : ℝ) : ℝ := mu*s-mu^2/2

/-- F(Q) in (36)–(37), PDF p.29; there is one h(Q) term. -/
def noDecoyF (Q : ℝ) : ℝ := 1-QAlgorithms.binEntropy2 (2*Q)-QAlgorithms.binEntropy2 Q

/-- Quadratic proxy using 2Q only inside entropy, Eqs.(36)–(37), PDF p.29. -/
def noDecoyProxy (nu s Q mu : ℝ) : ℝ :=
  nu * (mu*s*noDecoyF Q-mu^2*(1-QAlgorithms.binEntropy2 (2*Q))/2)

/-- Optimizer of that quadratic proxy, Eq.(37), PDF p.29. -/
def noDecoyOptimizer (s Q : ℝ) : ℝ := s*noDecoyF Q/(1-QAlgorithms.binEntropy2 (2*Q))

/-- Proxy replacing exp(-mu) by 1-mu, Eqs.(38)–(39), PDF pp.29–30. -/
def decoyProxy (nu s Q mu : ℝ) : ℝ :=
  nu*s*mu*((1-mu)*(1-QAlgorithms.binEntropy2 Q)-QAlgorithms.binEntropy2 Q)

/-- Optimizer of the decoy proxy, Eq.(39), PDF p.30. -/
def decoyOptimizer (Q : ℝ) : ℝ := (1-QAlgorithms.binEntropy2 Q/(1-QAlgorithms.binEntropy2 Q))/2

/-- A countable convex mixture of unit vectors on the full signal Hilbert
space, IV.A.1, PDF pp.26–27. Every normalized trace-class state admits such a
representation; no orthogonality or finite support is imposed. -/
structure MixedSignal (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  weights : PhotonLaw
  vector : ℕ → H
  unit : ∀ j, ‖vector j‖ = 1

/-- Born expectation of an effect in the actual signal mixture, Eq.(32), PDF p.29. -/
def signalExpectation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (rho : MixedSignal H) (M : H →L[ℂ] H) : ℝ :=
  ∑' j, rho.weights.mass j * (inner ℂ (rho.vector j) (M (rho.vector j))).re

/-- Frequency-weighted component rate from setting-independent conditional states
and one receiver effect, Eqs.(27),(32), PDF pp.28–29. -/
def decoyComponent {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (nu : ℝ) (w : X → ℝ) (p : X → PhotonLaw) (rho : ℕ → MixedSignal H)
    (M : H →L[ℂ] H) (xi : X) (n : ℕ) : ℝ :=
  nu*w xi*(p xi).mass n*signalExpectation (rho n) M

/-- Wrong-detection rate from a subeffect W of the same instrument, Eq.(32),
PDF p.29; linear in g_n, not separately in epsilon_n. -/
def decoyWrong {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (nu : ℝ) (w : X → ℝ) (p : X → PhotonLaw) (rho : ℕ → MixedSignal H)
    (W : H →L[ℂ] H) (xi : X) (n : ℕ) : ℝ :=
  nu*w xi*(p xi).mass n*signalExpectation (rho n) W

/-- Calibrated photon rate, Eq.(46), PDF p.31. -/
def calibratedPhoton (p : PhotonLaw) (nu b : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  nu*p.mass n*f n*b

/-- Calibrated dark rate, Eq.(47), PDF p.31. The model uses 2p_d exactly. -/
def calibratedDark (p : PhotonLaw) (nu b pd : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  nu*p.mass n*(1-f n*b)*(2*pd)

/-- Total calibrated detection rate, Eq.(44), PDF p.31. -/
def calibratedTotal (p : PhotonLaw) (nu b pd : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' n, (calibratedPhoton p nu b f n + calibratedDark p nu b pd f n)

/-- Photon fraction in IV.C's notation, distinct from IV.A's fractions, PDF p.31. -/
def calibratedFraction (p : PhotonLaw) (nu b pd : ℝ) (f : ℕ → ℝ) : ℝ :=
  (∑' n, calibratedPhoton p nu b f n)/calibratedTotal p nu b pd f

/-- Equal Bob-basis branches, with other-basis minus probability 1/2 as required
by footnote 58; Eq.(53), PDF p.32. -/
def sargAccepted (nu pa f e : ℝ) : ℝ := nu*pa*f*((1/2)*e+(1/2)*(1/2))

/-- Wrong same-basis branch, Eqs.(53)–(54), PDF p.32. -/
def sargWrong (nu pa f e : ℝ) : ℝ := nu*pa*f*((1/2)*e)

/-- Continuous device count with free trusted stations, Eq.(79), PDF p.40. -/
def networkCount (L target ell rate : ℝ) : ℝ := (L/ell)*(target/rate)

/-- Continuous network cost, Eq.(79), PDF p.40. -/
def networkCost (C L target ell rate : ℝ) : ℝ := C*networkCount L target ell rate

/-- Three independent Bernoulli factors: total propagation t and two endpoint
detections eta. Appendix B, Eq.(B1), PDF p.46. -/
def directLaw (t eta : ℝ) (b : Fin 3 → Bool) : ℝ :=
  (if b 0 then t else 1-t) * (if b 1 then eta else 1-eta) * (if b 2 then eta else 1-eta)

/-- Coincidence rate in the noiseless direct-link toy model, Eq.(B1), PDF p.46. -/
def directRate (nu t eta : ℝ) : ℝ :=
  nu * ∑ b : Fin 3 → Bool, if (∀ i, b i = true) then directLaw t eta b else 0

/-- Geometric waiting law on positive rounds, footnote 75, PDF p.46. -/
def geometricRound (x : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else x*(1-x)^(n-1)

/-- Maximum of two independent waiting times, computed from their product law.
Footnote 75, PDF p.46. -/
def twoLinkWaiting (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1),
    if max i j = n then geometricRound x i*geometricRound x j else 0

/-- Exact footnote-75 mean, PDF p.46; used only for 0<x<=1. -/
def waitingMean (x : ℝ) : ℝ := (3-2*x)/(x*(2-x))

/-- Multimode success per round, footnote 75, PDF p.46. -/
def modeSuccess (t eta : ℝ) (N : ℕ) : ℝ := 1-(1-Real.sqrt t*eta)^N

/-- Exact-mean cycle time, Eq.(B2) and footnote 75, PDF p.46. -/
def cycleTime (ell c t eta : ℝ) (N : ℕ) : ℝ := (ell/c)*waitingMean (modeSuccess t eta N)

/-- Mean-cutoff toy rate, Eq.(B2), PDF pp.46–47. Equality at the lifetime cuts
the rate to zero; random memory-expiration histories are not modelled. -/
def repeaterRate (ell c t eta : ℝ) (N : ℕ) (life pM etaM : ℝ) : ℝ :=
  let tau := cycleTime ell c t eta N
  if tau < life then tau⁻¹*(pM^2*etaM^2/2) else 0

/-- Depolarized Bell measurement: index 0 desired; index 1 has the same key
correlations. Appendix B, PDF pp.46–47. -/
def bellLaw (F : ℝ) (i : Fin 4) : ℝ := if i = 0 then F else (1-F)/3

/-- Two wrong Bell outcomes reverse the key correlation, Eq.(B3), PDF p.47. -/
def bellError (F : ℝ) : ℝ := ∑ i : Fin 4, if i.val ≥ 2 then bellLaw F i else 0

/-- Assigned signed one-way perfect-EC yield of the mean-cycle toy model,
Eq.(B3), PDF p.47. -/
def repeaterKey (R F : ℝ) : ℝ :=
  signedRate R (QAlgorithms.binEntropy2 (bellError F)) (QAlgorithms.binEntropy2 (bellError F))

/-! Sanity examples pin definitions only; source theorem proofs are not attempted. -/

example : vacuumLaw.mass 0 = 1 := by simp [vacuumLaw]

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : H) :
    sourceReplacementVector (fun _ : Unit => u) () = u := by simp [sourceReplacementVector]

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (rho : MixedSignal H) :
    signalExpectation rho 0 = 0 := by simp [signalExpectation]

example : lossPattern 0 (1/3) (fun _ => false) = 1 := by simp [lossPattern]

example : zeroProxy 1 1 = (1/2 : ℝ) := by norm_num [zeroProxy]

example : noDecoyF 0 = 1 := by simp [noDecoyF, QAlgorithms.binEntropy2]

example : decoyOptimizer 0 = (1/2 : ℝ) := by simp [decoyOptimizer, QAlgorithms.binEntropy2]

example : sargAccepted 1 1 1 0 = (1/4 : ℝ) := by norm_num [sargAccepted]

example : geometricRound 1 1 = 1 := by norm_num [geometricRound]

example : waitingMean 1 = 1 := by norm_num [waitingMean]

example : modeSuccess 1 1 1 = 1 := by norm_num [modeSuccess]

example : bellLaw 1 1 = 0 := by norm_num [bellLaw]

example : repeaterKey 0 1 = 0 := by simp [repeaterKey, signedRate]

end QAlgorithms.Papers.Independent.Gap48.P25


