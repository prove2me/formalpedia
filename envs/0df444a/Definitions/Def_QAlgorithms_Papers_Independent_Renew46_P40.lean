-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40
-- name    : QAlgorithms_Papers_Independent_Renew46_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:17:08.278791+00:00
-- url     : https://prove2.me/theorems/cbf33ad4-5f29-4d0e-bbfd-b0db70ae93ad
-- title:
--   Definitions for Optimal Teleportation Based on Bell Measurement
-- statement:
--   The objects the formalized statements of *Optimal Teleportation Based on Bell Measurement* (arXiv:quant-ph/0208015) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QuditMatrix`: Single-register matrices in the computational basis of PDF p.2.
--   - `ResourceMatrix`: Two-register resource operators, Alice's half first (PDF pp.2–3).
--   - `BellLabel`: The n² Bell outcomes (s,t), PDF pp.2–3.
--   - `cyclicShift`: PDF p.2: h|j⟩=|(j+1) mod n⟩, in column action.
--   - `clockRoot`: PDF p.2: omega=exp(-2 pi i/n), with the negative phase.
--   - `negativePhaseClock`: PDF p.2: g|j⟩=omega^j |j⟩.
--   - `bellWeyl`: PDF p.2, Eq.(1): U_st=h^t g^s; the order is part of the definition.
--   - `maximallyEntangledVector`: PDF p.2: the accepted normalized maximally entangled vector on a positive register.
--   - `generalizedBellVector`: PDF p.3, first equality of Eq.(4): (I tensor entrywise-conjugate U_m) Phi. The printed component shorthand uses a different matrix coefficient convention.
--   - `generalizedBellProjector`: PDF p.3: the rank-one Bell projector used by Alice on registers 1,2.
--   - `initialJoint`: PDF p.4, Eq.(9): independent preparation rho tensor chi, reassociated as (1,2),3.
--   - `unnormalizedBellBranch`: PDF pp.3–4: Bob's unnormalized branch after Alice's Bell projection and partial trace. No division by the outcome probability is made, so Born weights are retained.
--   - `IsCorrectionFamily`: PDF p.3: all outcome-dependent corrections are unitary; they do not take the input as data.
--   - `teleportation`: PDF pp.3–4: the operational Bell protocol. Bob applies T_m dagger, as in the proof; all measurement outcomes are summed. This definition does not use Eq.(7).
--   - `resourceBellCoefficient`: PDF p.3: c_ab=⟨Phi_a|chi|Phi_b⟩, with the conjugate-linear argument first.
--   - `bellExpansion`: Corrected Eq.(7), PDF p.3. Only the resource-index Weyl factors are conjugated; the outcome-index factors stay U_m and U_m dagger. This is an expansion to be proved, not the definition of the operational channel.
--   - `entangledOverlap`: PDF p.3, Eq.(5): overlap with (I tensor W)Phi, also used in Eq.(13). For density chi this real part equals the real nonnegative expectation.
--   - `fullyEntangledFraction`: PDF p.3, Eq.(5): fully entangled fraction over all local unitaries, without LOCC. The real supremum is over a nonempty compact unitary group and a continuous overlap; Theorem 3 below states that it is attained, rather than assuming attainment.
--   - `optimalCorrections`: PDF p.6, line before Theorem 3: T_m U_m dagger=W, so T_m=W U_m.
--   - `optimalExpansion`: Corrected Eq.(14), PDF p.6, with the resource-index conjugations forced by Eq.(4).
-- source:
--   Optimal Teleportation Based on Bell Measurement, arXiv:quant-ph/0208015v2, https://arxiv.org/abs/quant-ph/0208015v2

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Renew46.P40

/-- Single-register matrices in the computational basis of PDF p.2. -/
abbrev QuditMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Two-register resource operators, Alice's half first (PDF pp.2–3). -/
abbrev ResourceMatrix (n : ℕ) := Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ

/-- The n² Bell outcomes (s,t), PDF pp.2–3. -/
abbrev BellLabel (n : ℕ) := Fin n × Fin n

/-- PDF p.2: h|j⟩=|(j+1) mod n⟩, in column action. -/
def cyclicShift (n : ℕ) : QuditMatrix n :=
  Matrix.of fun i j => if i.val = (j.val + 1) % n then 1 else 0

/-- PDF p.2: omega=exp(-2 pi i/n), with the negative phase. -/
def clockRoot (n : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) / (n : ℂ))

/-- PDF p.2: g|j⟩=omega^j |j⟩. -/
def negativePhaseClock (n : ℕ) : QuditMatrix n :=
  Matrix.of fun i j => if i = j then clockRoot n ^ j.val else 0

/-- PDF p.2, Eq.(1): U_st=h^t g^s; the order is part of the definition. -/
def bellWeyl {n : ℕ} (m : BellLabel n) : QuditMatrix n :=
  cyclicShift n ^ m.2.val * negativePhaseClock n ^ m.1.val

/-- PDF p.2: the accepted normalized maximally entangled vector on a positive register. -/
def maximallyEntangledVector (n : ℕ) (hn : 0 < n) : EuclideanSpace ℂ (Fin n × Fin n) :=
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  finiteMaxEntangled (Fin n)

/-- PDF p.3, first equality of Eq.(4): (I tensor entrywise-conjugate U_m) Phi.
The printed component shorthand uses a different matrix coefficient convention. -/
def generalizedBellVector (n : ℕ) (hn : 0 < n) (m : BellLabel n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  act (Matrix.kronecker (1 : QuditMatrix n) ((bellWeyl m).map conj)) (maximallyEntangledVector n hn)

/-- PDF p.3: the rank-one Bell projector used by Alice on registers 1,2. -/
def generalizedBellProjector (n : ℕ) (hn : 0 < n) (m : BellLabel n) : ResourceMatrix n :=
  pureDensity (generalizedBellVector n hn m)

/-- PDF p.4, Eq.(9): independent preparation rho tensor chi, reassociated as (1,2),3. -/
def initialJoint {n : ℕ} (rho : QuditMatrix n) (chi : ResourceMatrix n) :
    Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) ℂ :=
  Matrix.of fun p q => rho p.1.1 q.1.1 * chi (p.1.2, p.2) (q.1.2, q.2)

/-- PDF pp.3–4: Bob's unnormalized branch after Alice's Bell projection and partial trace.
No division by the outcome probability is made, so Born weights are retained. -/
def unnormalizedBellBranch {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (m : BellLabel n) (rho : QuditMatrix n) : QuditMatrix n :=
  traceLeft (conjSuperop
    (Matrix.kronecker (generalizedBellProjector n hn m) (1 : QuditMatrix n))
    (initialJoint rho chi))

/-- PDF p.3: all outcome-dependent corrections are unitary; they do not take the input as data. -/
def IsCorrectionFamily {n : ℕ} (T : BellLabel n → QuditMatrix n) : Prop :=
  ∀ m, T m ∈ Matrix.unitaryGroup (Fin n) ℂ

/-- PDF pp.3–4: the operational Bell protocol. Bob applies T_m dagger, as in the proof;
all measurement outcomes are summed. This definition does not use Eq.(7). -/
def teleportation {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (T : BellLabel n → QuditMatrix n) : Superop (Fin n) (Fin n) :=
  fun rho => ∑ m, (T m)ᴴ * unnormalizedBellBranch hn chi m rho * T m

/-- PDF p.3: c_ab=⟨Phi_a|chi|Phi_b⟩, with the conjugate-linear argument first. -/
def resourceBellCoefficient {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (a b : BellLabel n) : ℂ :=
  inner ℂ (generalizedBellVector n hn a) (act chi (generalizedBellVector n hn b))

/-- Corrected Eq.(7), PDF p.3. Only the resource-index Weyl factors are conjugated;
the outcome-index factors stay U_m and U_m dagger. This is an expansion to be proved,
not the definition of the operational channel. -/
def bellExpansion {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (T : BellLabel n → QuditMatrix n) (rho : QuditMatrix n) : QuditMatrix n :=
  ((n : ℂ) ^ 2)⁻¹ •
    ∑ a : BellLabel n, ∑ b : BellLabel n, resourceBellCoefficient hn chi a b •
      ∑ m : BellLabel n,
        (T m)ᴴ * (bellWeyl a).map conj * bellWeyl m * rho *
          (bellWeyl m)ᴴ * ((bellWeyl b).map conj)ᴴ * T m

/-- PDF p.3, Eq.(5): overlap with (I tensor W)Phi, also used in Eq.(13).
For density chi this real part equals the real nonnegative expectation. -/
def entangledOverlap {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (W : QuditMatrix n) : ℝ :=
  effectProb (pureDensity
    (act (Matrix.kronecker (1 : QuditMatrix n) W) (maximallyEntangledVector n hn))) chi

/-- PDF p.3, Eq.(5): fully entangled fraction over all local unitaries, without LOCC.
The real supremum is over a nonempty compact unitary group and a continuous overlap;
Theorem 3 below states that it is attained, rather than assuming attainment. -/
def fullyEntangledFraction {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) : ℝ :=
  sSup (Set.range (fun W : Matrix.unitaryGroup (Fin n) ℂ =>
    entangledOverlap hn chi (W : QuditMatrix n)))

/-- PDF p.6, line before Theorem 3: T_m U_m dagger=W, so T_m=W U_m. -/
def optimalCorrections {n : ℕ} (W : Matrix.unitaryGroup (Fin n) ℂ) :
    BellLabel n → QuditMatrix n :=
  fun m => (W : QuditMatrix n) * bellWeyl m

/-- Corrected Eq.(14), PDF p.6, with the resource-index conjugations forced by Eq.(4). -/
def optimalExpansion {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (W : Matrix.unitaryGroup (Fin n) ℂ) (rho : QuditMatrix n) : QuditMatrix n :=
  ((n : ℂ) ^ 2)⁻¹ •
    ∑ a : BellLabel n, ∑ b : BellLabel n, resourceBellCoefficient hn chi a b •
      ∑ m : BellLabel n,
        (bellWeyl m)ᴴ * (W : QuditMatrix n)ᴴ * (bellWeyl a).map conj * bellWeyl m * rho *
          (bellWeyl m)ᴴ * ((bellWeyl b).map conj)ᴴ * (W : QuditMatrix n) * bellWeyl m

/-- Sanity: the cyclic shift moves the last basis label back to zero (PDF p.2). -/
example : cyclicShift 3 0 2 = 1 := by
  norm_num [cyclicShift]

/-- Sanity: the negativePhaseClock fixes basis label zero (PDF p.2). -/
example : negativePhaseClock 3 0 0 = 1 := by
  simp [negativePhaseClock]

/-- Sanity: U_00 is the identity, independently of dimension (PDF p.3). -/
example (n : ℕ) (hn : 0 < n) : bellWeyl (n := n) (⟨0, hn⟩, ⟨0, hn⟩) = 1 := by
  simp [bellWeyl]

/-- Sanity: the positive singleton register has Phi=1 (PDF p.2). -/
example : maximallyEntangledVector 1 (by decide) (0, 0) = 1 := by
  simp [maximallyEntangledVector, finiteMaxEntangled]

/-- Sanity: independence and register order in Eq.(9), PDF p.4. -/
example {n : ℕ} (rho : QuditMatrix n) (chi : ResourceMatrix n)
    (i j k a b c : Fin n) :
    initialJoint rho chi ((i,j),k) ((a,b),c) = rho i a * chi (j,k) (b,c) := by
  rfl

/-- Sanity: a zero resource gives zero overlap, not a normalized resource (PDF p.3). -/
example (n : ℕ) (hn : 0 < n) (W : QuditMatrix n) :
    entangledOverlap hn (0 : ResourceMatrix n) W = 0 := by
  simp [entangledOverlap, effectProb]

/-- Sanity: zero resource branches carry zero Born weight, without renormalization (PDF p.4). -/
example (n : ℕ) (hn : 0 < n) (m : BellLabel n) (rho : QuditMatrix n) :
    unnormalizedBellBranch hn (0 : ResourceMatrix n) m rho = 0 := by
  ext i j
  simp [unnormalizedBellBranch, initialJoint, conjSuperop, traceLeft, Matrix.mul_apply]

/-- Sanity: in dimension one the complete Bell protocol is the identity (PDF pp.3–6).
This tests the permitted singleton edge, including preparation, measurement, trace and correction. -/
example (rho : QuditMatrix 1) :
    teleportation (by decide : 0 < 1) (1 : ResourceMatrix 1) (fun _ => 1) rho = rho := by
  ext i j
  fin_cases i
  fin_cases j
  simp [teleportation, unnormalizedBellBranch, generalizedBellProjector, generalizedBellVector, maximallyEntangledVector, finiteMaxEntangled,
    bellWeyl, act, Matrix.mulVec, Matrix.kronecker, Matrix.mul_apply,
    initialJoint, traceLeft, pureDensity, conjSuperop, Fintype.sum_prod_type]

end QAlgorithms.Papers.Independent.Renew46.P40


