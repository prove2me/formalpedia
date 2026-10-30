-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08
-- name    : QAlgorithms_Papers_Independent_Extend50_P08
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:23:38.918998+00:00
-- url     : https://prove2.me/theorems/df4191c9-3981-4139-bb29-c9d319f130d0
-- title:
--   Definitions for Minimal Port-based Teleportation
-- statement:
--   The objects the formalized statements of *Minimal Port-based Teleportation* (arXiv:2111.05499) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ports`: Computational coordinates of N ports of dimension d (PDF p.3).
--   - `AC`: Alice's N ports and input C, in that order (PDF pp.3–4).
--   - `AliceMatrix`: Alice's resource-filter matrix (PDF p.3, Eq.(1)).
--   - `EffectMatrix`: Effects on Alice and the input (PDF p.3).
--   - `Effects`: Physical outcomes: none is failure, some i names the retained port (PDF p.4).
--   - `liftAlice`: Extend an Alice filter by the identity on C (PDF p.10, Eq.(32)).
--   - `resource`: The physical filtered, normalized Bell resource of Eq.(1), PDF p.3. Normalization is a property of filters with Tr(O†O)=d^N, not imposed by rescaling O.
--   - `IsPhysicalPBT`: Physical PBT data: trace-normalized resource filter and a complete PSD POVM including failure; Bob's retained-port action is fixed by branch below (PDF pp.3–4).
--   - `pulledBackEffect`: Effective effect O† M O; the physical M and effective effect are distinct (PDF p.4, Eq.(6)).
--   - `portBellEffect`: Eq.(3), PDF p.3: identity on all other ports times the normalized Bell projector. The other-port identity does not require the retained coordinates to coincide.
--   - `pbtSignal`: The normalized signal state sigma_i, PDF p.3, Eq.(3).
--   - `pbtSignalSum`: rho has trace N, not one (PDF pp.3,7, Eq.(18)).
--   - `inverseSqrtScalar`: Scalar support inverse square root: zero eigenvalues stay zero (PDF p.4).
--   - `supportInverseSqrt`: Support inverse square root of the particular PBT rho (PDF p.7, Eq.(18)).
--   - `srm`: Uncompleted SRM effect of Eq.(18), PDF p.7.
--   - `srmFailureEffect`: The SRM failure effect Delta, PDF pp.4,7.
--   - `minimalEffects`: Minimal PBT's physical N+1-outcome family, PDF p.7.
--   - `redistribute`: Uniformly redistribute the physical failure effect (PDF p.11, Eq.(39)). The resulting family has a zero failure effect. N>0 is required in uses.
--   - `completedEffects`: Corresponding completed deterministic SRM, with the same resource (PDF pp.4,10).
--   - `retainedPortBranch`: Retain B_i and discard the other B ports after Alice's outcome i (PDF p.3, Eq.(2)). This is the exact coordinate contraction of M with (O tensor I)|Psi+>: the reversed AC indices implement the partial trace. All input off-diagonal blocks are retained, so this acts on entangled inputs.
--   - `successfulMap`: Sum of successful retained-port branches (PDF pp.3–4).
--   - `pbtSuccess`: Average/Choi success, Tr(T(I/d)), not a worst-input success bound (PDF p.4, Eq.(6)).
--   - `conditionalFidelity`: Conditional entanglement fidelity; uses have strictly positive success (PDF p.10, Eq.(35)).
--   - `IsExact`: Exact pPBT means each successful branch is a nonnegative multiple of the identity channel on every matrix, not just on one input (PDF p.4, Eq.(7)).
--   - `IsConvergent`: A physical family converges when its two figures of merit tend to one, on an eventually positive-success domain (PDF p.7, Definition 1).
--   - `irrepDim`: Actual symmetric-group irrep dimension d_lambda (PDF p.5).
--   - `pbtSchurMultiplicity`: Actual Schur–Weyl multiplicity m_lambda, counted by SSYTs (PDF p.5).
--   - `OneBox`: One added box, including the empty predecessor at N=1 (PDF pp.4–5). The size equation is explicit even on the unused N=0 domain.
--   - `teleportationMatrix`: Young-branching incidence Gram matrix on dimension-truncated shapes. Source [23], arXiv:1707.08456, Definition 3 and Theorem 23, PDF pp.7,14; this is the actual matrix referred to on PDF pp.9,20 of the present paper.
--   - `teleportationRayleigh`: Rayleigh quadratic form of the concrete teleportation matrix (source [23] §4).
--   - `IsPrincipal`: Nonnegative unit principal eigenvector, expressed equivalently by maximizing its Rayleigh form over the real unit sphere (PDF pp.9,15,20).
--   - `deterministicFilter`: Deterministic-optimal central filter, using the same vector v throughout (PDF p.9 Eq.(30), p.20 Eq.(A9)).
--   - `probabilisticNormalization`: g(N) of Eq.(A6), PDF p.20; physical-domain positivity is not assumed.
--   - `probabilisticFilter`: Canonical optimal pPBT filter, Eq.(A5), PDF p.20.
--   - `skipPort`: Delete the selected port from the ordered computational coordinates.
--   - `probabilisticCoefficient`: Eq.(A6)'s u_alpha, PDF p.20. Uses N≥1.
--   - `probabilisticEffective`: Canonical EFFECTIVE success effect from Eq.(A5), PDF p.20. The factor 1/d is the normalized Bell projector, with the complementary Young projector embedded on exactly the other N-1 ports.
--   - `probabilisticInverse`: Inverse of the positive, full-support canonical pPBT filter, Eq.(A5). Its invertibility on the physical domain is a consequence of its coefficients.
--   - `probabilisticPhysical`: Physical successful effect obtained by undoing the resource pullback, consistent with Eqs.(6),(7),(A5), PDF pp.4,20.
--   - `probabilisticEffects`: Complete PHYSICAL optimal pPBT POVM, PDF pp.4,20.
--   - `minimalSuccessFormula`: The sum in Theorem 2, Eq.(19), PDF p.7.
--   - `bellDeterministicFormula`: The deterministic Bell-resource numerator (A10), PDF p.20.
--   - `optimizedSuccessFormula`: Principal-vector success evaluation in Theorem 3, Eq.(31), PDF p.10.
--   - `resourceOverlap`: Root fidelity of the two specified filtered pure resources (PDF pp.14–16, Appendix C). These vectors are normalized on the stated domains.
--   - `qubitPrincipal`: Explicit qubit principal vector in shape coordinates, from the positive square root of gamma(j) in Eqs.(55),(59), PDF pp.15–16.
--   - `qubitResourceOverlap`: The overlap for the actual qubit filters, not an independently chosen sum.
--   - `qubitOverlapFormula`: Eq.(56), PDF p.15, reindexed by k=N/2-j, k=0,...,floor(N/2). Subtraction takes place in R; parity is preserved without real factorials.
--   - `unnormalizedBell`: Unnormalized entangled vector of Lemma 12, PDF p.21.
--   - `denseUnnormalized`: Unnormalized remote postmeasurement state; entanglement transfer gives the TRANSPOSE, before using the particular real SRM symmetry (PDF p.17, Eq.(67)).
--   - `denseProbability`: Remote outcome probability, constructed from the state (PDF p.17).
--   - `denseState`: The state on ALL B ports and D conditional on outcome i (PDF p.17, Eq.(68)).
--   - `denseFidelity`: F_{i|k}, Bell effect on B_k D extended by identity on the other B ports (PDF p.17, Eq.(70)).
--   - `denseTransition`: Constructed classical transition coefficients, PDF p.17, Eq.(69).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, https://arxiv.org/abs/2111.05499v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Minimal Port-based Teleportation, arXiv:2111.05499v2.
Paper-local physical constructions. No mixed-tower projector is postulated.
The formulas for branches below are the coordinate contraction of the filtered
Bell resource with Alice's effect, followed by discarding all unretained ports.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Computational coordinates of N ports of dimension d (PDF p.3). -/
abbrev Ports (d N : ℕ) := Fin N → Fin d

/-- Alice's N ports and input C, in that order (PDF pp.3–4). -/
abbrev AC (d N : ℕ) := Ports d N × Fin d

/-- Alice's resource-filter matrix (PDF p.3, Eq.(1)). -/
abbrev AliceMatrix (d N : ℕ) := Matrix (Ports d N) (Ports d N) ℂ

/-- Effects on Alice and the input (PDF p.3). -/
abbrev EffectMatrix (d N : ℕ) := Matrix (AC d N) (AC d N) ℂ

/-- Physical outcomes: none is failure, some i names the retained port (PDF p.4). -/
abbrev Effects (d N : ℕ) := Option (Fin N) → EffectMatrix d N

/-- Extend an Alice filter by the identity on C (PDF p.10, Eq.(32)). -/
def liftAlice {d N : ℕ} (O : AliceMatrix d N) : EffectMatrix d N :=
  Matrix.kronecker O (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The physical filtered, normalized Bell resource of Eq.(1), PDF p.3.
Normalization is a property of filters with Tr(O†O)=d^N, not imposed by rescaling O. -/
def resource {d N : ℕ} (hd : 0 < d) (O : AliceMatrix d N) :
    EuclideanSpace ℂ (Ports d N × Ports d N) :=
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  act (Matrix.kronecker O (1 : AliceMatrix d N)) (finiteMaxEntangled (Ports d N))

/-- Physical PBT data: trace-normalized resource filter and a complete PSD POVM
including failure; Bob's retained-port action is fixed by branch below (PDF pp.3–4). -/
def IsPhysicalPBT {d N : ℕ} (O : AliceMatrix d N) (M : Effects d N) : Prop :=
  0 < N ∧ 2 ≤ d ∧ (Oᴴ * O).trace = (d : ℂ) ^ N ∧ IsPOVM M

/-- Effective effect O† M O; the physical M and effective effect are distinct
(PDF p.4, Eq.(6)). -/
def pulledBackEffect {d N : ℕ} (O : AliceMatrix d N) (M : EffectMatrix d N) : EffectMatrix d N :=
  (liftAlice O)ᴴ * M * liftAlice O

/-- Eq.(3), PDF p.3: identity on all other ports times the normalized Bell projector.
The other-port identity does not require the retained coordinates to coincide. -/
def portBellEffect (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  Matrix.of fun x y =>
    if (∀ j : Fin N, j ≠ i → x.1 j = y.1 j) ∧ x.1 i = x.2 ∧ y.1 i = y.2
    then (d : ℂ)⁻¹ else 0

/-- The normalized signal state sigma_i, PDF p.3, Eq.(3). -/
def pbtSignal (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  (((d : ℝ) ^ (N - 1))⁻¹) • portBellEffect d N i

/-- rho has trace N, not one (PDF pp.3,7, Eq.(18)). -/
def pbtSignalSum (d N : ℕ) : EffectMatrix d N := ∑ i : Fin N, pbtSignal d N i

/-- Scalar support inverse square root: zero eigenvalues stay zero (PDF p.4). -/
def inverseSqrtScalar (x : ℝ) : ℝ := (Real.sqrt x)⁻¹

/-- Support inverse square root of the particular PBT rho (PDF p.7, Eq.(18)). -/
def supportInverseSqrt (d N : ℕ) : EffectMatrix d N :=
  cfc inverseSqrtScalar (pbtSignalSum d N)

/-- Uncompleted SRM effect of Eq.(18), PDF p.7. -/
def srm (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  supportInverseSqrt d N * pbtSignal d N i * supportInverseSqrt d N

/-- The SRM failure effect Delta, PDF pp.4,7. -/
def srmFailureEffect (d N : ℕ) : EffectMatrix d N := 1 - ∑ i : Fin N, srm d N i

/-- Minimal PBT's physical N+1-outcome family, PDF p.7. -/
def minimalEffects (d N : ℕ) : Effects d N
  | none => srmFailureEffect d N
  | some i => srm d N i

/-- Uniformly redistribute the physical failure effect (PDF p.11, Eq.(39)).
The resulting family has a zero failure effect. N>0 is required in uses. -/
def redistribute {d N : ℕ} (M : Effects d N) : Effects d N
  | none => 0
  | some i => M (some i) + ((N : ℝ)⁻¹) • M none

/-- Corresponding completed deterministic SRM, with the same resource
(PDF pp.4,10). -/
def completedEffects (d N : ℕ) : Effects d N := redistribute (minimalEffects d N)

/-- Retain B_i and discard the other B ports after Alice's outcome i
(PDF p.3, Eq.(2)). This is the exact coordinate contraction of M with
(O tensor I)|Psi+>: the reversed AC indices implement the partial trace.
All input off-diagonal blocks are retained, so this acts on entangled inputs. -/
def retainedPortBranch {d N : ℕ} (O : AliceMatrix d N) (M : EffectMatrix d N) (i : Fin N) :
    Superop (Fin d) (Fin d) :=
  fun X => Matrix.of fun b b' =>
    ((d : ℂ) ^ N)⁻¹ *
      ∑ x : Ports d N, ∑ y : Ports d N,
        if x i = b ∧ y i = b' ∧ (∀ j : Fin N, j ≠ i → x j = y j) then
          ∑ c : Fin d, ∑ c' : Fin d, pulledBackEffect O M (y, c') (x, c) * X c c'
        else 0

/-- Sum of successful retained-port branches (PDF pp.3–4). -/
def successfulMap {d N : ℕ} (O : AliceMatrix d N) (M : Effects d N) :
    Superop (Fin d) (Fin d) := fun X => ∑ i : Fin N, retainedPortBranch O (M (some i)) i X

/-- Average/Choi success, Tr(T(I/d)), not a worst-input success bound
(PDF p.4, Eq.(6)). -/
def pbtSuccess {d N : ℕ} (O : AliceMatrix d N) (M : Effects d N) : ℝ :=
  ((successfulMap O M) (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace.re

/-- Conditional entanglement fidelity; uses have strictly positive success
(PDF p.10, Eq.(35)). -/
def conditionalFidelity {d N : ℕ} (hd : 0 < d) (O : AliceMatrix d N) (M : Effects d N) : ℝ :=
  QuditFidelity.entanglementFidelity d hd (successfulMap O M) / pbtSuccess O M

/-- Exact pPBT means each successful branch is a nonnegative multiple of the
identity channel on every matrix, not just on one input (PDF p.4, Eq.(7)). -/
def IsExact {d N : ℕ} (O : AliceMatrix d N) (M : Effects d N) : Prop :=
  ∀ i : Fin N, ∃ p : ℝ, 0 ≤ p ∧ ∀ X : Matrix (Fin d) (Fin d) ℂ,
    retainedPortBranch O (M (some i)) i X = (p : ℂ) • X

/-- A physical family converges when its two figures of merit tend to one,
on an eventually positive-success domain (PDF p.7, Definition 1). -/
def IsConvergent (d : ℕ) (hd : 0 < d) (O : (N : ℕ) → AliceMatrix d N)
    (M : (N : ℕ) → Effects d N) : Prop :=
  (∀ N, 0 < N → IsPhysicalPBT (O N) (M N)) ∧
  (∀ᶠ N in Filter.atTop, 0 < pbtSuccess (O N) (M N)) ∧
  Filter.Tendsto (fun N => pbtSuccess (O N) (M N)) Filter.atTop (nhds 1) ∧
  Filter.Tendsto (fun N => conditionalFidelity hd (O N) (M N)) Filter.atTop (nhds 1)

/-- Actual symmetric-group irrep dimension d_lambda (PDF p.5). -/
def irrepDim {d n : ℕ} (lambda : Schur.Partition d n) : ℝ :=
  Module.finrank ℂ (Schur.spechtSpace lambda)

/-- Actual Schur–Weyl multiplicity m_lambda, counted by SSYTs (PDF p.5). -/
def pbtSchurMultiplicity {d n : ℕ} (lambda : Schur.Partition d n) : ℝ := Schur.schurDimension lambda

/-- One added box, including the empty predecessor at N=1 (PDF pp.4–5).
The size equation is explicit even on the unused N=0 domain. -/
def OneBox {d n m : ℕ} (alpha : Schur.Partition d n) (mu : Schur.Partition d m) : Prop :=
  m = n + 1 ∧ alpha.val.cells ⊆ mu.val.cells

/-- Young-branching incidence Gram matrix on dimension-truncated shapes.
Source [23], arXiv:1707.08456, Definition 3 and Theorem 23, PDF pp.7,14;
this is the actual matrix referred to on PDF pp.9,20 of the present paper. -/
def teleportationMatrix (d N : ℕ) : Matrix (Schur.Partition d N) (Schur.Partition d N) ℝ :=
  Matrix.of fun mu nu => ∑ alpha : Schur.Partition d (N - 1),
    if OneBox alpha mu ∧ OneBox alpha nu then 1 else 0

/-- Rayleigh quadratic form of the concrete teleportation matrix (source [23] §4). -/
def teleportationRayleigh {d N : ℕ} (v : Schur.Partition d N → ℝ) : ℝ :=
  ∑ mu, ∑ nu, v mu * teleportationMatrix d N mu nu * v nu

/-- Nonnegative unit principal eigenvector, expressed equivalently by maximizing
its Rayleigh form over the real unit sphere (PDF pp.9,15,20). -/
def IsPrincipal {d N : ℕ} (v : Schur.Partition d N → ℝ) : Prop :=
  (∀ mu, 0 ≤ v mu) ∧ (∑ mu, (v mu) ^ 2) = 1 ∧
    ∀ w : Schur.Partition d N → ℝ, (∑ mu, (w mu) ^ 2) = 1 →
      teleportationRayleigh w ≤ teleportationRayleigh v

/-- Deterministic-optimal central filter, using the same vector v throughout
(PDF p.9 Eq.(30), p.20 Eq.(A9)). -/
def deterministicFilter {d N : ℕ} (v : Schur.Partition d N → ℝ) : AliceMatrix d N :=
  ∑ mu, ((Real.sqrt ((d : ℝ) ^ N) * v mu /
    Real.sqrt (irrepDim mu * pbtSchurMultiplicity mu) : ℝ) : ℂ) • Schur.isotypicProjector mu

/-- g(N) of Eq.(A6), PDF p.20; physical-domain positivity is not assumed. -/
def probabilisticNormalization (d N : ℕ) : ℝ :=
  (∑ mu : Schur.Partition d N, (pbtSchurMultiplicity mu) ^ 2)⁻¹

/-- Canonical optimal pPBT filter, Eq.(A5), PDF p.20. -/
def probabilisticFilter (d N : ℕ) : AliceMatrix d N :=
  ∑ mu : Schur.Partition d N,
    ((Real.sqrt ((d : ℝ) ^ N) *
      Real.sqrt (probabilisticNormalization d N * pbtSchurMultiplicity mu / irrepDim mu) : ℝ) : ℂ) •
      Schur.isotypicProjector mu

/-- Delete the selected port from the ordered computational coordinates. -/
def skipPort {N : ℕ} (i : Fin N) (j : Fin (N - 1)) : Fin N :=
  ⟨if j.val < i.val then j.val else j.val + 1, by
    have hi := i.isLt
    have hj := j.isLt
    split <;> omega⟩

/-- Eq.(A6)'s u_alpha, PDF p.20. Uses N≥1. -/
def probabilisticCoefficient {d N : ℕ} (alpha : Schur.Partition d (N - 1)) : ℝ :=
  (d : ℝ) ^ (N + 1) * probabilisticNormalization d N * pbtSchurMultiplicity alpha /
    ((N : ℝ) * irrepDim alpha)

/-- Canonical EFFECTIVE success effect from Eq.(A5), PDF p.20.
The factor 1/d is the normalized Bell projector, with the complementary
Young projector embedded on exactly the other N-1 ports. -/
def probabilisticEffective (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  Matrix.of fun x y =>
    ∑ alpha : Schur.Partition d (N - 1),
      ((probabilisticCoefficient (d := d) (N := N) alpha / d : ℝ) : ℂ) *
        Schur.isotypicProjector alpha (fun j => x.1 (skipPort i j))
          (fun j => y.1 (skipPort i j)) *
        (if x.1 i = x.2 ∧ y.1 i = y.2 then 1 else 0)

/-- Inverse of the positive, full-support canonical pPBT filter, Eq.(A5).
Its invertibility on the physical domain is a consequence of its coefficients. -/
def probabilisticInverse (d N : ℕ) : AliceMatrix d N :=
  cfc (fun x : ℝ => x⁻¹) (probabilisticFilter d N)

/-- Physical successful effect obtained by undoing the resource pullback,
consistent with Eqs.(6),(7),(A5), PDF pp.4,20. -/
def probabilisticPhysical (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  liftAlice (probabilisticInverse d N) * probabilisticEffective d N i *
    liftAlice (probabilisticInverse d N)

/-- Complete PHYSICAL optimal pPBT POVM, PDF pp.4,20. -/
def probabilisticEffects (d N : ℕ) : Effects d N
  | none => 1 - ∑ i : Fin N, probabilisticPhysical d N i
  | some i => probabilisticPhysical d N i

/-- The sum in Theorem 2, Eq.(19), PDF p.7. -/
def minimalSuccessFormula (d N : ℕ) : ℝ :=
  (∑ alpha : Schur.Partition d (N - 1), ∑ mu : Schur.Partition d N,
    if OneBox alpha mu then irrepDim mu * pbtSchurMultiplicity alpha else 0) / (d : ℝ) ^ (N + 1)

/-- The deterministic Bell-resource numerator (A10), PDF p.20. -/
def bellDeterministicFormula (d N : ℕ) : ℝ :=
  (∑ alpha : Schur.Partition d (N - 1),
    (∑ mu : Schur.Partition d N,
      if OneBox alpha mu then Real.sqrt (irrepDim mu * pbtSchurMultiplicity mu) else 0) ^ 2) /
    (d : ℝ) ^ (N + 2)

/-- Principal-vector success evaluation in Theorem 3, Eq.(31), PDF p.10. -/
def optimizedSuccessFormula {d N : ℕ} (v : Schur.Partition d N → ℝ) : ℝ :=
  (∑ alpha : Schur.Partition d (N - 1), ∑ mu : Schur.Partition d N,
    if OneBox alpha mu then pbtSchurMultiplicity alpha / pbtSchurMultiplicity mu * (v mu) ^ 2 else 0) / d

/-- Root fidelity of the two specified filtered pure resources
(PDF pp.14–16, Appendix C). These vectors are normalized on the stated domains. -/
def resourceOverlap {d N : ℕ} (hd : 0 < d) (O P : AliceMatrix d N) : ℝ :=
  ‖inner ℂ (resource hd O) (resource hd P)‖

/-- Explicit qubit principal vector in shape coordinates, from the positive
square root of gamma(j) in Eqs.(55),(59), PDF pp.15–16. -/
def qubitPrincipal (N : ℕ) (mu : Schur.Partition 2 N) : ℝ :=
  2 / Real.sqrt (N + 2) *
    Real.sin (Real.pi * ((mu.val.rowLen 0 : ℝ) - (mu.val.rowLen 1 : ℝ) + 1) / (N + 2))

/-- The overlap for the actual qubit filters, not an independently chosen sum. -/
def qubitResourceOverlap (N : ℕ) : ℝ :=
  resourceOverlap (by norm_num : 0 < 2) (probabilisticFilter 2 N)
    (deterministicFilter (qubitPrincipal N))

/-- Eq.(56), PDF p.15, reindexed by k=N/2-j, k=0,...,floor(N/2).
Subtraction takes place in R; parity is preserved without real factorials. -/
def qubitOverlapFormula (N : ℕ) : ℝ :=
  2 / (N + 2) * Real.sqrt (6 / (((N : ℝ) + 1) * (N + 3))) *
    ∑ k ∈ Finset.range (N / 2 + 1),
      ((N : ℝ) - 2 * k + 1) *
        Real.sin (Real.pi * ((N : ℝ) - 2 * k + 1) / (N + 2))

/-- Unnormalized entangled vector of Lemma 12, PDF p.21. -/
def unnormalizedBell (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then 1 else 0

/-- Unnormalized remote postmeasurement state; entanglement transfer gives the
TRANSPOSE, before using the particular real SRM symmetry (PDF p.17, Eq.(67)). -/
def denseUnnormalized (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  (((d : ℝ) ^ (N + 1))⁻¹) • (completedEffects d N (some i))ᵀ

/-- Remote outcome probability, constructed from the state (PDF p.17). -/
def denseProbability (d N : ℕ) (i : Fin N) : ℝ := (denseUnnormalized d N i).trace.re

/-- The state on ALL B ports and D conditional on outcome i (PDF p.17, Eq.(68)). -/
def denseState (d N : ℕ) (i : Fin N) : EffectMatrix d N :=
  (denseProbability d N i)⁻¹ • denseUnnormalized d N i

/-- F_{i|k}, Bell effect on B_k D extended by identity on the other B ports
(PDF p.17, Eq.(70)). -/
def denseFidelity (d N : ℕ) (i k : Fin N) : ℝ :=
  effectProb (portBellEffect d N k) (denseState d N i)

/-- Constructed classical transition coefficients, PDF p.17, Eq.(69). -/
def denseTransition (d N : ℕ) (i k : Fin N) : ℝ :=
  (d : ℝ) ^ 2 * denseProbability d N i * denseFidelity d N i k

/-! Sanity examples pin bad-input defaults and physical register conventions. -/

example : inverseSqrtScalar 0 = 0 ∧ inverseSqrtScalar 1 = 1 := by
  simp [inverseSqrtScalar]

example (d : ℕ) : pbtSignalSum d 0 = 0 := by simp [pbtSignalSum]

example {d N : ℕ} (M : Effects d N) : redistribute M none = 0 := rfl

example (d N : ℕ) : ∑ i : Fin N, srm d N i + srmFailureEffect d N = 1 := by
  unfold srmFailureEffect
  abel

example {d N : ℕ} (O : AliceMatrix d N) (i : Fin N) :
    retainedPortBranch O (0 : EffectMatrix d N) i = fun _ => 0 := by
  funext X
  ext b b'
  simp [retainedPortBranch, pulledBackEffect]

example (b : Fin 2) :
    portBellEffect 2 1 (0 : Fin 1) ((fun _ => b), b) ((fun _ => b), b) = (2 : ℂ)⁻¹ := by
  simp [portBellEffect]

example : unnormalizedBell 2 (0, 1) = 0 ∧ unnormalizedBell 2 (1, 1) = 1 := by
  simp [unnormalizedBell]

end QAlgorithms.Papers.Independent.Extend50.P08


