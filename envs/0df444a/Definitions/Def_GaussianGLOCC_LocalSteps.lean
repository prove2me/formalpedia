-- Prove2me | Definitions.Def_GaussianGLOCC_LocalSteps
-- name    : GaussianGLOCC_LocalSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:53.005992+00:00
-- url     : https://prove2.me/theorems/3b3564dc-eb32-4831-b791-ea22f910b3d2
-- title:
--   One-party Gaussian steps: local unitaries, vacuum ancillas, discarding, homodyne detection
-- statement:
--   A bipartite state of $n_A+n_B$ modes is a density operator on the full Fock space; $A$ holds the first $n_A$ modes and $B$ the last $n_B$. The elementary Gaussian steps a party can take are:
--
--   1. a **local Gaussian unitary** $\rho\mapsto(U\otimes\mathbb 1)\rho(U\otimes\mathbb 1)^\dagger$, $U$ any Gaussian unitary on the party's modes (beam splitters, phase shifts, squeezers, displacements);
--   2. **appending a vacuum mode** $\rho\mapsto\rho\otimes|0\rangle\langle 0|$ to the party;
--   3. **discarding** the party's last mode (partial trace);
--   4. an ideal **homodyne detection** of the $X$ quadrature of the party's last mode with real outcome $y$: the conditional state of the remaining modes is the trace-norm limit, as $d\to 0^+$, of the normalized states obtained by projecting the measured mode onto the pure squeezed state with CM $\operatorname{diag}(d^2,d^{-2})$ centred at $X=y$.
--
--   $B$'s steps are $A$'s steps with the two parties exchanged. These are the operations of p.2 ("beam splitters, phase shifts and squeezers together with homodyne measurements") and p.3 ("a concatenation of Gaussian unitary operations (on possibly a larger set of modes), together with homodyne measurements").
--
--   **Formalization Note** Every step acts on Fock coefficients of actual density operators; no step is defined by its effect on covariance matrices. Gaussian unitaries are the published `Renew46.P39.AffineMultimodeGaussianUnitary`, and the homodyne limit follows the published `Renew46.P39.HomodyneOutcome` construction (one mode, $X$ quadrature), with every series and every positive weight required explicitly. Other quadratures are measured after a phase-shift unitary.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, pp.2–3 (Gaussian operations), p.7 first paragraph (vacuum ancilla, homodyne detection, displacement)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
open Filter
open scoped Topology ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity traceSize rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Frontier30.P14 (unitaryCoeff conjugateKernel)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

namespace GaussianGLOCC

/-! # One-party Gaussian steps on a bipartite oscillator state

Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, pp.2–3 and p.7: Gaussian operations
"correspond exactly to those operations that can be implemented by means of optical elements
such as beam splitters, phase shifts and squeezers together with homodyne measurements" (p.2);
"The most general “pure” Gaussian operation can be conceived as a concatenation of Gaussian
unitary operations (on possibly a larger set of modes), together with homodyne measurements"
(p.3). A bipartite state of `nA + nB` modes is a density kernel on the full Fock space with
basis labels `FockIndex (nA + nB)`; system A is the first `nA` modes, B the last `nB`. Every
step below acts on actual density kernels; none is defined by its effect on covariance
matrices. B's steps are A's steps conjugated by the party swap. -/

/-- arXiv:quant-ph/0301038v1, p.3: the A part (first `nA` modes) of a bipartite Fock label. -/
def splitA {nA nB : ℕ} (i : FockIndex (nA + nB)) : FockIndex nA :=
  fun k => i (Fin.castAdd nB k)

/-- arXiv:quant-ph/0301038v1, p.3: the B part (last `nB` modes) of a bipartite Fock label. -/
def splitB {nA nB : ℕ} (i : FockIndex (nA + nB)) : FockIndex nB :=
  fun k => i (Fin.natAdd nA k)

/-- arXiv:quant-ph/0301038v1, p.3: the bipartite Fock label with A part `a` and B part `b`. -/
def joinAB {nA nB : ℕ} (a : FockIndex nA) (b : FockIndex nB) : FockIndex (nA + nB) :=
  Fin.append a b

/-- arXiv:quant-ph/0301038v1, p.3: relabel a `(nB + nA)`-mode label as an `(nA + nB)`-mode
label by exchanging the two parties' blocks of modes. -/
def swapIdx {nA nB : ℕ} (i : FockIndex (nB + nA)) : FockIndex (nA + nB) :=
  joinAB (splitB i) (splitA i)

/-- arXiv:quant-ph/0301038v1, p.3: the same bipartite state with the roles of A and B
exchanged (B's modes first). Used to define B's local steps from A's. -/
def swapAB {nA nB : ℕ} (ρ : DensityKernel (nA + nB)) : DensityKernel (nB + nA) :=
  fun i j => ρ (swapIdx i) (swapIdx j)

/-- arXiv:quant-ph/0301038v1, p.3, eq. (5): the Fock coefficients of `U ⊗ 𝟙_B` for a bounded
Gaussian unitary `U` on A's `nA` modes. -/
noncomputable def localUnitaryKernelA {nA nB : ℕ} (U : AffineMultimodeGaussianUnitary nA) :
    DensityKernel (nA + nB) :=
  fun i j => unitaryCoeff U.unitary (splitA i) (splitA j) * if splitB i = splitB j then 1 else 0

/-- arXiv:quant-ph/0301038v1, pp.2–3: a local Gaussian unitary of party A,
`ρ ↦ (U ⊗ 𝟙_B) ρ (U ⊗ 𝟙_B)†`, on Fock coefficients.

**Formalization Note.** `U` is the published `AffineMultimodeGaussianUnitary nA` of
`QAlgorithms.Papers.Independent.Renew46.P39`: a unitary on the full `nA`-mode Fock space with a
symplectic matrix and a phase-space displacement, fixed by its Weyl action. Beam splitters,
phase shifts, squeezers and displacements on A's modes are all of this form. The coefficient
series converge absolutely for a density `ρ` (bounded `U`, trace-class `ρ`). -/
noncomputable def unitaryA {nA nB : ℕ} (U : AffineMultimodeGaussianUnitary nA) (ρ : DensityKernel (nA + nB)) :
    DensityKernel (nA + nB) :=
  conjugateKernel (localUnitaryKernelA U) ρ

/-- arXiv:quant-ph/0301038v1, pp.2–3: a local Gaussian unitary of party B,
`ρ ↦ (𝟙_A ⊗ U) ρ (𝟙_A ⊗ U)†` (A's step conjugated by the party swap). -/
noncomputable def unitaryB {nA nB : ℕ} (U : AffineMultimodeGaussianUnitary nB) (ρ : DensityKernel (nA + nB)) :
    DensityKernel (nA + nB) :=
  swapAB (unitaryA U (swapAB ρ))

/-- The occupation of A's last mode in an `((m + 1) + nB)`-mode label. -/
def lastA {m nB : ℕ} (i : FockIndex ((m + 1) + nB)) : ℕ :=
  splitA i (Fin.last m)

/-- The `(m + nB)`-mode label obtained by deleting A's last mode. -/
def dropLastA {m nB : ℕ} (i : FockIndex ((m + 1) + nB)) : FockIndex (m + nB) :=
  joinAB (Fin.init (splitA i)) (splitB i)

/-- The `((m + 1) + nB)`-mode label obtained by inserting occupation `t` as A's last mode. -/
def insertLastA {m nB : ℕ} (i : FockIndex (m + nB)) (t : ℕ) : FockIndex ((m + 1) + nB) :=
  joinAB (Fin.snoc (α := fun _ => ℕ) (splitA i) t) (splitB i)

/-- arXiv:quant-ph/0301038v1, p.7 ("an additional vacuum field mode") and p.3 ("Gaussian
unitary operations (on possibly a larger set of modes)"): party A appends a fresh mode in the
vacuum, `ρ ↦ ρ ⊗ |0⟩⟨0|`, as A's new last mode. -/
def appendVacuumA {nA nB : ℕ} (ρ : DensityKernel (nA + nB)) : DensityKernel ((nA + 1) + nB) :=
  fun i j => if lastA i = 0 ∧ lastA j = 0 then ρ (dropLastA i) (dropLastA j) else 0

/-- arXiv:quant-ph/0301038v1, pp.3, 7: party B appends a vacuum mode as B's new last mode. -/
def appendVacuumB {nA nB : ℕ} (ρ : DensityKernel (nA + nB)) : DensityKernel (nA + (nB + 1)) :=
  swapAB (appendVacuumA (swapAB ρ))

/-- arXiv:quant-ph/0301038v1, pp.2–3: party A discards its last mode (partial trace over it),
`ρ ↦ Tr_{A,last} ρ`.

**Formalization Note.** For a density `ρ` the series converges absolutely
(`|ρ_{(i,t),(j,t)}| ≤ (ρ_{(i,t),(i,t)} + ρ_{(j,t),(j,t)})/2`); the protocol relation
`GLOCCReach` only applies this step to densities. -/
noncomputable def discardLastA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB)) : DensityKernel (m + nB) :=
  fun i j => ∑' t : ℕ, ρ (insertLastA i t) (insertLastA j t)

/-- arXiv:quant-ph/0301038v1, pp.2–3: party B discards its last mode. -/
noncomputable def discardLastB {nA m : ℕ} (ρ : DensityKernel (nA + (m + 1))) : DensityKernel (nA + m) :=
  swapAB (discardLastA (swapAB ρ))

/-- arXiv:quant-ph/0301038v1, p.3 and p.7: the covariance matrix `diag(d², d⁻²)` of the pure
single-mode squeezed seed used to approximate an ideal X-homodyne detection as `d → 0⁺`. -/
noncomputable def xSeedCovariance (d : ℝ) : Cov 1 :=
  Matrix.diagonal (fun i => if i.2 = 0 then d ^ 2 else d⁻¹ ^ 2)

/-- The pure single-mode Gaussian seed with CM `diag(d², d⁻²)`, X-mean `y` and P-mean `0`:
a normalized pure state on the full one-mode Fock space, characterized by its characteristic
function (the published `Renew46.P39.SeedAt` pattern, for one mode and the X quadrature). -/
def XSeedAt (d y : ℝ) (seed : DensityKernel 1) : Prop :=
  GaussianWithCovariance seed (xSeedCovariance d) ∧
    (∃ ψ : Hilbert (FockIndex 1), ‖ψ‖ = 1 ∧ seed = rankOne ψ) ∧
    ∀ v, CharacteristicSummable seed v ∧
      multimodeWeylTrace seed v =
        covarianceCharacteristicValue (xSeedCovariance d) (fun i => if i.2 = 0 then y else 0) v

/-- The unnormalized post-measurement kernel `⟨φ| ρ |φ⟩` on A's last mode, for
`seed = |φ⟩⟨φ|`: `Σ_{u,v} ρ_{(i,u),(j,v)} φ̄_u φ_v`. -/
noncomputable def homodyneProjectedA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB)) (seed : DensityKernel 1) :
    DensityKernel (m + nB) :=
  fun i j => ∑' u : ℕ, ∑' v : ℕ,
    ρ (insertLastA i u) (insertLastA j v) * seed (fun _ => v) (fun _ => u)

/-- Convergence of every series in `homodyneProjectedA` and of its trace (so no `tsum`
defaults to `0`). -/
def HomodyneSummableA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB)) (seed : DensityKernel 1) :
    Prop :=
  (∀ i j u, Summable (fun v : ℕ =>
    ρ (insertLastA i u) (insertLastA j v) * seed (fun _ => v) (fun _ => u))) ∧
  (∀ i j, Summable (fun u : ℕ => ∑' v : ℕ,
    ρ (insertLastA i u) (insertLastA j v) * seed (fun _ => v) (fun _ => u))) ∧
  Summable (fun i => (homodyneProjectedA ρ seed i i).re)

/-- The trace (probability weight) of the projected kernel. -/
noncomputable def homodyneWeightA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB))
    (seed : DensityKernel 1) : ℝ :=
  ∑' i, (homodyneProjectedA ρ seed i i).re

/-- The normalized post-measurement state, used only where the weight is positive. -/
noncomputable def homodyneOutputA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB))
    (seed : DensityKernel 1) : DensityKernel (m + nB) :=
  ((homodyneWeightA ρ seed : ℂ)⁻¹) • homodyneProjectedA ρ seed

/-- arXiv:quant-ph/0301038v1, p.3 ("homodyne measurements") and p.7 ("one realizes a homodyne
detection in the additional field mode"): `σ` is the state of the remaining modes after an
ideal homodyne detection of the X quadrature of A's last mode with outcome `y ∈ ℝ`.

It is the trace-norm limit, as `d → 0⁺`, of the normalized states obtained by projecting A's
last mode onto the pure squeezed seed with CM `diag(d², d⁻²)` centered at X-value `y`; every
series converges and every weight is positive along the way.

**Formalization Note.** This is the published `Renew46.P39.HomodyneOutcome` construction for one
measured mode and the X quadrature; the measured mode is removed. Homodyne detection of any
other quadrature is a phase-shift unitary followed by this step. No covariance formula for the
conditional state is assumed. -/
def HomodyneLastA {m nB : ℕ} (ρ : DensityKernel ((m + 1) + nB)) (y : ℝ)
    (σ : DensityKernel (m + nB)) : Prop :=
  IsDensity σ ∧ ∃ seeds : ℝ → DensityKernel 1,
    (∀ d, 0 < d → XSeedAt d y (seeds d) ∧ HomodyneSummableA ρ (seeds d) ∧
      0 < homodyneWeightA ρ (seeds d)) ∧
    Tendsto (fun d => traceSize (homodyneOutputA ρ (seeds d) - σ)) (𝓝[>] 0) (𝓝 0)

/-- arXiv:quant-ph/0301038v1, pp.3, 7: ideal X-homodyne detection of B's last mode with
outcome `y` (A's step conjugated by the party swap). -/
def HomodyneLastB {nA m : ℕ} (ρ : DensityKernel (nA + (m + 1))) (y : ℝ)
    (σ : DensityKernel (nA + m)) : Prop :=
  HomodyneLastA (swapAB ρ) y (swapAB σ)

end GaussianGLOCC


