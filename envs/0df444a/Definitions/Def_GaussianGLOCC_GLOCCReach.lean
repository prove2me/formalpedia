-- Prove2me | Definitions.Def_GaussianGLOCC_GLOCCReach
-- name    : GaussianGLOCC_GLOCCReach
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:40.505983+00:00
-- url     : https://prove2.me/theorems/670da5a6-32ac-44c6-9c23-682fc6f1bf48
-- title:
--   Deterministic Gaussian LOCC (GLOCC) and one-local protocols
-- statement:
--   A state $\rho$ of $n_A+n_B$ modes can be **transformed by GLOCC** into a state $\tau$ if there is a protocol, a finite tree of one-party Gaussian steps by $A$ or $B$ (local Gaussian unitaries, vacuum ancillas, discarding modes, homodyne detections), such that every branch ends exactly at $\tau$. After a homodyne detection with outcome $y\in\mathbb R$ the protocol continues from the conditional state, and the continuation may depend on $y$: this is the classical communication, and both parties' later steps may depend on all earlier outcomes. Because every outcome must lead to $\tau$, the transformation is deterministic. Intermediate states may be mixed and the number of rounds is arbitrary; Gaussian ancillas in any state and heterodyne or general-dyne detections are compositions of these steps.
--
--   A **one-local** protocol (Lemma 3) is one in which $B$ only applies local Gaussian unitaries (which may depend on $A$'s outcomes), while $A$'s steps are unrestricted.
--
--   **Formalization Note** `GLOCCReach` and `OneLocalReach` are inductive relations on bipartite states. Each step requires its input to be a density operator; all steps map densities to densities, so this excludes nothing a protocol can reach. The homodyne constructor takes the conditional states as a function of the outcome.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, pp.1–3 (Gaussian operations, GLOCC), Theorem 1, p.4; Lemma 3, p.5; p.7 first paragraph

import Mathlib
import Definitions.Def_GaussianGLOCC_LocalSteps
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, p.3: a bipartite oscillator state:
party A holds `nA` modes, party B holds `nB` modes, and `rho` is the joint density kernel on the
full `(nA + nB)`-mode Fock space (A = first `nA` modes). -/
structure BiState where
  /-- the number of modes held by A -/
  nA : ℕ
  /-- the number of modes held by B -/
  nB : ℕ
  /-- the joint state -/
  rho : DensityKernel (nA + nB)

/-- arXiv:quant-ph/0301038v1, pp.1–3 and Theorem 1, p.4: `GLOCCReach s t` — the state `s` can be
transformed **deterministically** into the state `t` by Gaussian local operations with
classical communication (GLOCC).

A protocol is a finite tree of one-party steps, each by A or by B:
1. a local Gaussian unitary (beam splitters, phase shifts, squeezers, displacements) on the
   party's current modes;
2. appending a vacuum ancilla mode to the party;
3. discarding (tracing out) the party's last mode;
4. an ideal homodyne detection of the X quadrature of the party's last mode. Every outcome
   `y ∈ ℝ` leads to a conditional state `σ y`, and the protocol continues from `σ y` with steps
   that may depend on `y`. This dependence is the classical communication: both parties' later
   operations may depend on all earlier outcomes.

Every branch must end exactly at `t`, so the transformation succeeds with certainty.
Gaussian ancillas in any state, homodyne detection of any quadrature, and heterodyne or
general-dyne detection are compositions of these steps.

**Formalization Note.** p.2: Gaussian operations "correspond exactly to those operations that
can be implemented by means of optical elements such as beam splitters, phase shifts and
squeezers together with homodyne measurements"; p.3: "The most general “pure” Gaussian operation
can be conceived as a concatenation of Gaussian unitary operations (on possibly a larger set of
modes), together with homodyne measurements"; p.7 realizes the paper's protocol by a Gaussian
unitary, a vacuum ancilla, a homodyne detection and a communicated displacement. Intermediate
states may be mixed and protocols may have any number of rounds. Every step requires its input
to be a density operator; all steps map densities to densities, so this guard excludes nothing
that a protocol can reach. The homodyne constructor takes the conditional states as a function
of the outcome (a nested `∃` is not allowed inside an inductive type); by choice this is the
same as "for every outcome there is a conditional state". -/
inductive GLOCCReach : BiState → BiState → Prop
  | refl (s : BiState) : GLOCCReach s s
  | unitaryA {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ)
      (U : AffineMultimodeGaussianUnitary nA) :
      GLOCCReach ⟨nA, nB, unitaryA U ρ⟩ t → GLOCCReach ⟨nA, nB, ρ⟩ t
  | unitaryB {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ)
      (U : AffineMultimodeGaussianUnitary nB) :
      GLOCCReach ⟨nA, nB, unitaryB U ρ⟩ t → GLOCCReach ⟨nA, nB, ρ⟩ t
  | vacuumA {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ) :
      GLOCCReach ⟨nA + 1, nB, appendVacuumA ρ⟩ t → GLOCCReach ⟨nA, nB, ρ⟩ t
  | vacuumB {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ) :
      GLOCCReach ⟨nA, nB + 1, appendVacuumB ρ⟩ t → GLOCCReach ⟨nA, nB, ρ⟩ t
  | discardA {m nB : ℕ} {ρ : DensityKernel ((m + 1) + nB)} {t : BiState} (hρ : IsDensity ρ) :
      GLOCCReach ⟨m, nB, discardLastA ρ⟩ t → GLOCCReach ⟨m + 1, nB, ρ⟩ t
  | discardB {nA m : ℕ} {ρ : DensityKernel (nA + (m + 1))} {t : BiState} (hρ : IsDensity ρ) :
      GLOCCReach ⟨nA, m, discardLastB ρ⟩ t → GLOCCReach ⟨nA, m + 1, ρ⟩ t
  | homodyneA {m nB : ℕ} {ρ : DensityKernel ((m + 1) + nB)} {t : BiState} (hρ : IsDensity ρ)
      (σ : ℝ → DensityKernel (m + nB)) (hσ : ∀ y, HomodyneLastA ρ y (σ y))
      (next : ∀ y, GLOCCReach ⟨m, nB, σ y⟩ t) : GLOCCReach ⟨m + 1, nB, ρ⟩ t
  | homodyneB {nA m : ℕ} {ρ : DensityKernel (nA + (m + 1))} {t : BiState} (hρ : IsDensity ρ)
      (σ : ℝ → DensityKernel (nA + m)) (hσ : ∀ y, HomodyneLastB ρ y (σ y))
      (next : ∀ y, GLOCCReach ⟨nA, m, σ y⟩ t) : GLOCCReach ⟨nA, m + 1, ρ⟩ t

/-- arXiv:quant-ph/0301038v1, Lemma 3, p.5: transformation "by one-local Gaussian operations
(i.e., Gaussian local operations in system A with communication from system A to B only
together with local Gaussian unitary operations in B)".

The same deterministic protocol trees as `GLOCCReach`, except that B performs only local
Gaussian unitaries: no ancilla, no discarding and no measurement in B. A's steps are
unrestricted. B's unitaries may depend on A's earlier outcomes, which is the one-way
communication from A to B. -/
inductive OneLocalReach : BiState → BiState → Prop
  | refl (s : BiState) : OneLocalReach s s
  | unitaryA {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ)
      (U : AffineMultimodeGaussianUnitary nA) :
      OneLocalReach ⟨nA, nB, unitaryA U ρ⟩ t → OneLocalReach ⟨nA, nB, ρ⟩ t
  | unitaryB {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ)
      (U : AffineMultimodeGaussianUnitary nB) :
      OneLocalReach ⟨nA, nB, unitaryB U ρ⟩ t → OneLocalReach ⟨nA, nB, ρ⟩ t
  | vacuumA {nA nB : ℕ} {ρ : DensityKernel (nA + nB)} {t : BiState} (hρ : IsDensity ρ) :
      OneLocalReach ⟨nA + 1, nB, appendVacuumA ρ⟩ t → OneLocalReach ⟨nA, nB, ρ⟩ t
  | discardA {m nB : ℕ} {ρ : DensityKernel ((m + 1) + nB)} {t : BiState} (hρ : IsDensity ρ) :
      OneLocalReach ⟨m, nB, discardLastA ρ⟩ t → OneLocalReach ⟨m + 1, nB, ρ⟩ t
  | homodyneA {m nB : ℕ} {ρ : DensityKernel ((m + 1) + nB)} {t : BiState} (hρ : IsDensity ρ)
      (σ : ℝ → DensityKernel (m + nB)) (hσ : ∀ y, HomodyneLastA ρ y (σ y))
      (next : ∀ y, OneLocalReach ⟨m, nB, σ y⟩ t) : OneLocalReach ⟨m + 1, nB, ρ⟩ t

end GaussianGLOCC


