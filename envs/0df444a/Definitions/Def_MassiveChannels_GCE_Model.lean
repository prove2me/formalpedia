-- Prove2me | Definitions.Def_MassiveChannels_GCE_Model
-- name    : MassiveChannels_GCE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:52.43302+00:00
-- url     : https://prove2.me/theorems/85c02899-c58b-410e-94c1-b93b08b57ccc
-- title:
--   Grand-canonical state, constraints, capacity values and Fock ensemble
-- statement:
--   Let $\mathcal H$ and $\hat N$ be commuting Hermitian operators on a finite-dimensional complex Hilbert space. At inverse temperature $\beta$ and chemical potential $\mu$, define the grand-canonical state by
--
--   $$\rho_{\mathrm{GCE}}=\frac{\exp[-\beta(\mathcal H-\mu\hat N)]}{\operatorname{tr}\exp[-\beta(\mathcal H-\mu\hat N)]}.$$
--
--   For a finite ensemble $\mathcal E=\{(p_i,\rho_i)\}$ of arbitrary density matrices, its mean is $\bar\rho=\sum_i p_i\rho_i$. The ensemble is admissible at $(E,N)$ exactly when $\operatorname{tr}(\bar\rho\mathcal H)=E$ and $\operatorname{tr}(\bar\rho\hat N)=N$. Its capacity value is its accessible information, maximized over all finite admissible ensembles. A Fock ensemble consists of the pure states of a joint orthonormal eigenbasis of $\mathcal H$ and $\hat N$, weighted by the probabilities assigned by $\rho_{\mathrm{GCE}}$.
--
--   These definitions keep the optimization over mixed input states and arbitrary finite ensembles, as in the paper.
--
--   **Formalization Note** The Hilbert space is finite-dimensional; this represents a finite-level fermionic system and a truncation of the bosonic Fock space. Expectations take the real part of the trace. Accessible information uses the published definition that optimizes over all finite POVMs and measures information in bits.
-- source:
--   Sen(De), Sen, Gromek, Bruß, Lewenstein, Capacities of Quantum Channels for Massive Bosons and Fermions, arXiv:quant-ph/0505028v2, pp. 1–2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Defs_SDP

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- The grand-canonical density matrix at inverse temperature `beta` and chemical potential `mu`. -/
def rhoGCE {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (beta mu : ℝ) : Matrix Q Q ℂ :=
  gibbsState ((-(beta : ℂ)) • (Ham - (mu : ℂ) • Nop))

/-- Expectation of an observable in a state, taking the real trace. -/
def expect {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (A rho : Matrix Q Q ℂ) : ℝ :=
  (rho * A).trace.re

/-- Both average constraints are exact equalities for an arbitrary finite ensemble. -/
def Admissible {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (E N : ℝ) (e : CQData X Q) : Prop :=
  e.Valid ∧ expect Ham (ensembleMean e) = E ∧ expect Nop (ensembleMean e) = N

/-- Accessible-information values of every finite admissible ensemble, including mixed states. -/
def capacityValues {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ) (E N : ℝ) : Set ℝ :=
  {v | ∃ (k : ℕ) (e : CQData (Fin k) Q),
    Admissible Ham Nop E N e ∧ v = accessibleInformation e}

/-- An orthonormal basis whose vectors are eigenvectors of both physical observables. -/
def IsJointEigenbasis {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (Ham Nop : Matrix Q Q ℂ)
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : Prop :=
  ∀ j : Q, ∃ a b : ℝ,
    (∀ i : Q, (∑ k : Q, Ham i k * v j k) = (a : ℂ) * v j i) ∧
    (∀ i : Q, (∑ k : Q, Nop i k * v j k) = (b : ℂ) * v j i)

/-- The ensemble of pure basis states with the Born weights of `rho`. -/
def fockEnsemble {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (rho : Matrix Q Q ℂ)
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : CQData Q Q where
  prob j := effectProb (pureDensity (v j)) rho
  state j := pureDensity (v j)

end MassiveChannels.GCE


