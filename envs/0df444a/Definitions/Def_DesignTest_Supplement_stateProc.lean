-- Prove2me | Definitions.Def_DesignTest_Supplement_stateProc
-- name    : DesignTest_Supplement_stateProc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:53.918494+00:00
-- url     : https://prove2.me/theorems/0b244ac9-ae55-46e2-ab3e-b8281f7271a5
-- title:
--   Non-adaptive incoherent and per-sample coherent state-preparation procedures
-- statement:
--   In the state-preparation access model, $m$ pure states $\psi_1,\dots,\psi_m$ are sampled and each can be queried $q$ times, each query producing a copy of $|\psi_i\rangle\langle\psi_i|$.
--
--   1. A **non-adaptive incoherent** procedure measures every copy $k$ of sample $i$ on its own with a POVM $\{E_{i,k,o}\}_o$ on $\mathbb C^d$ fixed in advance; the transcript probability is $\prod_{i,k}\langle\psi_i|E_{i,k,o_{ik}}|\psi_i\rangle$.
--   2. A **per-sample coherent** procedure measures the $q$ copies of sample $i$ jointly with a POVM $\{E_{i,o}\}_o$ on $(\mathbb C^d)^{\otimes q}$ fixed in advance, with transcript probability $\prod_i\mathrm{Tr}[E_{i,o_i}(|\psi_i\rangle\langle\psi_i|)^{\otimes q}]$; outcomes of different samples are combined classically.
--
--   They are the incoherent tester of Theorem 4.4 and the tester class of Theorem 4.5.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.1, 3.3, 3.5, 3.6, pp.14–15; Theorem 4.5, p.32

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_Supplement_PState
import Definitions.Def_DesignTest_Supplement_RandProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory
open scoped ComplexOrder

/-- **A deterministic non-adaptive incoherent procedure in the state-preparation access model**, `q`
copies of each of `m` sampled states (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary
Designs*, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.1, 3.3, 3.5, 3.6, pp.14–15): copy `k` of
sample `i` is measured on its own, with a POVM `{E i k o}_{o ∈ Fin K}` fixed in advance, and discarded.

**Formalization Note.** A measurement of one copy with freshly initialized ancillas is a POVM on `ℂ^d`.
Initial randomness and classical post-processing are supplied by `RandProc`. -/
structure SNAI (d m q K : ℕ) where
  /-- the POVM applied to copy `k` of sample `i` -/
  E : Fin m → Fin q → Fin K → Matrix (Fin d) (Fin d) ℂ
  /-- effects are positive semidefinite -/
  psd : ∀ i k o, (E i k o).PosSemidef
  /-- effects sum to the identity -/
  sum_one : ∀ i k, ∑ o, E i k o = 1

/-- Transcript probability `∏_{i,k} ⟨ψ_i|E_{i,k,o_{ik}}|ψ_i⟩` of a non-adaptive incoherent state
procedure. -/
noncomputable def SNAI.prob {d m q K : ℕ} (A : SNAI d m q K) (ψ : Fin m → DesignTest.PureVec d)
    (o : Fin m → Fin q → Fin K) : ℝ :=
  ∏ i, ∏ k, (Matrix.trace (A.E i k (o i k) * projOf (ψ i))).re

/-- Randomized non-adaptive incoherent state procedures with `m` samples and `q` copies per sample. -/
abbrev SNAIProc (d m q K : ℕ) :=
  RandProc (DesignTest.PureVec d) m (SNAI d m q K) (Fin m → Fin q → Fin K) SNAI.prob

/-- **A deterministic non-adaptive coherent state procedure whose measurements act jointly only on the
copies of one sampled process** (STOC 2027 submission (sha256 e2f0a429…), Theorem 4.5, p.32;
Definitions 3.3, 3.6, p.15): the `q` copies `(|ψ_i⟩⟨ψ_i|)^{⊗q}` of sample `i` are measured by a joint POVM
`{E i o}_{o ∈ Fin K}` on `(ℂ^d)^{⊗q}` fixed in advance; the outcomes of different samples are combined
classically (by `RandProc.out`). -/
structure SPerSample (d m q K : ℕ) where
  /-- the joint POVM on the `q` copies of sample `i` -/
  E : Fin m → Fin K → Matrix (Fin q → Fin d) (Fin q → Fin d) ℂ
  /-- effects are positive semidefinite -/
  psd : ∀ i o, (E i o).PosSemidef
  /-- effects sum to the identity -/
  sum_one : ∀ i, ∑ o, E i o = 1

/-- Transcript probability `∏_i Tr[E_{i,o_i} (|ψ_i⟩⟨ψ_i|)^{⊗q}]`. -/
noncomputable def SPerSample.prob {d m q K : ℕ} (A : SPerSample d m q K)
    (ψ : Fin m → DesignTest.PureVec d) (o : Fin m → Fin K) : ℝ :=
  ∏ i, (Matrix.trace (A.E i (o i) * DesignTest.tensorPow (ψ i) q)).re

/-- Randomized per-sample coherent state procedures with `m` samples and `q` copies per sample. -/
abbrev SPerSampleProc (d m q K : ℕ) :=
  RandProc (DesignTest.PureVec d) m (SPerSample d m q K) (Fin m → Fin K) SPerSample.prob

end DesignTest.Supplement


