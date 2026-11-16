-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_Supplement_ensembles
-- name    : RandomOracleUnitarySynthesis_Supplement_ensembles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:36:00.165966+00:00
-- url     : https://prove2.me/theorems/b8b69135-2c27-4c8c-a30f-a5b23c8df56e
-- title:
--   Discrete random-phase ensembles with Haar or Hadamard interleavings
-- statement:
--   For $N=2^n$ and $n$ interleaving matrices $H_1,\ldots,H_n$, independently sample $n+1$ uniformly random functions $f_j:[N]\to\{0,\ldots,N-1\}$. With computational-basis labels identified bijectively with $[N]$, put
--
--   $$F_j=\sum_x e^{2\pi i f_j(x)/N}|x\rangle\langle x|,\qquad U=F_nH_n\cdots F_1H_1F_0.$$
--
--   The measure $\mu_H$ is the push-forward of the uniform law on the finite type of all these function tuples by this product. When the $H_j$ are unitary it is a probability law on unitary matrices. The product Haar law samples $n$ independent interleavings from the published base Haar probability. The Hadamard ensemble uses the published normalized $H^{\otimes n}$ for every interleaving. The Hadamard basis map takes bit zero to false and bit one to true; the separate arbitrary enumeration of phase labels changes no distribution because all phase tables are sampled uniformly.
--
--   These are the concrete ensembles of Sections 5 and 6. The construction always has exactly $n$ interleavings and $n+1$ discrete phase layers, including the scalar case $n=0$.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), §5 construction, printed p. 35 (PDF p. 37); §6 construction, printed p. 41 (PDF p. 43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_designs
import Definitions.Def_PRUMicrocrypt_phaseHadamardU

open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-! The two ensembles, §5 printed p.35 / PDF p.37 and §6 printed p.41 / PDF p.43.
The generic discrete phase matrix and normalized Hadamard are published imports.
We only reindex them and form this paper's n+1-layer distribution. -/

/-- A fixed bijection for the paper's interchangeable labels [N] and {0,1}^n.
The uniform phase-function distribution is invariant under this choice. -/
def basisIndex (n : ℕ) : synthesis_Bits n ≃ Fin (2^n) :=
  Fintype.equivFinOfCardEq (by simp [synthesis_Bits, DirectFidelity.State.Q])

abbrev PhaseTables (n : ℕ) := Fin (n+1) → PRUMicrocrypt.Idx n → Fin (2^n)

/-- The published phase layer, merely reindexed onto the base model's bit basis. -/
def phaseLayer {n : ℕ} (f : PRUMicrocrypt.Idx n → Fin (2^n)) : synthesis_Mat n :=
  (PRUMicrocrypt.phaseLayer n f).submatrix (basisIndex n) (basisIndex n)

/-- Exactly F_n H_n ... F_1 H_1 F_0. The first applied layer is F_0. -/
def phaseProduct {n : ℕ} (H : Fin n → synthesis_Mat n) (f : PhaseTables n) : synthesis_Mat n :=
  (List.finRange n).foldl (fun W j => phaseLayer (f j.succ) * H j * W) (phaseLayer (f 0))

/-- The law of n+1 independent uniform functions to N discrete phases, on matrices.
For unitary H each output is unitary; the design predicate records this support. -/
def phaseEnsemble {n : ℕ} (H : Fin n → synthesis_Mat n) : Measure (synthesis_Mat n) :=
  (PMF.uniformOfFintype (PhaseTables n)).toMeasure.map (phaseProduct H)

/-- The published normalized H^{⊗n}, using 0 ↔ false and 1 ↔ true per bit. -/
def hadamardMatrix (n : ℕ) : synthesis_Mat n :=
  (QAlgorithms.hadamardN n).submatrix
    (fun x i => decide (x i = 1)) (fun x i => decide (x i = 1))

/-- §6's ensemble: every one of the n interleavings is the n-qubit Hadamard. -/
def hadamardEnsemble (n : ℕ) : Measure (synthesis_Mat n) :=
  phaseEnsemble (fun _ : Fin n => hadamardMatrix n)

/-- Independent n-fold product of the BASE Haar probability. -/
def interleavingHaar (n : ℕ) : Measure (Fin n → synthesis_Unitary n) :=
  Measure.pi (fun _ : Fin n => synthesis_haar n)

end RandomOracleUnitarySynthesis.Supplement


