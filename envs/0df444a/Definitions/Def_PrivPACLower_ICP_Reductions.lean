-- Prove2me | Definitions.Def_PrivPACLower_ICP_Reductions
-- name    : PrivPACLower_ICP_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:05.826504+00:00
-- url     : https://prove2.me/theorems/1228bf0a-846e-4397-a0eb-f6c344294d60
-- title:
--   Hamming distance, resampling, repetition and adaptive block composition
-- statement:
--   For databases of equal length, their Hamming distance is the number of positions with distinct records. Resampling $n$ records with replacement from an $N$-record database $S$ and then applying $M$ has the explicitly computed law
--
--   $$R_M(S)=\frac1{N^n}\sum_{\iota:[n]\to[N]}\mathcal L(M(S\circ\iota)).$$
--
--   Repeating each input record $\ell$ times produces the database indexed by $[\ell]\times[m]$, then flattened to $[\ell m]$. Its learner is $M$ composed with that database map. For adaptive composition on fixed disjoint blocks of lengths $m_i$, stage $i$ is a Markov kernel taking its own block and the full earlier output history. The joint output law is the iterated kernel composition retaining that history.
--
--   These constructions are actual laws used in the privacy conclusions, rather than independent mechanisms constrained by desired properties.
--
--   **Formalization Note** Theorems certify that the displayed finite mixtures and adaptive laws are probability measures. Their definitions as measures need no arbitrary normalization proof parameter. The resampling theorem assumes $n\ge1$ and $N\ge2n$, so its normalizer is nonzero. Adaptive histories are nested heterogeneous products; all block sizes, including zero, are permitted. The unused stages after the last block never enter the output law.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 11, 16, 42–43, Lemmas 3, 4, 9 and 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

noncomputable def hamming {Z : Type*} {n : ℕ} (S S' : Fin n → Z) : ℕ :=
  by classical exact (Finset.univ.filter (fun i => S i ≠ S' i)).card

/-- The resampled law, uniformly averaging over all index maps. -/
noncomputable def resampleLaw {Z O : Type*} [MeasurableSpace O] {n N : ℕ}
    (M : PrivateUniformGen.Characterization.Mechanism Z O n) (S : Fin N → Z) : Measure O :=
  (Fintype.card (Fin n → Fin N) : ℝ≥0∞)⁻¹ •
    ∑ ι : Fin n → Fin N, (M (S ∘ ι) : Measure O)

def repeatDB {Z : Type*} {m : ℕ} (ℓ : ℕ) (S : Fin m → Z) : Fin (ℓ*m) → Z :=
  fun t => S (finProdFinEquiv.symm t).2

noncomputable def repeatedLearner {X : Type*} {m : ℕ} (ℓ : ℕ)
    (M : Learner X (ℓ*m)) : Learner X m := fun S => M (repeatDB ℓ S)

/-- Heterogeneous chronological history; nesting records the order of adaptive outputs. -/
def History (O : ℕ → Type*) : ℕ → Type _
  | 0 => PUnit
  | t+1 => History O t × O t

instance historyMeasurable (O : ℕ → Type*) [∀ t, MeasurableSpace (O t)] :
    (t : ℕ) → MeasurableSpace (History O t)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | t+1 => @Prod.instMeasurableSpace (History O t) (O t) (historyMeasurable O t) inferInstance

/-- Iterated kernel composition; later blocks receive the entire earlier history.
The unused stages t ≥ k are zero and do not enter the final law at t = k. -/
noncomputable def adaptiveLaw {Z : Type*} {k : ℕ} (m : Fin k → ℕ)
    (O : ℕ → Type*) [∀ t, MeasurableSpace (O t)]
    (K : ∀ i : Fin k, (Fin (m i) → Z) → Kernel (History O i.val) (O i.val))
    (d : Fin (∑ i, m i) → Z) : (t : ℕ) → Measure (History O t)
  | 0 => Measure.dirac PUnit.unit
  | t+1 => if ht : t < k then
      (Kernel.id ×ₖ K ⟨t, ht⟩ (fun j => d (finSigmaFinEquiv ⟨⟨t,ht⟩, j⟩))) ∘ₘ
        adaptiveLaw m O K d t
    else 0

end PrivPACLower.ICP


