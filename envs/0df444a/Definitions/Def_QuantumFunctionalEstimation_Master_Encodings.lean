-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Encodings
-- name    : QuantumFunctionalEstimation_Master_Encodings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:28:36.059445+00:00
-- url     : https://prove2.me/theorems/50be85d1-5caf-4dc9-9f60-fe51c67f440e
-- title:
--   Haar directions and the one- and multi-direction sampling laws
-- statement:
--   Let $U$ have normalized Haar probability on the complex unitary group $U(d)$. Its first column has the Haar unit-vector law, and the projector associated with a vector $u$ is $P_u=uu^*$. For $D\ge2$ and $-1\le z\le D-1$, define
--   $$\varsigma_{z,u}=\frac{1+z}{D}P_u+\frac{1-z/(D-1)}{D}(I-P_u).$$
--   For a real probability law $\mu$, the one-direction average is the integral of $\varsigma_{Z,u}^{\otimes n}$ against the product of $\mu$ and the Haar direction law.
--
--   For the multi-direction law, draw independent scalars $X_1,\ldots,X_q$ with law $\mu$, independently of $U$, and take the first $q$ columns $u_i$. Put $S=\sum_iX_i$ and $r=d-q$. The sampled matrix is
--   $$\rho=\frac1d\sum_{i=1}^qX_iP_{u_i}+\frac{d-S}{rd}\left(I-\sum_{i=1}^qP_{u_i}\right)\quad(S\le d/2),$$
--   and $\rho=I/d$ otherwise. Its law on the density-matrix subtype is denoted $\operatorname{multiPrior}(d,q,\mu)$.
--
--   These definitions fix the exact random objects of the two encoding lemmas. Basis columns are jointly orthonormal, whereas the two vectors in the overlap lemma are sampled independently.
--
--   **Formalization Note** The state law is the matrix pushforward pulled back along the density-matrix embedding. It is not normalized artificially; under the source hypotheses it has total mass one, as the milestone explicitly concludes. Sampling $d$ scalars and ignoring those after $q$ gives exactly the source law.
--
--   Differences from the source:
--   - encoding: q iid scalars and a Haar basis → d iid coordinates with only the first q used and a single Haar unitary; reason: unused independent coordinates leave the pushforward unchanged
--   - encoding: probability law of sampled states → matrix pushforward followed by comap along the state embedding; reason: under the source support and dimension conditions every sampled matrix is a state; probability is to be proved, not assumed
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Definition 3.1, printed p. 14 (PDF p. 16); Definition 3.3, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Model
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace QuantumFunctionalEstimation.Master

/-- Probability Haar on the actual compact complex unitary group. -/
local instance haarProbability (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨QAlgorithms.Schur.unitaryHaar.eq_1 d ▸ Measure.haarMeasure_self⟩

/-- The first column, for positive dimension; its Haar pushforward is the uniform unit direction. -/
def haarDirection (d : ℕ) (hd : 0 < d) : Measure (Fin d → ℂ) :=
  Measure.map (fun U : Matrix.unitaryGroup (Fin d) ℂ => fun i => (U : Matrix (Fin d) (Fin d) ℂ) i ⟨0, hd⟩)
    (QAlgorithms.Schur.unitaryHaar d)

/-- Rank-one projector, entry by entry. -/
def projector {d : ℕ} (u : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => u i * star (u j)

/-- Definition 3.1. Used with D >= 2 and -1 <= z <= D-1. -/
def oneDirection (D : ℕ) (z : ℝ) (u : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (((1 + z) / D : ℝ) : ℂ) • projector u +
    (((1 - z / (D - 1 : ℝ)) / D : ℝ) : ℂ) • (1 - projector u)

/-- Independent Z and Haar direction, integrated AFTER taking the tensor power. -/
def oneAverage (D : ℕ) (hD : 0 < D) (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    Matrix (Fin n → Fin D) (Fin n → Fin D) ℂ :=
  ∫ t, QAlgorithms.piKron n (oneDirection D t.1 t.2)
    ∂((μ : Measure ℝ).prod (haarDirection D hD))

/-- First q columns; q is at most d in every source use. -/
def selected (d q : ℕ) : Finset (Fin d) := Finset.univ.filter (fun i => i.val < q)

/-- Definition 3.3, including its maximally mixed fallback. Unused iid coordinates do not affect the law. -/
def multiMatrix (d q : ℕ) (X : Fin d → ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let S := ∑ i ∈ selected d q, X i
  let P := ∑ j ∈ selected d q, projector (fun i => (U : Matrix (Fin d) (Fin d) ℂ) i j)
  if S ≤ (d : ℝ) / 2 then
    ((1 / d : ℝ) : ℂ) • (∑ j ∈ selected d q,
      (X j : ℂ) • projector (fun i => (U : Matrix (Fin d) (Fin d) ℂ) i j)) +
      (((d - S) / ((d - q : ℕ) * d) : ℝ) : ℂ) • (1 - P)
  else ((1 / d : ℝ) : ℂ) • 1

/-- Definition 3.3 as a pushforward, restricted along the actual state-space embedding.
For the source parameters the raw law is carried by states, so comap loses no mass.
Probability of this constructed measure is a conclusion, never an assumption. -/
def multiPrior (d q : ℕ) (μ : ProbabilityMeasure ℝ) : Measure (State d) :=
  (Measure.map (fun t : (Fin d → ℝ) × Matrix.unitaryGroup (Fin d) ℂ => multiMatrix d q t.1 t.2)
    ((Measure.pi (fun _ : Fin d => (μ : Measure ℝ))).prod (QAlgorithms.Schur.unitaryHaar d))).comap
      (Subtype.val : State d → Matrix (Fin d) (Fin d) ℂ)

end QuantumFunctionalEstimation.Master


