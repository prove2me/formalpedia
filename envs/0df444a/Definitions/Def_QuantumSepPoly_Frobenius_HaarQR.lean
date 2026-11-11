-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_HaarQR
-- name    : QuantumSepPoly_Frobenius_HaarQR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:57.199836+00:00
-- url     : https://prove2.me/theorems/146606a3-32ca-47b7-9461-882295c2882f
-- title:
--   Gaussian QR and the Haar sampling law
-- statement:
--   Apply Gram–Schmidt to successive columns of a complex Gaussian matrix, subtracting their orthogonal projections and normalizing each residual by its positive Euclidean norm. The resulting triangular diagonal is nonnegative real, which fixes the QR phases. If any pivot is zero, return the identity matrix. Define Haar measure as the pushforward of the Gaussian matrix law through this actual map.
--   $$H_{ab}=u_bu_a^*-\delta_{ab}I/d,\qquad \|A\|_F^2=\sum_{i,j}\|A(E_{ij})\|_H^2.$$
--   A separate target asserts measurability, normalized Haar invariance, and polynomial-time implementation; none is a structure field or an axiom.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Gaussian
import Definitions.Def_QuantumSepPoly_Frobenius_PartialTraces

noncomputable section

namespace QuantumSepPoly.Frobenius
open MeasureTheory ProbabilityTheory

instance opMeasurable (d : ℕ) : MeasurableSpace (Op d) := inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℂ))
instance opBorel (d : ℕ) : BorelSpace (Op d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℂ))

/-- §2.3, p.8: Gaussian QR with positive real diagonal of R (phase normalization).
Singular pivots cause the entire output to be the identity. -/
def qrColumns {d : ℕ} (G : Op d) : List (Vec d) :=
  (List.finRange d).foldl (fun qs j =>
    let g : Vec d := fun i => G i j
    let v : Vec d := fun i => g i - (qs.map (fun q =>
      (∑ a, star (q a) * g a) * q i)).sum
    let q : Vec d := if vecSq v = 0 then 0 else fun i => v i / (vecNorm v : ℂ)
    qs ++ [q]) []

def haarQR {d : ℕ} (G : Op d) : Op d := by
  classical
  let qs := qrColumns G
  exact if ∃ q ∈ qs, vecSq q = 0 then 1 else fun i j => (qs[j.val]?.getD 0) i

def gaussianMatrix (d : ℕ) : Measure ((Fin d × Fin d × Bool) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def gaussianMatrixValue {d : ℕ} (g : (Fin d × Fin d × Bool) → ℝ) : Op d :=
  fun i j => ((g (i,j,false) : ℂ) + Complex.I * g (i,j,true)) / (Real.sqrt 2 : ℂ)

/-- The actual sampling map, not an assumed output law or a free Haar instruction. -/
def sampledUnitary {d : ℕ} (g : (Fin d × Fin d × Bool) → ℝ) : Op d :=
  haarQR (gaussianMatrixValue g)

def haar (d : ℕ) : Measure (Op d) := (gaussianMatrix d).map sampledUnitary

def Hentry (d : ℕ) (a b : Fin d) : Op d :=
  fun i j => (if i = b ∧ j = a then 1 else 0) -
    (if a = b ∧ i = j then 1 / (d : ℂ) else 0)

/-- Hilbert–Schmidt norm of a linear map, computed on matrix units. -/
def linearFrob {d : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : Op d →ₗ[ℂ] H) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A (Matrix.single i j 1)‖^2)

end QuantumSepPoly.Frobenius


