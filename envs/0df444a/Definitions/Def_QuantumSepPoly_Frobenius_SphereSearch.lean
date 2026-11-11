-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_SphereSearch
-- name    : QuantumSepPoly_Frobenius_SphereSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:13.660044+00:00
-- url     : https://prove2.me/theorems/056f8a79-ce4a-414f-b1ef-6785b57ed54b
-- title:
--   Finite search for bounded dimensions
-- statement:
--   For the bounded-dimension branch of Theorem 5.7, enumerate coordinate vectors in a finite disk grid with mesh
--   $$\min\{1/4,\tau/(32\sqrt d)\}.$$
--   Normalize each vector, with the fixed basis-vector replacement at zero. Enumerate all pairs and retain the largest explicitly evaluated product objective using comparisons. This is a finite search, not a supplied maximizer. Exponential dependence on the accuracy-dependent dimension cutoff is allowed; the main theorem still requires a program polynomial in dimension at every fixed accuracy.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 21 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DiskNet

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- Explicit finite coordinate enumeration, used only below the fixed-accuracy
dimension cutoff in Theorem 5.7. It is not a free maximizer. -/
def coordinateVectors (E : List ℂ) : (d : ℕ) → List (Vec d)
  | 0 => [Fin.elim0]
  | d+1 => E.flatMap fun x => (coordinateVectors E d).map fun y => Fin.cons x y

def sphereSearchCandidates (d : ℕ) (τ : ℝ) : List (Vec d) :=
  (coordinateVectors (diskGrid 1 (min (1/4) (τ / (32*Real.sqrt (d:ℝ))))) d).map normalize

def sphereSearch {d : ℕ} (τ : ℝ) (M : Bip d) : Vec d × Vec d :=
  ((sphereSearchCandidates d τ).product (sphereSearchCandidates d τ)).foldl
    (fun best candidate => if productValue M candidate.1 candidate.2 > productValue M best.1 best.2
      then candidate else best) (firstVector d, firstVector d)

end QuantumSepPoly.Frobenius


