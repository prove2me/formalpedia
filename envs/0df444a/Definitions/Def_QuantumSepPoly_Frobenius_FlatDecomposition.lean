-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_FlatDecomposition
-- name    : QuantumSepPoly_Frobenius_FlatDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:50.72001+00:00
-- url     : https://prove2.me/theorems/01c20b50-ab4c-4148-bf0c-a96260dbccf2
-- title:
--   Entrywise flat and tail decomposition
-- statement:
--   For fixed constants $c_0,c_1$ and integer $m$, set $p=\lceil m(1+\log(1/\delta))\rceil$. Below the source dimension threshold use the entire rotated matrix as the flat part and zero as the tail. Otherwise threshold rotated entries at
--   $$8c_1p^2\|M\|_F/d^2.$$
--   Entries strictly larger in modulus go into the tail; the others remain in the flat part. The source successful event is the computed inequality $\|M_{\rm tail}\|_F\le\delta\|M\|_F$. The data structure carries constants only, without assumed success or correctness.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_HaarQR

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- Data of the cutoff in Lemma 3.3, pp.12–13. It asserts no correctness. -/
structure FlatParameters where
  c0 : ℝ
  c1 : ℝ
  m : ℕ

def flatPower (p : FlatParameters) (δ : ℝ) : ℕ := Nat.ceil (p.m * (1 + Real.log (1/δ)))
def flatSmall (p : FlatParameters) (δ : ℝ) (d : ℕ) : Prop :=
  (d : ℝ) < (p.m + 1) * (Real.log (1/δ) + 1) / p.c0

def flatPart {d : ℕ} (p : FlatParameters) (δ : ℝ) (M : Bip d) (U V : Op d) : Bip d := by
  classical
  let X := locallyRotate M U V
  let cutoff := 8 * p.c1 * (flatPower p δ : ℝ)^2 * frob M / (d : ℝ)^2
  exact if flatSmall p δ d then X else fun i j => if ‖X i j‖ > cutoff then 0 else X i j

def tailPart {d : ℕ} (p : FlatParameters) (δ : ℝ) (M : Bip d) (U V : Op d) : Bip d :=
  locallyRotate M U V - flatPart p δ M U V

/-- The reduction tests the computed tail, rather than assuming it is small. -/
def flattenSuccess {d : ℕ} (p : FlatParameters) (δ : ℝ) (M : Bip d) (U V : Op d) : Prop :=
  frob (tailPart p δ M U V) ≤ δ * frob M

end QuantumSepPoly.Frobenius


