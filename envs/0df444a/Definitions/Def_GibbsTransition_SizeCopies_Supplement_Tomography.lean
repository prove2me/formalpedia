-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_Tomography
-- name    : GibbsTransition_SizeCopies_Supplement_Tomography
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:37:46.044384+00:00
-- url     : https://prove2.me/theorems/089596dd-d94d-46e8-b7bb-5954d9a397c1
-- title:
--   Separate-copy tomography, spectral flooring, and fixed-temperature learner
-- statement:
--   At field zero, independently measure the $D^2$ observables $|j\rangle\langle j|$, $X_{jk}=|j\rangle\langle k|+|k\rangle\langle j|$, and $Y_{jk}=i(|j\rangle\langle k|-|k\rangle\langle j|)$, in dimensions $D=q,q^8$. Their spectral Born laws determine a rational Hermitian estimate. Choose a fixed positive rational $\mu\in[\mu_0/4,\mu_0/2]$, where $\mu_0=q^{-8}e^{-2\beta(20J+4J_b)}$, and
--   $$t=\min\{\mu/4,\beta\mu d\epsilon/24576\},\qquad s_D=2D^2t^{-2}\log(4D^2/\delta).$$
--   A rational logarithm upper approximation chooses an integer count in $[s_D,s_D+2)$ per observable. On every outcome, the Bernstein polynomial of degree $\lceil D^2/t^2\rceil$ floors the spectrum at $\mu/2$. A finite rational matrix-logarithm series, trace removal and subtraction of the known boundary recover bulk terms. The public effect and boundary are approximated through a recursive public table; its contents do not include the unknown terms. The final output is the rational finite-energy search applied to these reconstructed terms.
--
--   The two supplied systems have sides one and two only, both at field zero. The explicit query counts give the supplied-spin total with weights one and eight. No energy oracle or success assumption enters the algorithm, including on bad tomography outcomes.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), (45)–(56),(76)–(79), printed pp. 13–15,24–25 (PDF pp. 15–17,26–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Numerics
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

/-- A public recursive Cauchy table for P (slot 0) and B_L (slot L).
Only public data are in this table; it never encodes an unknown interaction. -/
structure PublicNumerics where
  code : ℕ → ℕ

def publicEntry (v : PublicNumerics) (L row col m : ℕ) : QC :=
  let z := (Encodable.decode (v.code (Encodable.encode (L,row,col,m))) : Option (ℚ × ℚ)).getD (0,0)
  qc z.1 z.2

def EffectivePublic {q : ℕ} (p : FieldData q) (v : PublicNumerics) : Prop :=
  Computable v.code ∧
  (∀ (i j : Fin q) (m : ℕ),
    ‖qcComplex (publicEntry v 0 i.val j.val m)-p.P i j‖ ≤ (2:ℝ)^(-(m:ℤ))) ∧
  ∀ (L : ℕ), 1 ≤ L → ∀ (s t : Config q L) (m : ℕ),
    ‖qcComplex (publicEntry v L (configCode s) (configCode t) m)-p.boundary L s t‖ ≤
      (2:ℝ)^(-(m:ℤ))

def hermitianize {n : Type} (A : QMatrix n) : QMatrix n :=
  qScale (1/2) (A + A.conjTranspose)

def publicBlock (v : PublicNumerics) (L D m : ℕ) : QMatrix (Fin D) :=
  hermitianize (fun i j => publicEntry v L i.val j.val m)

def numericPrecision {q : ℕ} (p : FieldData q) (epsilon : ℚ) : ℕ :=
  2^20 * (q^8+1) * (gap p * epsilon).den

def muFloor {q : ℕ} (p : FieldData q) (beta : ℚ) : ℝ :=
  (q : ℝ)^(-8 : ℤ) * Real.exp (-2*(beta : ℝ)*(20*p.J+4*p.Jb))

def tomographyTolerance {q : ℕ} (p : FieldData q) (beta mu epsilon : ℚ) : ℚ :=
  min (mu/4) (beta*mu*gap p*epsilon/24576)

def tomographyCount (D : ℕ) (t delta : ℚ) : ℕ :=
  ⌈2*(D : ℚ)^2/t^2 * logUpper (4*(D : ℚ)^2/delta) (t^2/(16*(D : ℚ)^2))⌉₊

abbrev TomographyData (D n : ℕ) := Fin D → Fin D → Fin n → Fin 3

def empirical {D n : ℕ} (y : TomographyData D n) (i j : Fin D) : ℚ :=
  (∑ k : Fin n, ((y i j k).val : ℚ)-1) / n

/-- (49), indexed by D² ordered pairs: diagonal A_j, upper X_jk, lower Y_jk. -/
def observable {D : ℕ} (i j : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  if i = j then Matrix.single i i 1 else
    if i < j then Matrix.single i j 1 + Matrix.single j i 1
    else Complex.I • (Matrix.single j i 1 - Matrix.single i j 1)

/-- Spectral projective Born law for each of the three possible outcomes.
Zero-probability extra outcomes for A_j are retained as harmless encodings. -/
def observableProbability {D : ℕ} (rho : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) (r : Fin 3) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.trace (rho * cfc
    (fun x : ℝ => if x = (r.val : ℝ)-1 then 1 else 0) (observable i j))).re

def tomographyWeight {D n : ℕ} (rho : Matrix (Fin D) (Fin D) ℂ)
    (y : TomographyData D n) : ℝ≥0∞ :=
  ∏ i : Fin D, ∏ j : Fin D, ∏ k : Fin n, observableProbability rho i j (y i j k)

/-- The sign in the imaginary entry matches Y=i(E_jk-E_kj) in (49). -/
def rawEstimate {D n : ℕ} (y : TomographyData D n) : QMatrix (Fin D) :=
  fun i j => if i = j then qc (empirical y i i) 0 else
    if i < j then qc (empirical y i j/2) (empirical y j i/2)
    else qc (empirical y j i/2) (-empirical y i j/2)

/-- Exact rational Bernstein polynomial (76), defined even on bad outcomes. -/
def spectralFloor {D : ℕ} (R : QMatrix (Fin D)) (mu t : ℚ) : QMatrix (Fin D) :=
  let m := ⌈(D : ℚ)^2/t^2⌉₊
  let T := qScale (1/(2*(D : ℚ))) (R + qScale D 1)
  ∑ k ∈ Finset.range (m+1),
    qScale (max (2*(D : ℚ)*k/m-D) (mu/2) * (Nat.choose m k : ℚ))
      (T^k * (1-T)^(m-k))

/-- log(sigma)-log(D)I by a finite rational series. The removed scalar is
irrelevant to traceless inversion. No exact matrix logarithm is an input. -/
def logApprox {D : ℕ} (sigma : QMatrix (Fin D)) (mu tau : ℚ) : QMatrix (Fin D) :=
  let n := ⌈(2*(D : ℚ)/mu)^2 * ((tau.den : ℚ)+1)*1024⌉₊;
  -(∑ k ∈ Finset.range n,
    qScale (1/(k+1 : ℚ)) ((1-qScale (1/(D : ℚ)) sigma)^(k+1)))

def invertBlock {q : ℕ} (p : FieldData q) (v : PublicNumerics)
    (L D : ℕ) (beta mu epsilon : ℚ) (R : QMatrix (Fin D)) : QMatrix (Fin D) :=
  let t := tomographyTolerance p beta mu epsilon
  let sigma := spectralFloor R mu t
  let tau := beta*gap p*epsilon/2^20
  qScale (-1/beta) (qTraceFree (logApprox sigma mu tau)) -
    qTraceFree (publicBlock v L D (numericPrecision p epsilon))

def qTensor {q : ℕ} (A B : QMatrix (Fin q)) : QMatrix (Fin q × Fin q) :=
  fun s t => A s.1 t.1 * B s.2 t.2

def qPartialSite {q : ℕ} (X : QMatrix (Config q 2)) (x : Site 2) : QMatrix (Fin q) :=
  fun a b => qReal (1/(q : ℚ)^7) * ∑ s : Config q 2,
    if (s x).val = 0 then X (Function.update s x a) (Function.update s x b) else 0

def qPartialEdge {q : ℕ} (X : QMatrix (Config q 2)) (x y : Site 2) : QMatrix (Fin q × Fin q) :=
  fun a b => qReal (1/(q : ℚ)^6) * ∑ s : Config q 2,
    if (s x).val = 0 ∧ (s y).val = 0 then
      X (Function.update (Function.update s x a.1) y a.2)
        (Function.update (Function.update s x b.1) y b.2) else 0

def reconstructedTerms {q : ℕ} (hq : 0 < q) (p : FieldData q) (v : PublicNumerics)
    (beta mu epsilon : ℚ) {n1 n2 : ℕ}
    (y1 : TomographyData q n1) (y2 : TomographyData (q^8) n2) : RationalTerms q :=
  let X1 := invertBlock p v 1 q beta mu epsilon (rawEstimate y1)
  let Y2 := invertBlock p v 2 (q^8) beta mu epsilon (rawEstimate y2)
  let X2 : QMatrix (Config q 2) := fun s t => Y2
    ⟨configCode s % q^8, Nat.mod_lt _ (pow_pos hq 8)⟩
    ⟨configCode t % q^8, Nat.mod_lt _ (pow_pos hq 8)⟩
  let C := fun x => qPartialSite X2 x
  { onsite := qScale 2 (qScale (1/8) (∑ x : Site 2, C x)) - X1
    edge := fun i => qPartialEdge X2 corner (adjacent i) -
      qTensor (C corner) 1 - qTensor 1 (C (adjacent i))
    effect := publicBlock v 0 q (numericPrecision p epsilon) }

def tomographyRho1 {q : ℕ} (hq : 0 < q) (p : FieldData q) (u : FieldInteraction q)
    (beta : ℚ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => fieldGibbs p u 1 0 beta (decodeConfig hq 1 i.val) (decodeConfig hq 1 j.val)

def tomographyRho2 {q : ℕ} (hq : 0 < q) (p : FieldData q) (u : FieldInteraction q)
    (beta : ℚ) : Matrix (Fin (q^8)) (Fin (q^8)) ℂ :=
  fun i j => fieldGibbs p u 2 0 beta (decodeConfig hq 2 i.val) (decodeConfig hq 2 j.val)

/-- The complete learner: separate-copy observables, rational spectral floor,
log inversion with known boundary subtraction, reconstruction, finite search.
The unknown u appears only in the two physical input density matrices. -/
def tomographyFinal {q : ℕ} (hq : 0 < q) (p : FieldData q) (v : PublicNumerics)
    (u : FieldInteraction q) (beta mu epsilon delta : ℚ) : Measure ℚ :=
  let t := tomographyTolerance p beta mu epsilon
  let n1 := tomographyCount q t delta
  let n2 := tomographyCount (q^8) t delta
  ∑ y1 : TomographyData q n1, ∑ y2 : TomographyData (q^8) n2,
    (tomographyWeight (tomographyRho1 hq p u beta) y1 *
      tomographyWeight (tomographyRho2 hq p u beta) y2) •
    Measure.dirac (energySearch hq p (reconstructedTerms hq p v beta mu epsilon y1 y2) epsilon)

def tomographyCopies {q : ℕ} (p : FieldData q) (beta mu epsilon delta : ℚ) : ℕ :=
  let t := tomographyTolerance p beta mu epsilon
  q^2 * tomographyCount q t delta + (q^8)^2 * tomographyCount (q^8) t delta

def tomographySpins {q : ℕ} (p : FieldData q) (beta mu epsilon delta : ℚ) : ℕ :=
  let t := tomographyTolerance p beta mu epsilon
  q^2 * tomographyCount q t delta + 8*(q^8)^2 * tomographyCount (q^8) t delta

end GibbsTransition.SizeCopies.Supplement


