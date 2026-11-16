-- Prove2me | Definitions.Def_CKKSPrecision_FourierUnits_Supplement_ckks_model
-- name    : CKKSPrecision_FourierUnits_Supplement_ckks_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:23:18.157191+00:00
-- url     : https://prove2.me/theorems/3d77b1bf-abc7-4e51-b3b8-04a1b7599e8b
-- title:
--   CKKS power-basis encoding, ciphertext phases and restored errors
-- statement:
--   Let $r\ge1$ be a power of two, $N=2r$ and $R=\mathbb Z[\zeta]$ for the published primitive $4r$th root. Use the published slots $\sigma_j(\zeta)=\zeta^{5^j}$, $0\le j<r$. A ciphertext has two integral components, interpreted modulo an odd integer $Q>1$. Its phase under secret $s\in R$ is $c_0+c_1s$.
--
--   The inverse selected-embedding transform has power-basis coefficients
--   $$
--   f_k=\frac1r\sum_{j=0}^{r-1}\operatorname{Re}\bigl(z_j\sigma_j(\zeta)^{-k}\bigr),\qquad 0\le k<N.
--   $$
--   Encoding rounds $\Delta f_k$ to the nearest integer, with half-integer ties toward $+\infty$. Centered reduction reduces each integral coefficient to $(-Q/2,Q/2)$. Congruence is equality up to $Q$ times an element of $R$. Rescaling computes the centered residues modulo $D$, divides the residue differences by $D$, and reduces modulo $Q'=Q/D$.
--
--   A restored representation consists of $M\in R$ with
--   $$
--   p(c_0+c_1s)\equiv M\pmod Q,\qquad \sigma_j(M)=\Delta(x_j+e_j).
--   $$
--   The normalized error is $\eta_j=e_j/\sigma_j(p)$, used only for nonzero $p$. Decoding applies the slot embeddings to the centered restored phase and divides by the scale. The definition also gives the exact component operations and an abstract relinearization phase-error interface, together with the expression in parentheses in (20).
--
--   These objects give the arithmetic interface shared by both preservation lemmas and the circuit analysis. Integral ring membership is explicit; all field divisions are used only under the positivity and integrality hypotheses of the statements.
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), pp. 4, 6–7, 13–15 (PDF pp. 6, 8–9, 15–17), §§2.1–2.2, 3.1, 7.1–7.2, (16)–(20).

import Definitions.Def_CKKSPrecision_FourierUnits_fourier_construction

set_option autoImplicit false
noncomputable section

namespace CKKSPrecision.FourierUnits.Supplement

abbrev Scalar (r : ℕ+) := K (conductor r)
abbrev Slot (r : ℕ+) := Fin (r : ℕ)
abbrev Vector (r : ℕ+) := Slot r → ℂ
abbrev Coeff (r : ℕ+) := Fin (2 * (r : ℕ))

def InRing {r : ℕ+} (f : Scalar r) : Prop := f ∈ R (conductor r)

def sigma {r : ℕ+} (f : Scalar r) : Vector r := fun j => slots r j f

/-- Inverse selected embedding transform in the power basis, including the conjugate half.
    For power-of-two r these are exactly the 2r real coefficients of sigma^{-1}(z). -/
def inverseCoeff {r : ℕ+} (z : Vector r) (k : Coeff r) : ℝ :=
  (∑ j, (z j * (slots r j (zeta (conductor r))) ^ (-(k.val : ℤ))).re) / (r : ℕ)

def coeffReal {r : ℕ+} (f : Scalar r) (k : Coeff r) : ℝ := inverseCoeff (sigma f) k

def evalInteger {r : ℕ+} (a : Coeff r → ℤ) : Scalar r :=
  ∑ k, (a k : Scalar r) * zeta (conductor r) ^ k.val

/-- Fixed nearest-integer tie convention, toward positive infinity. -/
def encode {r : ℕ+} (delta : ℝ) (x : Vector r) : Scalar r :=
  evalInteger (fun k => ⌊delta * inverseCoeff x k + 1 / 2⌋)

/-- Centered integer residue for positive odd q. No boundary tie can occur. -/
def centerInt (q a : ℤ) : ℤ := (a + (q - 1) / 2) % q - (q - 1) / 2

/-- Polynomial coefficient reduction; integral inputs have integral power-basis coefficients. -/
def center {r : ℕ+} (q : ℕ) (f : Scalar r) : Scalar r :=
  evalInteger (fun k => centerInt q ⌊coeffReal f k⌋)

def Congruent {r : ℕ+} (q : ℕ) (f g : Scalar r) : Prop :=
  ∃ h : Scalar r, InRing h ∧ f - g = (q : Scalar r) * h

structure Cipher (r : ℕ+) where
  c0 : Scalar r
  c1 : Scalar r

def IntegralCipher {r : ℕ+} (ct : Cipher r) : Prop := InRing ct.c0 ∧ InRing ct.c1

def phase {r : ℕ+} (s : Scalar r) (ct : Cipher r) : Scalar r := ct.c0 + ct.c1 * s

def centeredCipher {r : ℕ+} (q : ℕ) (ct : Cipher r) : Cipher r :=
  ⟨center q ct.c0, center q ct.c1⟩

def residues {r : ℕ+} (d : ℕ) (ct : Cipher r) : Cipher r := centeredCipher d ct

def rescale {r : ℕ+} (d q' : ℕ) (ct : Cipher r) : Cipher r :=
  centeredCipher q' ⟨(ct.c0 - center d ct.c0) / d, (ct.c1 - center d ct.c1) / d⟩

def rescaledMessage {r : ℕ+} (d : ℕ) (p s m : Scalar r) (ct : Cipher r) : Scalar r :=
  (m - p * phase s (residues d ct)) / d

def Represented {r : ℕ+} (q : ℕ) (delta : ℝ) (p s : Scalar r)
    (ct : Cipher r) (m : Scalar r) (x e : Vector r) : Prop :=
  InRing m ∧ Congruent q (p * phase s ct) m ∧
    ∀ j, sigma m j = (delta : ℂ) * (x j + e j)

def restoredError {r : ℕ+} (delta : ℝ) (m : Scalar r) (x : Vector r) : Vector r :=
  fun j => sigma m j / (delta : ℂ) - x j

def normalizedError {r : ℕ+} (delta : ℝ) (p m : Scalar r) (x : Vector r) : Vector r :=
  fun j => restoredError delta m x j / sigma p j

def decoded {r : ℕ+} (q : ℕ) (delta : ℝ) (p s : Scalar r) (ct : Cipher r) : Vector r :=
  fun j => sigma (center q (p * phase s ct)) j / (delta : ℂ)

def addCipher {r : ℕ+} (q : ℕ) (a b : Cipher r) : Cipher r :=
  centeredCipher q ⟨a.c0 + b.c0, a.c1 + b.c1⟩

def subCipher {r : ℕ+} (q : ℕ) (a b : Cipher r) : Cipher r :=
  centeredCipher q ⟨a.c0 - b.c0, a.c1 - b.c1⟩

def addPlainCipher {r : ℕ+} (q : ℕ) (a : Cipher r) (mu : Scalar r) : Cipher r :=
  ⟨center q (a.c0 + mu), a.c1⟩

def multPlainCipher {r : ℕ+} (q : ℕ) (a : Cipher r) (mu : Scalar r) : Cipher r :=
  centeredCipher q ⟨mu * a.c0, mu * a.c1⟩

/-- Phase before relinearization of the tensor product corrected componentwise by p. -/
def productPhase {r : ℕ+} (q : ℕ) (p s : Scalar r) (a b : Cipher r) : Scalar r :=
  center q (p * center q (a.c0 * b.c0)) +
    center q (p * center q (a.c0 * b.c1 + a.c1 * b.c0)) * s +
    center q (p * center q (a.c1 * b.c1)) * s ^ 2

/-- Abstract relinearization: the evaluation-key details are immaterial to this interface. -/
def Relin {r : ℕ+} (q : ℕ) (p s : Scalar r) (a b out : Cipher r) (kappa : Scalar r) : Prop :=
  IntegralCipher out ∧ InRing kappa ∧
    Congruent q (phase s out) (productPhase q p s a b + kappa)

def multiplicationBound {r : ℕ+} (p : Scalar r) (aa ab ba bb : Slot r → ℝ)
    (kappaBound residueBound : ℝ) (d : ℕ) (delta : ℝ) (j : Slot r) : ℝ :=
  aa j * bb j + ab j * ba j + ‖sigma p j‖ * ba j * bb j +
    (kappaBound + residueBound) / ((d : ℝ) * delta)

end CKKSPrecision.FourierUnits.Supplement


