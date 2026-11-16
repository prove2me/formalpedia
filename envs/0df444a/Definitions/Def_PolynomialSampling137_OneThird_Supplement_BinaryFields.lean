-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_BinaryFields
-- name    : PolynomialSampling137_OneThird_Supplement_BinaryFields
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:45:47.068725+00:00
-- url     : https://prove2.me/theorems/daeadc5f-bf0c-4c20-afe3-ea4f3b57edb4
-- title:
--   Binary field coordinates, odd powers and inverse target laws
-- statement:
--   A binary field model consists of an actual finite field $K$ and a linear isomorphism from $K$ to $\mathbb F_2^r$. Uniform image laws are computed from fibers. For $d\ge0$, the odd-power map is
--
--   $$\Phi_d(x)=(x,x^3,\ldots,x^{2^{d+1}-1})\in K^{2^d}.$$
--
--   Its bit coordinates are written in consecutive blocks. For a finite set $S\subset K$, the shifted-inverse law is the law of $((X+a)^{-1})_{a\in S}$ for uniform $X\in K$, with inverse of zero equal to zero. The appended law records $X$ as well. Small bias tests every nonzero binary character, using the real phase $(-1)^{\lambda\cdot y}$. A separate inverse-line map in an extension $E/K$ is $x\mapsto(\theta+x)^{-1}$, expressed in the supplied binary basis of $E$. These are distinct constructions; no estimate is a field of the field model.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §4.2, Appendix A.2 and Appendix C, printed pp. 15–16, 34–35, 41–42; PDF pp. 17–18, 36–37, 43–44

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

/-- A finite characteristic-two field with an actual binary coordinate identification.
No bound or analytic estimate is a field of this structure. -/
structure BinaryField (r : ℕ) where
  Carrier : Type
  field : Field Carrier
  algebra : Algebra (ZMod 2) Carrier
  finite : Fintype Carrier
  coords : Carrier ≃ₗ[ZMod 2] Word r

attribute [instance] BinaryField.field BinaryField.algebra BinaryField.finite

def OddPowers {r : ℕ} (K : BinaryField r) (d : ℕ) (x : K.Carrier) :
    Word (r * 2 ^ d) :=
  fun j => K.coords (x ^ (2 * (j.val / r) + 1)) ⟨j.val % r, by
    have : 0 < r := by
      by_contra h
      have hr : r = 0 := by omega
      have hj := j.isLt
      simp [hr] at hj
    exact Nat.mod_lt _ this⟩

def OddPowerLaw {r : ℕ} (K : BinaryField r) (d : ℕ) : Word (r * 2 ^ d) → ℝ :=
  UniformImage (OddPowers K d)

def ShiftedInverse {r : ℕ} (K : BinaryField r) (S : Finset K.Carrier)
    (x : K.Carrier) : S → K.Carrier := fun a => (x + a.val)⁻¹

def ShiftedInverseLaw {r : ℕ} (K : BinaryField r) (S : Finset K.Carrier) :
    (S → K.Carrier) → ℝ := by
  classical
  exact UniformImage (ShiftedInverse K S)

def AppendedInverseLaw {r : ℕ} (K : BinaryField r) (S : Finset K.Carrier) :
    ((S → K.Carrier) × K.Carrier) → ℝ := by
  classical
  exact UniformImage (fun x => (ShiftedInverse K S x, x))

/-- Every binary character, not merely characters linear over an extension field. -/
def SmallBias {n : ℕ} (P : Word n → ℝ) (ε : ℝ) : Prop :=
  ∀ ell : Word n, ell ≠ 0 →
    |∑ y, P y * (if (∑ i, ell i * y i) = 0 then 1 else -1)| ≤ ε

/-- Inverse line in any finite extension, written in a supplied binary basis. -/
def InverseLine {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra (ZMod 2) E]
    {n : ℕ} (e : E ≃ₗ[ZMod 2] Word n) (θ : E) (x : K) : Word n :=
  e ((θ + algebraMap K E x)⁻¹)

end PolynomialSampling137.OneThird.Supplement


