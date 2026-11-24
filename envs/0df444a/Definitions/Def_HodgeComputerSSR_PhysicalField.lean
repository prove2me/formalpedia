-- Prove2me | Definitions.Def_HodgeComputerSSR_PhysicalField
-- name    : HodgeComputerSSR_PhysicalField
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:36:53.379172+00:00
-- url     : https://prove2.me/theorems/8c71acc1-e1e4-4a51-83cf-60220f932c76
-- title:
--   Physical sextic hypersurface, irreducibility, and residue field
-- statement:
--   Defines the symmetric sextic hypersurface $F \in \mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]$ and monomial source $A = X_0 X_1 X_2 Y_0 Y_1 Y_2$ for `symmetric-sextic-residual`, matching `HodgeComputer.SymmetricSexticResidual.{F, A}` verbatim:
--
--   $$F = \sum_{i=0}^2 X_i^6 + \sum_{j=0}^2 Y_j^6 + \frac{5}{7} Q_X^2 Q_Y + \frac{10}{7} Q_X Q_Y^2,$$
--
--   where $Q_X = X_0 X_1 + X_0 X_2 + X_1 X_2$ and $Q_Y = Y_0 Y_1 + Y_0 Y_2 + Y_1 Y_2$. Proves $F$ is homogeneous of degree $6$ and irreducible (via specialization to $Y^6 + ((X+1)^6 - 1)$ and Eisenstein's criterion), defines the domain quotient ring $\mathbb{C}[X, Y]/(F)$ and its function field `FunctionField`, and records the normalized certificate bridge `certificate_of_normalized`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/PhysicalField.lean

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Definitions.Def_HodgeComputerFormal_Algebra
import Theorems.Thm_HodgeComputer_Formal_HoldoutCover_irreducible_power_add_constant
import Theorems.Thm_HodgeComputer_Formal_HoldoutCover_hasCertificate_of_normalized
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-! Physical sextic hypersurface, irreducibility, residue function field,
and homogeneous certificate bridge for `symmetric-sextic-residual`. -/

noncomputable section
namespace SymmetricSexticResidual
open MvPolynomial HoldoutConstruction
open scoped Polynomial

abbrev Poly6 := MvPolynomial (Fin 6) ℂ

def e1X : Poly6 := X 0 + X 1 + X 2
def QX  : Poly6 := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
def e3X : Poly6 := X 0 * X 1 * X 2
def e1Y : Poly6 := X 3 + X 4 + X 5
def QY  : Poly6 := X 3 * X 4 + X 3 * X 5 + X 4 * X 5
def e3Y : Poly6 := X 3 * X 4 * X 5
def ΔX  : Poly6 := (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)
def ΔY  : Poly6 := (X 3 - X 4) * (X 3 - X 5) * (X 4 - X 5)

def sextic : Poly6 :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 +
    C (5 / 7 : ℂ) * QX ^ 2 * QY + C (10 / 7 : ℂ) * QX * QY ^ 2

def source : Poly6 := e3X * e3Y

theorem sextic_eq_target : sextic = HodgeComputer.SymmetricSexticResidual.F := by
  dsimp only [sextic, QX, QY, HodgeComputer.SymmetricSexticResidual.F]
  have h5 : C (σ := Fin 6) (5 / 7 : ℂ) = (5 : Poly6) * C (1 / 7 : ℂ) := by
    rw [show (5 : Poly6) = C (5 : ℂ) from rfl, ← map_mul]; congr 1; norm_num
  have h10 : C (σ := Fin 6) (10 / 7 : ℂ) = (10 : Poly6) * C (1 / 7 : ℂ) := by
    rw [show (10 : Poly6) = C (10 : ℂ) from rfl, ← map_mul]; congr 1; norm_num
  have h20 : (20 : Poly6) * C (1 / 7 : ℂ) = 2 * ((10 : Poly6) * C (1 / 7 : ℂ)) := by ring
  rw [h5, h10]
  ring

theorem source_eq_target : source = HodgeComputer.SymmetricSexticResidual.A := by
  dsimp only [source, e3X, e3Y, HodgeComputer.SymmetricSexticResidual.A]
  ring

theorem QX_isHomogeneous : QX.IsHomogeneous 2 := by
  have h (i j : Fin 6) : (X (R := ℂ) i * X j).IsHomogeneous 2 :=
    (isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)
  exact ((h 0 1).add (h 0 2)).add (h 1 2)

theorem QY_isHomogeneous : QY.IsHomogeneous 2 := by
  have h (i j : Fin 6) : (X (R := ℂ) i * X j).IsHomogeneous 2 :=
    (isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)
  exact ((h 3 4).add (h 3 5)).add (h 4 5)

theorem sextic_isHomogeneous : sextic.IsHomogeneous 6 := by
  have hp (i : Fin 6) : (X (R := ℂ) i ^ 6).IsHomogeneous 6 := isHomogeneous_X_pow i 6
  have h1 : (C (5 / 7 : ℂ) * QX ^ 2 * QY).IsHomogeneous 6 := by
    have hq2 : (QX ^ 2).IsHomogeneous 4 := by simpa using QX_isHomogeneous.pow 2
    have hc : (C (σ := Fin 6) (5 / 7 : ℂ) * QX ^ 2).IsHomogeneous 4 := by
      simpa using (isHomogeneous_C (Fin 6) (5 / 7 : ℂ)).mul hq2
    simpa using hc.mul QY_isHomogeneous
  have h2 : (C (10 / 7 : ℂ) * QX * QY ^ 2).IsHomogeneous 6 := by
    have hq2 : (QY ^ 2).IsHomogeneous 4 := by simpa using QY_isHomogeneous.pow 2
    have hc : (C (σ := Fin 6) (10 / 7 : ℂ) * QX).IsHomogeneous 2 := by
      simpa using (isHomogeneous_C (Fin 6) (10 / 7 : ℂ)).mul QX_isHomogeneous
    simpa using hc.mul hq2
  exact ((((((hp 0).add (hp 1)).add (hp 2)).add (hp 3)).add (hp 4)).add (hp 5)).add h1 |>.add h2

theorem source_isHomogeneous : source.IsHomogeneous 6 := by
  have hx : e3X.IsHomogeneous 3 :=
    ((isHomogeneous_X ℂ (0 : Fin 6)).mul (isHomogeneous_X ℂ 1)).mul (isHomogeneous_X ℂ 2)
  have hy : e3Y.IsHomogeneous 3 :=
    ((isHomogeneous_X ℂ (3 : Fin 6)).mul (isHomogeneous_X ℂ 4)).mul (isHomogeneous_X ℂ 5)
  exact hx.mul hy

private def qxTail : MvPolynomial (Fin 5) ℂ := X 0 * X 1
private def qxLin  : MvPolynomial (Fin 5) ℂ := X 0 + X 1
private def qyTail : MvPolynomial (Fin 5) ℂ := X 2 * X 3 + X 2 * X 4 + X 3 * X 4

private def sexticUni : (MvPolynomial (Fin 5) ℂ)[X] :=
  Polynomial.X ^ 6 +
    Polynomial.C (MvPolynomial.C (5 / 7 : ℂ) * qxLin ^ 2 * qyTail) * Polynomial.X ^ 2 +
    Polynomial.C (MvPolynomial.C (10 / 7 : ℂ) * qxLin * qxTail * qyTail +
      MvPolynomial.C (10 / 7 : ℂ) * qxLin * qyTail ^ 2) * Polynomial.X +
    Polynomial.C (X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 +
      MvPolynomial.C (5 / 7 : ℂ) * qxTail ^ 2 * qyTail +
      MvPolynomial.C (10 / 7 : ℂ) * qxTail * qyTail ^ 2)

private theorem sexticUni_monic : sexticUni.Monic := by
  dsimp only [sexticUni]
  rw [add_assoc, add_assoc]
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 2 _) (by decide)
  · apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

private theorem finSuccEquiv_sextic :
    MvPolynomial.finSuccEquiv ℂ 5 sextic = sexticUni := by
  have he : (Fin.cases (Polynomial.X : (MvPolynomial (Fin 5) ℂ)[X])
      (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X, Polynomial.C (X 0), Polynomial.C (X 1),
        Polynomial.C (X 2), Polynomial.C (X 3), Polynomial.C (X 4)] := by
    funext i; fin_cases i <;> rfl
  simp [sextic, QX, QY, sexticUni, qxTail, qxLin, qyTail,
    MvPolynomial.finSuccEquiv_apply, he]
  have h10 : Polynomial.C (MvPolynomial.C (σ := Fin 5) (10 / 7 : ℂ)) =
      2 * Polynomial.C (MvPolynomial.C (σ := Fin 5) (5 / 7 : ℂ)) := by
    rw [show (2 : (MvPolynomial (Fin 5) ℂ)[X]) = Polynomial.C (MvPolynomial.C 2) from rfl,
      ← map_mul, ← map_mul]
    congr 2; norm_num
  rw [h10]
  ring

private def irredSpec : MvPolynomial (Fin 5) ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X + 1, Polynomial.C Complex.I, 0]

private theorem sexticUni_map_irredSpec :
    sexticUni.map irredSpec =
      (Polynomial.X : (ℂ[X])[X]) ^ 6 + Polynomial.C ((Polynomial.X + 1) ^ 6 - 1) := by
  have hi6 : (Complex.I : ℂ) ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, Complex.I_sq]; norm_num
  have hspec (i : Fin 5) : irredSpec (X i) =
      (![0, 0, Polynomial.X + 1, Polynomial.C Complex.I, 0] : Fin 5 → ℂ[X]) i := by
    simp [irredSpec]
  have hlin : irredSpec qxLin = 0 := by simp [qxLin, hspec]
  have htail : irredSpec qxTail = 0 := by simp [qxTail, hspec]
  simp only [sexticUni, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  have hc0 : irredSpec (MvPolynomial.C (5 / 7 : ℂ) * qxLin ^ 2 * qyTail) = 0 := by
    simp [map_mul, map_pow, hlin]
  have hc1 : irredSpec (MvPolynomial.C (10 / 7 : ℂ) * qxLin * qxTail * qyTail +
      MvPolynomial.C (10 / 7 : ℂ) * qxLin * qyTail ^ 2) = 0 := by
    simp [map_add, map_mul, hlin]
  have hc2 : irredSpec (X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 +
      MvPolynomial.C (5 / 7 : ℂ) * qxTail ^ 2 * qyTail +
      MvPolynomial.C (10 / 7 : ℂ) * qxTail * qyTail ^ 2) = (Polynomial.X + 1) ^ 6 - 1 := by
    simp only [map_add, map_mul, map_pow, hspec, htail,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      zero_pow (by decide : 6 ≠ 0), zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, add_zero, zero_add]
    rw [← map_pow, hi6, map_neg, map_one, sub_eq_add_neg]
  rw [hc0, hc1, hc2]
  simp

theorem sextic_irreducible : Irreducible sextic := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [finSuccEquiv_sextic]
  apply sexticUni_monic.irreducible_of_irreducible_map irredSpec
  rw [sexticUni_map_irredSpec]
  exact HodgeComputer.Formal.HoldoutCover.irreducible_power_add_constant ((Polynomial.X + 1) ^ 6 - 1 : ℂ[X])
    (by simp [Polynomial.coeff_X_add_one_pow])
    (by norm_num [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one])
    6 (by decide)

theorem sextic_prime : Prime sextic := sextic_irreducible.prime

theorem sextic_not_dvd_pderiv_zero : ¬ sextic ∣ MvPolynomial.pderiv (0 : Fin 6) sextic := by
  rintro ⟨q, hq⟩
  let ev : Poly6 →+* ℂ[X] := MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0, 0, 0, 0, 0]
  have h1 : ev (MvPolynomial.pderiv (0 : Fin 6) sextic) = 6 * Polynomial.X ^ 5 := by
    simp [ev, sextic, QX, QY, pderiv_X]
  have h2 : ev sextic = Polynomial.X ^ 6 := by
    simp [ev, sextic, QX, QY]
  have h3 := congrArg ev hq
  rw [map_mul, h1, h2] at h3
  have h5 := congrArg (fun p : ℂ[X] => p.coeff 5) h3
  simp [Polynomial.coeff_X_pow_mul'] at h5

abbrev QuotientRing := Poly6 ⧸ Ideal.span {sextic}

instance : IsDomain QuotientRing := by
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact Ideal.span_singleton_prime sextic_prime.ne_zero |>.mpr sextic_prime

abbrev FunctionField := FractionRing QuotientRing
abbrev AmbientField  := FractionRing Poly6

def quotientMap : Poly6 →+* QuotientRing := Ideal.Quotient.mk _
def residueMap  : Poly6 →+* FunctionField := (algebraMap QuotientRing FunctionField).comp quotientMap

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  Ideal.Quotient.mk_surjective

theorem quotientMap_eq_zero_iff (p : Poly6) : quotientMap p = 0 ↔ sextic ∣ p := by
  change Ideal.Quotient.mk (Ideal.span {sextic}) p = 0 ↔ sextic ∣ p
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem residueMap_eq_zero_iff (p : Poly6) : residueMap p = 0 ↔ sextic ∣ p :=
  HoldoutConstruction.residue_fractionMap_kernel quotientMap sextic quotientMap_eq_zero_iff p

theorem certificate_of_normalized
    (D : Poly6) (N : Fin 6 → Poly6) (Q : Poly6)
    (hlegal : residueMap D ≠ 0)
    (normal : HodgeTestbed.directional sextic N = source * D)
    (divergence : HodgeTestbed.divergenceNumerator D N = sextic * Q) :
    HodgeComputer.HasCertificate (n := HodgeComputer.SymmetricSexticResidual.n) HodgeComputer.SymmetricSexticResidual.F HodgeComputer.SymmetricSexticResidual.A HodgeComputer.SymmetricSexticResidual.d HodgeComputer.SymmetricSexticResidual.q := by
  change HodgeComputer.HasCertificate (n := 5) HodgeComputer.SymmetricSexticResidual.F HodgeComputer.SymmetricSexticResidual.A 6 1
  rw [← sextic_eq_target, ← source_eq_target]
  have hrel : IsRelPrime sextic D :=
    (HoldoutConstruction.legal_of_residue_ne_zero residueMap sextic D
      sextic_irreducible residueMap_eq_zero_iff hlegal).2
  exact HodgeComputer.Formal.HoldoutCover.hasCertificate_of_normalized sextic source D N Q
    sextic_isHomogeneous source_isHomogeneous sextic_prime hrel
    normal divergence 0 sextic_not_dvd_pderiv_zero

end SymmetricSexticResidual


