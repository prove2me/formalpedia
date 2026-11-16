-- Prove2me | Definitions.Def_APSCounting893_Main_Supplement_Certificates
-- name    : APSCounting893_Main_Supplement_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:06:34.914567+00:00
-- url     : https://prove2.me/theorems/cc01665b-16bf-485b-bfba-90777aed6e6c
-- title:
--   Integral-closure certificates, powered systems and algebraic branches
-- statement:
--   For a field $K$, a tuple $F=(f_1,\ldots,f_m)$ and a target $f$ in $K[x_1,\ldots,x_n]$, introduce an independent variable $u$ and set $\Phi=(f_1,\ldots,f_m,u,1-uf)$. A certificate $Q\in K[Y_1,\ldots,Y_m,U,V]$ satisfies
--
--   $$Q(f_1,\ldots,f_m,u,1-uf)=0,\qquad Q(Y_1,\ldots,Y_m,0,0)=1.$$
--
--   The first equality is a polynomial identity in $(x,u)$; the second is a polynomial identity in all $Y$. The complex annihilator is the published substitution kernel with its outputs reindexed. Put $\Delta=\max\{\deg f_i,\deg f+1\}$ and $D_0=(\rho+2)\Delta^{\rho+1}$, where $\rho$ is the transcendence degree of the generated fraction field. Define $\Psi_M=(uf_1^M,\ldots,uf_m^M,u,1-uf)$. Zero polynomials have total degree zero and $\Delta\ge1$.
--
--   For the boundedness criterion, algebraic branches of $\overline{\mathbb C(t)}$ are realized inside the published Puiseux ambient field: a branch is a Puiseux series satisfying a nonzero polynomial in $\mathbb C[t][X]$. This is the algebraic part of the Puiseux closure, with unrestricted ramification. Its valuation is the series order, including $\operatorname{val}_t(0)=+\infty$. These constructions define the actual polynomial objects used by the certificate and reduction theorems.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §7, pp. 28–32; Theorems 7.3, 7.5, 7.7–7.8 and Corollary 7.6

import Definitions.Def_APSCounting893_Main_Supplement_Integrality

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Output variables are Y indexed by Fin m, followed by U and V indexed by Fin 2. -/
abbrev Certificate (K : Type) [CommSemiring K] (m : ℕ) :=
  MvPolynomial (Fin m ⊕ Fin 2) K

noncomputable def phiSystem {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) : PolynomialMap K (n + 1) (m + 2) :=
  Fin.addCases (fun i => extendPolynomial (F i))
    (fun j : Fin 2 => if j = 0 then freshVariable n
      else 1 - freshVariable n * extendPolynomial f)

/-- Substitution in the full polynomial ring, with u independent of x. -/
noncomputable def certificateSubstitute {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) :
    Certificate K m →+* Polynomials K (n + 1) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i => extendPolynomial (F i))
      (fun j : Fin 2 => if j = 0 then freshVariable n
        else 1 - freshVariable n * extendPolynomial f))

/-- Restriction to U=V=0 is a polynomial in every Y coordinate. -/
noncomputable def certificateSlice {K : Type} [Field K] {m : ℕ} :
    Certificate K m →+* Polynomials K m :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X (fun _ => 0))

noncomputable def certificateAt {K : Type} [Field K] {m : ℕ}
    (c : Affine K m) (Q : Certificate K m) : K :=
  MvPolynomial.eval (Sum.elim c (fun _ => 0)) Q

/-- Reuse the published complex annihilator through the canonical output reindexing. -/
noncomputable def certificateAnnihilates {n m : ℕ} (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) (Q : Certificate ℂ m) : Prop :=
  MvPolynomial.rename (Sum.elim (fun i : Fin m => i.castAdd 2)
    (fun j : Fin 2 => j.natAdd m)) Q ∈ annihilator (phiSystem F f)

def GlobalCertificate {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) (Q : Certificate K m) : Prop :=
  certificateSubstitute F f Q = 0 ∧ certificateSlice Q = 1

noncomputable def certificateDelta {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) : ℕ :=
  max (Finset.univ.sup (fun i => (F i).totalDegree)) (f.totalDegree + 1)

noncomputable def certificateBound {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) : ℕ :=
  (generatorRank F + 2) * certificateDelta F f ^ (generatorRank F + 1)

/-- The power is on each generator, before multiplication by u. -/
noncomputable def poweredSystem {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (f : Polynomials K n) (M : ℕ) :
    PolynomialMap K (n + 1) (m + 2) :=
  Fin.addCases (fun i => freshVariable n * extendPolynomial (F i) ^ M)
    (fun j : Fin 2 => if j = 0 then freshVariable n
      else 1 - freshVariable n * extendPolynomial f)

/-- Algebraic branches of C(t) in a fixed Puiseux algebraic closure. The polynomial relation
has coefficients in C[t] and is nonzero as a polynomial before specialization. Clearing
rational-function denominators loses no algebraic branch. -/
def IsAlgebraicBranch (s : PuiseuxAmbient) : Prop :=
  IsPuiseux s ∧ ∃ p : Polynomial (Polynomial ℂ), p ≠ 0 ∧
    Polynomial.eval₂
      (Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))) s p = 0

end APSCounting893.Main.Supplement


