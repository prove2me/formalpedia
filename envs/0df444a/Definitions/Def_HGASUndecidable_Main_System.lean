-- Prove2me | Definitions.Def_HGASUndecidable_Main_System
-- name    : HGASUndecidable_Main_System
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:16:13.732207+00:00
-- url     : https://prove2.me/theorems/27be56ba-e23e-4478-87d4-fca120554272
-- title:
--   The full polynomial system X_e and all tests of Section 8.4.1
-- statement:
--   The state dimension is nₛ=38q+4r+2. The order is (r_l,s_l,Re ζ_l,Im ζ_l) for each clock, Re R,Im R, then 17 complex coordinates (L,C,E,Y,ψ₂,ψ₃,ψ₄,H,T₁,T₂,T₃,T₄,Δ,U,G,G⁺,G⁻) per unknown. Complex multivariate polynomials are split coefficientwise into real and imaginary parts. Negative character powers use positive powers of conjugates, so off-circle formulas remain polynomial. The controller, oscillator, modular, Jacobi Z and J, auxiliary-root and reciprocal equations are written in full. Residuals are the squared real constraints and squared moduli of all eleven complex constraints per unknown. All seven complex moments per unknown appear. Dobs is R times the product F_j(1−η²)G⁺_jG⁻_j. The test vector consists of every residual, both components of every moment, and both components of Dobs. Passing the tests retains both zero averages and pointwise residual vanishing.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §8.4.1, (8.1),(8.4),(8.6)–(8.14),(8.20)–(8.23), printed pp. 40–57 (PDF 42–59)

import Definitions.Def_HGASUndecidable_Main_Fourier

noncomputable section
open scoped BigOperators ComplexConjugate

namespace HGASUndecidable.Main

abbrev CPoly (n : ℕ) := MvPolynomial (Fin n) ℂ

def ns (a : DiophantineData) : ℕ := 38*a.q + 4*a.r + 2

def polyVariable (n k : ℕ) : CPoly n := if h : k < n then MvPolynomial.X ⟨k,h⟩ else 0

def cvariable (n k : ℕ) : CPoly n := polyVariable n k + MvPolynomial.C Complex.I * polyVariable n (k+1)

def pconj {n : ℕ} (p : CPoly n) : CPoly n := p.map (starRingEnd ℂ)
def preal {n : ℕ} (p : CPoly n) : RPoly n := ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).re
def pimag {n : ℕ} (p : CPoly n) : RPoly n := ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).im
def pnormSq {n : ℕ} (p : CPoly n) : RPoly n := preal p ^ 2 + pimag p ^ 2

def signedPower {n : ℕ} (p : CPoly n) (k : ℤ) : CPoly n :=
  if 0 ≤ k then p ^ k.natAbs else (pconj p) ^ k.natAbs

def clockR (a : DiophantineData) (l : Fin (a.q+a.r)) : CPoly (ns a) := polyVariable (ns a) (4*l.val)
def clockS (a : DiophantineData) (l : Fin (a.q+a.r)) : CPoly (ns a) := polyVariable (ns a) (4*l.val+1)
def zeta (a : DiophantineData) (l : Fin (a.q+a.r)) : CPoly (ns a) := cvariable (ns a) (4*l.val+2)
def oscillator (a : DiophantineData) : CPoly (ns a) := cvariable (ns a) (4*(a.q+a.r))
/-- Within each 34-real-coordinate block: L,C,E,Y, ψ₂,ψ₃,ψ₄,H,T₁,T₂,T₃,T₄,Δ,U,G,G⁺,G⁻. -/
def block (a : DiophantineData) (j : Fin a.q) (k : ℕ) : CPoly (ns a) :=
  cvariable (ns a) (4*(a.q+a.r)+2+34*j.val+2*k)

def Q (a : DiophantineData) (j : Fin a.q) := zeta a (Fin.castAdd a.r j) ^ 4
def chi (a : DiophantineData) (l : Fin a.r) := zeta a (Fin.natAdd a.q l) ^ 4
def V (a : DiophantineData) (j : Fin a.q) := ∏ l, signedPower (chi a l) (a.B l j)
def S (a : DiophantineData) (j : Fin a.q) := ∏ l, signedPower (chi a l) (a.A l j)
def W (a : DiophantineData) (j : Fin a.q) := pconj (Q a j) * S a j

def omega (a : DiophantineData) (l : Fin (a.q+a.r)) : CPoly (ns a) :=
  (primeAt l.val : CPoly (ns a)) * clockR a l

def Omega (a : DiophantineData) (j : Fin a.q) := 4 * omega a (Fin.castAdd a.r j)
def Nu (a : DiophantineData) (j : Fin a.q) := 4 * ∑ l, (a.B l j : CPoly (ns a)) * omega a (Fin.natAdd a.q l)
def recipFrequency (a : DiophantineData) (j : Fin a.q) :=
  -Omega a j + 4 * ∑ l, (a.A l j : CPoly (ns a)) * omega a (Fin.natAdd a.q l)

def modularD {n : ℕ} (b : ℕ → CPoly n) : List (CPoly n) :=
  let L := b 0; let C := b 1; let E := b 2; let Y := b 3
  [MvPolynomial.C (1/3) * L*(E+L+2*C), MvPolynomial.C (1/3)*C*(E-2*L-C),
   MvPolynomial.C (1/6)*(E^2-L^2-L*C-C^2), MvPolynomial.C (1/12)*(E+L-C)*Y]

/-- The six last Jacobi coordinates and four coefficient coordinates of (8.11). -/
def jacobiZ {n : ℕ} (b : ℕ → CPoly n) : List (CPoly n) :=
  let p₂ := b 0; let p₃ := b 1; let p₄ := b 2; let H := b 3
  let T₁ := b 4; let T₂ := b 5; let T₃ := b 6; let T₄ := b 7; let Δ := b 8; let U := b 9
  let κ := H + MvPolynomial.C (1/12)*(p₃^2+p₄^2)
  [0,0,0,0,Δ,U*(Δ*T₂-p₂*T₃*T₄), U*(Δ*T₃-p₃*T₄*T₂), U*(Δ*T₄-p₄*T₂*T₃),
   U*(Δ^2-p₃*p₄*T₂^2)-4*κ*T₁, -U^2*Δ]

def jacobiJ {n : ℕ} (b : ℕ → CPoly n) : List (CPoly n) :=
  let p₂ := b 0; let p₃ := b 1; let p₄ := b 2; let H := b 3
  let T₁ := b 4; let T₂ := b 5; let T₃ := b 6; let T₄ := b 7; let Δ := b 8; let U := b 9
  let κ := H + MvPolynomial.C (1/12)*(p₃^2+p₄^2)
  let quarter : CPoly n := MvPolynomial.C (1/4)
  let half : CPoly n := MvPolynomial.C (1/2)
  let jt₁ := -quarter*Δ^2*U+quarter*p₃*p₄*T₂^2*U+κ*T₁
  let jt := fun pk pn pm Tk Tn Tm => -quarter*Δ^2*U^2*Tk + half*pk*Δ*Tn*Tm*U^2 +
    quarter*(p₃*p₄*T₂^2-pk*pm*Tn^2-pk*pn*Tm^2)*U^2*Tk+κ*Tk
  [2*κ*p₂, 2*(H+MvPolynomial.C (1/12)*(p₂^2-p₄^2))*p₃,
   2*(H-MvPolynomial.C (1/12)*(p₂^2+p₃^2))*p₄,
   2*H^2-MvPolynomial.C (1/144)*(p₂^4+p₃^4+p₄^4),
   jt₁, jt p₂ p₃ p₄ T₂ T₃ T₄, jt p₃ p₄ p₂ T₃ T₄ T₂, jt p₄ p₂ p₃ T₄ T₂ T₃,
   -quarter*Δ^3*U^2+3*(quarter*p₃*p₄*T₂^2*U^2+κ)*Δ-half*p₂*p₃*p₄*T₂*T₃*T₄*U^2,
   -U^2*jt₁]

def splitComplex {n : ℕ} (p : CPoly n) : List (RPoly n) := [preal p, pimag p]

def systemList (a : DiophantineData) (e : ℕ) : List (RPoly (ns a)) :=
  let I : CPoly (ns a) := MvPolynomial.C Complex.I
  let half : CPoly (ns a) := MvPolynomial.C (1/2)
  (List.ofFn (fun l : Fin (a.q+a.r) =>
    [preal (-clockS a l*((primeAt l.val : CPoly (ns a))*clockR a l^2-1)),
     preal (clockR a l*((primeAt l.val : CPoly (ns a))*clockR a l^2-1))] ++
     splitComplex (I*omega a l*zeta a l))).flatten ++
  splitComplex (-4*I*(∑ l, (rhs a e l : CPoly (ns a))*omega a (Fin.natAdd a.q l))*oscillator a) ++
  (List.ofFn (fun j : Fin a.q =>
    ((modularD (block a j)).map (fun p => I*Omega a j*p) ++
    List.zipWith (fun p z => I*Omega a j*p+half*(Omega a j+Nu a j)*z)
      (jacobiJ (fun k => block a j (k+4))) (jacobiZ (fun k => block a j (k+4))) ++
    [MvPolynomial.C (Complex.I/4)*(Omega a j+2*Nu a j)*block a j 14,
     I*half*recipFrequency a j*W a j*(block a j 15)^2,
     -I*half*recipFrequency a j*pconj (W a j)*(block a j 16)^2]).flatMap splitComplex)).flatten

def systemPolys (a : DiophantineData) (e : ℕ) (i : Fin (ns a)) : RPoly (ns a) :=
  (systemList a e)[i.val]?.getD 0

def system (a : DiophantineData) (e : ℕ) := evalField (systemPolys a e)

def outputF (a : DiophantineData) (j : Fin a.q) := block a j 14 * block a j 8

def residuals (a : DiophantineData) : List (RPoly (ns a)) :=
  (List.ofFn (fun l : Fin (a.q+a.r) =>
    [(preal (clockR a l)^2+preal (clockS a l)^2-1)^2, (pnormSq (zeta a l)-1)^2])).flatten ++
  [(pnormSq (oscillator a)-1)^2] ++
  (List.ofFn (fun j : Fin a.q =>
    let b := block a j
    [b 3^4-b 0-b 1, b 4^2-b 0, b 5-b 3^2, b 6^2-b 1, 12*b 7-b 2,
     b 4*b 11^2-b 6*b 9^2-b 5*b 8^2, b 4*b 10^2-b 5*b 9^2-b 6*b 8^2,
     b 13*b 8-1, b 14^4-MvPolynomial.C (lambda : ℂ)*Q a j*V a j^2,
     (1-MvPolynomial.C (eta : ℂ)*W a j)*b 15-1,
     (1-MvPolynomial.C (eta : ℂ)*pconj (W a j))*b 16-1].map pnormSq)).flatten

def moments (a : DiophantineData) : List (CPoly (ns a)) :=
  (List.ofFn (fun j : Fin a.q =>
    let b := block a j; let F := outputF a j
    [b 3-1, b 3*pconj (Q a j)-MvPolynomial.C (2*lambda : ℂ), b 6-1,
     b 4*pconj (zeta a (Fin.castAdd a.r j))^2-MvPolynomial.C (1/4), F-1,
     F*pconj (Q a j)*pconj (V a j)-MvPolynomial.C (lambda : ℂ),
     F*pconj (Q a j)*V a j-MvPolynomial.C (lambda : ℂ)])).flatten

def observed (a : DiophantineData) : CPoly (ns a) :=
  oscillator a * ∏ j, outputF a j * MvPolynomial.C (1-(eta : ℂ)^2)*block a j 15*block a j 16

def testsList (a : DiophantineData) : List (RPoly (ns a)) :=
  residuals a ++ (moments a).flatMap splitComplex ++ splitComplex (observed a)

def nh (a : DiophantineData) : ℕ := (testsList a).length

def testPolys (a : DiophantineData) (i : Fin (nh a)) : RPoly (ns a) := (testsList a)[i.val]
def tests (a : DiophantineData) (x : State (ns a)) : State (nh a) :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval x (testPolys a i))
def ceval {n : ℕ} (p : CPoly n) (x : State n) : ℂ := MvPolynomial.eval (fun i => (x i : ℂ)) p

def ResidualsVanish (a : DiophantineData) (x : ℝ → State (ns a)) : Prop :=
  ∀ t, ∀ p ∈ residuals a, MvPolynomial.eval (x t) p = 0

def MomentsZero (a : DiophantineData) (x : ℝ → State (ns a)) : Prop :=
  ∀ p ∈ moments a, zeroAverage (fun t => ceval p (x t))

def PassesTests (a : DiophantineData) (x : ℝ → State (ns a)) : Prop :=
  ResidualsVanish a x ∧ ∀ i : Fin (nh a), zeroAverage (fun t => (tests a (x t) i : ℂ))

end HGASUndecidable.Main


