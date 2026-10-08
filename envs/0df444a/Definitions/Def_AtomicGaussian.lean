-- Prove2me | Definitions.Def_AtomicGaussian
-- name    : AtomicGaussian
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.559987+00:00
-- url     : https://prove2.me/theorems/ad0d1541-eb0d-4600-8815-18429f116545
-- statement:
--   The ambient plane is two-dimensional real Euclidean space. With b=√3/2, the triangular lattice consists of b⁻¹ᐟ²(j+k/2,kb), for integers j,k; its dual consists of vectors having integer inner product with every lattice vector. The Gaussian is exp(−πα‖x‖²), radiality means constancy on equal-norm sets, and the real Fourier transform means the complex Fourier transform of a real function. The atomic construction fixes h=17/50, H=27/50, η=1/5, κ=π/36 and Z=391/1000. Its fifteen residues are 0,1,3,4,7,9,12,13,16,19,21,25,27,28,31 modulo 36. Nodes are positive integers in these residue classes; the distinguished finite nodes are 1,3,4,7,9,12,13,16,19,21, and all remaining nodes are tail nodes. For residue rₐ set pₐ(s)=2 sin(κ(s−rₐ)) and P(s)=∏ₐpₐ(s)². The node basis dₙ is the extended divided difference of P at n, and cₙ is the extended divided difference of dₙ at n. The finite basis functions are Cₐ(s)=4κ²∏ᵣ≠ₐpᵣ(s)² and Dₐ(s)=2κpₐ(s)cos(κ(s−rₐ))∏ᵣ≠ₐpᵣ(s)². Writing φ(s)=exp(πis/18), quadratic factors −φ(rₐ)+2X−φ(−rₐ)X² encode their finite Fourier expansions: their full product supplies coefficients Fⱼ for 0≤j≤30 at frequencies tⱼ=(j−15)/18; the Cₐ coefficient vectors come from 4κ²X times the product omitting factor a, and the Dₐ vectors from iκ(φ(rₐ)−φ(−rₐ)X²) times that omitted product. Define Wₖ(s)=ΣⱼFⱼ(iπtⱼ)ᵏexp(iπtⱼs), Q(n)=Re W₂(n)/2, and D(n)=Re W₃(n)/(6Q(n)). Transformed waves use x(k,t)=(4/3)/(k²+t²), λ(k,t)=(k+it)/(b(k²+t²)), ζ(k,v,t)=−tx(k,t)+i(kx(k,t)−v), and T(k,v,t;s)=λ(k,t)exp(iπζ(k,v,t)s). For a coefficient vector S, its two jets at n are the real parts of ΣⱼQ(n)⁻¹T(k,v,tⱼ;n)Sⱼ multiplied respectively inside the sum by −1 and D(n)−iπζ(k,v,tⱼ). A 20-by-23 matrix evaluates these two jets at the ten finite nodes, with v=H: its first twenty-two columns alternate the Cₐ,Dₐ vectors for 0≤a≤10 with k=H, and its last column uses F with k=h. R consists of columns 2 through 21, and R₀ of columns 0,1,22. An input coefficient record contains a real scalar, eleven finite C and D coefficients, and tail C and D coefficients with summable total absolute value. Its complex radial input at x is exp(−πhb‖x‖²) times the scalar multiple of P plus the tail basis series, evaluated at b‖x‖², together with exp(−πHb‖x‖²) times the finite basis sum. The 20-by-8 target matrix Yf has four diagonal 2-by-2 blocks, for the first four finite nodes n, equal to [Q(1)exp(πηn)/Q(n)] times ((1,0),(πη−D(n),−1)); its other entries vanish. Each 3-by-8 matrix γₛ vanishes except in column 1, whose entries are 11/25,0,−3/500 for side 0 and 11/25,0,3/500 for side 1. Put U₊=(I−R)⁻¹(Yf+R₀(γ₁+γ₀)) and U₋=(I+R)⁻¹(Yf+R₀(γ₁−γ₀)). The side matrices A₀,A₁ place γₛ in rows 0,1,22 and respectively (U₊+U₋)/2 and (U₊−U₋)/2 in the other rows. Finally set z(α)=1/[π(α/b−h)], p(z)=(z,1,ze^(−2/z),e^(−2/z),ze^(−3/z),e^(−3/z),ze^(−6/z),e^(−6/z)), and N(z)=Q(1)ze^(1/z). HasAtomicConstruction(α,f) is the defined proposition that I±R are invertible, the displayed U matrices satisfy their defining linear equations, and two input records exist whose scalars are respectively −3/500 and 3/500, whose zeroth finite C,D coefficients are 11/25,0, and whose interleaved finite coefficients equal the first twenty-two coordinates of Aₛp(z(α)), with corrections only in coordinates 2 through 21. Each side’s correction has sum of absolute values below 10⁻⁵ and its tail coefficients have total absolute sum below 3·10⁻⁹. At every point, f must equal the first complex input plus the Fourier transform of the second, divided by N(z(α)). No parameter range for α or existence of such an f is asserted here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AtomicGaussian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AtomicGaussian.lean; bytes 16..8390
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  (Real.sqrt b)⁻¹ •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
      EuclideanSpace.single 1 ((jk.2 : ℝ) * b))

def A : Set Plane := Set.range triangularPoint

def dualA : Set Plane := {w | ∀ a ∈ A, ∃ n : ℤ, inner ℝ a w = (n : ℝ)}

def gaussian (α : ℝ) (x : Plane) : ℝ := Real.exp (-Real.pi * α * ‖x‖ ^ 2)

def Radial (f : Plane → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → f x = f y

def realFourier (f : Plane → ℝ) (w : Plane) : ℂ := 𝓕 (fun x => (f x : ℂ)) w

end AtomicTriangular

namespace AtomicTriangular.Construction

def b : ℝ := Real.sqrt 3 / 2

def h : ℝ := 17 / 50

def H : ℝ := 27 / 50

def eta : ℝ := 1 / 5

def kappa : ℝ := Real.pi / 36

def residues : Finset ℤ := {0,1,3,4,7,9,12,13,16,19,21,25,27,28,31}

def residue (a : Fin 15) : ℤ := ![0,1,3,4,7,9,12,13,16,19,21,25,27,28,31] a

def Node : Type := {n : ℤ // 0 < n ∧ n % 36 ∈ residues}

def FiniteNodes : Finset ℤ := {1,3,4,7,9,12,13,16,19,21}

def sineFactor (a : Fin 15) (s : ℂ) : ℂ :=
  2 * Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ)))

def P (s : ℂ) : ℂ := ∏ a : Fin 15, (sineFactor a s)^2

def dBasis (n : Node) : ℂ → ℂ := dslope P (n.val : ℂ)

def cBasis (n : Node) : ℂ → ℂ := dslope (dBasis n) (n.val : ℂ)

def finiteC (a : Fin 15) (s : ℂ) : ℂ :=
  4 * (kappa : ℂ)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2

def finiteD (a : Fin 15) (s : ℂ) : ℂ :=
  2 * (kappa : ℂ) * sineFactor a s *
    Complex.cos ((kappa : ℂ) * (s - (residue a : ℂ))) *
      ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2

def phase (s : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * s / 18)

def atomFactor (a : Fin 15) : Polynomial ℂ :=
  -C (phase (residue a)) + C 2 * X - C (phase (-residue a)) * X^2

def atomPolynomial : Polynomial ℂ := ∏ a : Fin 15, atomFactor a

def cAtomPolynomial (a : Fin 15) : Polynomial ℂ :=
  C (4 * (kappa : ℂ)^2) * ∏ r ∈ Finset.univ.erase a, atomFactor r

def dAtomPolynomial (a : Fin 15) : Polynomial ℂ :=
  C (Complex.I * (kappa : ℂ)) *
    (C (phase (residue a)) - C (phase (-residue a)) * X^2) *
      ∏ r ∈ Finset.univ.erase a, atomFactor r

def fourierCoeff (j : Fin 31) : ℂ := atomPolynomial.coeff j.val

def frequency (j : Fin 31) : ℝ := ((j.val : ℝ)-15)/18

def waveDerivative (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : Fin 31, fourierCoeff j * (I*Real.pi*frequency j)^k *
    exp (I*Real.pi*frequency j*s)

def Q (n : ℤ) : ℝ := (waveDerivative 2 n).re / 2

def D (n : ℤ) : ℝ := (waveDerivative 3 n).re / (6 * Q n)

end AtomicTriangular.Construction

namespace AtomicTriangular.FiniteCertificate
open Construction

def cShiftPolynomial (a : Fin 15) : Polynomial ℂ := X * cAtomPolynomial a

def cCoefficient (a : Fin 15) (j : Fin 31) : ℂ := (cShiftPolynomial a).coeff j.val

def dCoefficient (a : Fin 15) (j : Fin 31) : ℂ := (dAtomPolynomial a).coeff j.val

end AtomicTriangular.FiniteCertificate

namespace AtomicTriangular.Construction

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def radial (x : Plane) : ℝ := b*‖x‖^2

def waveDen (k t : ℝ) : ℝ := k^2+t^2

def Xwave (k t : ℝ) : ℝ := (4/3)/waveDen k t

def lambda (k t : ℝ) : ℂ := ((k:ℂ)+I*t)/(b*waveDen k t : ℝ)

def zeta (k v t : ℝ) : ℂ := -(t:ℂ)*(Xwave k t:ℂ)+I*(k*Xwave k t-v:ℝ)

def transformedWave (k v t : ℝ) (s : ℂ) : ℂ := lambda k t*exp (I*Real.pi*zeta k v t*s)

def finiteColumn (col : Fin 23) (j : Fin 31) : ℂ :=
  if hc : col.val<22 then
    if col.val%2=0 then FiniteCertificate.cCoefficient ⟨col.val/2,by omega⟩ j
      else FiniteCertificate.dCoefficient ⟨col.val/2,by omega⟩ j
  else fourierCoeff j

def finiteNode (n : Fin 10) : ℤ := residue ⟨n.val+1,by omega⟩

def jetMultiplier (k v : ℝ) (n : ℤ) (d : Fin 2) (t : ℝ) : ℂ :=
  (Q n:ℂ)⁻¹*transformedWave k v t n *
    (if d.val=0 then -1 else (D n:ℂ)-I*Real.pi*zeta k v t)

def jet (k v : ℝ) (n : ℤ) (d : Fin 2) (S : Fin 31 → ℂ) : ℝ :=
  (∑ j : Fin 31, jetMultiplier k v n d (frequency j)*S j).re

def fullJetMatrix : Matrix (Fin 20) (Fin 23) ℝ := fun i col =>
  jet (if col.val=22 then h else H) H
    (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (finiteColumn col)

def R : Matrix (Fin 20) (Fin 20) ℝ := fun i j => fullJetMatrix i ⟨j.val+2,by omega⟩

def R0 : Matrix (Fin 20) (Fin 3) ℝ := fun i j =>
  fullJetMatrix i (if j.val<2 then ⟨j.val,by omega⟩ else 22)

abbrev TailNode := {n : Node // n.val ∉ FiniteNodes}

structure InputCoefficients where
  C : ℝ
  finiteC : Fin 11 → ℝ
  finiteD : Fin 11 → ℝ
  tailC : TailNode → ℝ
  tailD : TailNode → ℝ
  summable : Summable (fun n => |tailC n|+|tailD n|)

def tailInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  (a.C:ℂ)*P s + ∑' n : TailNode, ((a.tailC n:ℂ)*cBasis n.val s+(a.tailD n:ℂ)*dBasis n.val s)

def finiteInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  ∑ j : Fin 11, ((a.finiteC j:ℂ)*finiteC ⟨j.val,by omega⟩ s +
    (a.finiteD j:ℂ)*finiteD ⟨j.val,by omega⟩ s)

def inputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailInput a (radial x) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteInput a (radial x)

def Z : ℝ := 391/1000

def targetCoefficient (n : Fin 10) : ℝ := Q 1 / Q (finiteNode n) * Real.exp (Real.pi*eta*(finiteNode n))

def Yf : Matrix (Fin 20) (Fin 8) ℝ := fun i j =>
  if i.val<8 then
    targetCoefficient ⟨i.val/2,by omega⟩ *
      (if i.val%2=0 then (if j.val=i.val then 1 else 0)
       else (if j.val=i.val then -1 else if j.val=i.val-1 then Real.pi*eta-D (finiteNode ⟨i.val/2,by omega⟩) else 0))
  else 0

def gamma (side : Fin 2) : Matrix (Fin 3) (Fin 8) ℝ := fun i j =>
  if j.val=1 then (if i.val=0 then 11/25 else if i.val=1 then 0 else if side.val=0 then -(3/500) else 3/500) else 0

def Uplus : Matrix (Fin 20) (Fin 8) ℝ :=
  (1-R)⁻¹*(Yf+R0*(gamma 1+gamma 0))

def Uminus : Matrix (Fin 20) (Fin 8) ℝ :=
  (1+R)⁻¹*(Yf+R0*(gamma 1-gamma 0))

def finiteSolution (side : Fin 2) : Matrix (Fin 20) (Fin 8) ℝ :=
  if side.val=0 then (1/2:ℝ) • (Uplus+Uminus) else (1/2:ℝ) • (Uplus-Uminus)

def Acoefficient (side : Fin 2) : Matrix (Fin 23) (Fin 8) ℝ := fun i j =>
  if hi : i.val<2 then gamma side ⟨i.val,by omega⟩ j
  else if h22 : i.val=22 then gamma side 2 j
  else finiteSolution side ⟨i.val-2,by omega⟩ j

def gaussianZ (α : ℝ) : ℝ := 1/(Real.pi*(α/b-h))

def actualParameter (z : ℝ) : Fin 8 → ℝ :=
  ![z,1,z*Real.exp (-2/z),Real.exp (-2/z),z*Real.exp (-3/z),Real.exp (-3/z),
    z*Real.exp (-6/z),Real.exp (-6/z)]

def normalizingDen (z : ℝ) := Q 1*z*Real.exp (1/z)

end AtomicTriangular.Construction

namespace AtomicTriangular.Construction

def finiteCoordinates (a : InputCoefficients) (i : Fin 22) : ℝ :=
  if i.val % 2 = 0 then a.finiteC ⟨i.val / 2, by omega⟩
  else a.finiteD ⟨i.val / 2, by omega⟩

def HasAtomicConstruction (α : ℝ) (f : Plane → ℝ) : Prop :=
  IsUnit (1 - R) ∧ IsUnit (1 + R) ∧
  (1 - R) * Uplus = Yf + R0 * (gamma 1 + gamma 0) ∧
  (1 + R) * Uminus = Yf + R0 * (gamma 1 - gamma 0) ∧
  ∃ (a : Fin 2 → InputCoefficients) (u : Fin 2 → Fin 20 → ℝ),
    (∀ side,
      (a side).C = (if side.val = 0 then -(3/500) else 3/500) ∧
      (a side).finiteC 0 = 11/25 ∧ (a side).finiteD 0 = 0 ∧
      ∀ i : Fin 22,
        finiteCoordinates (a side) i =
          (∑ j : Fin 8, Acoefficient side ⟨i.val, by omega⟩ j *
            actualParameter (gaussianZ α) j) +
          (if hi : i.val < 2 then 0 else u side ⟨i.val - 2, by omega⟩)) ∧
    (∀ side,
      (∑ i : Fin 20, |u side i|) < 1/10^5 ∧
      Summable (fun n : TailNode => |(a side).tailC n| + |(a side).tailD n|) ∧
      (∑' n : TailNode, (|(a side).tailC n| + |(a side).tailD n|)) < 3/10^9) ∧
    (∀ x : Plane, (f x : ℂ) =
      (inputComplex (a 0) x + 𝓕 (inputComplex (a 1)) x) /
        (normalizingDen (gaussianZ α) : ℂ))

end AtomicTriangular.Construction

namespace AtomicTriangular



end AtomicTriangular
end
end OAI


