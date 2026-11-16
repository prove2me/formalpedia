-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_InverseConstructor
-- name    : PolynomialSampling137_OneThird_Supplement_InverseConstructor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:48:29.027411+00:00
-- url     : https://prove2.me/theorems/48812ac3-3e8e-4565-80fc-07db982622d0
-- title:
--   Deterministic padded inverse-line target
-- statement:
--   Fix $h=2^{16}$. At length $N\ge h$, put $k=\lfloor N/h\rfloor$ and $n=hk$. Use the specified published Shoup constructor for a monic irreducible polynomial of degree $n$. All products are polynomial remainders in its binary polynomial basis. Inversion uses binary repeated squaring, and the subfield basis is computed by deterministic Gaussian elimination on $z\mapsto z^{2^k}+z$.
--
--   $$D_N=\operatorname{Dist}(((\theta+X)^{-1},0^{N-n})),\quad X\sim U(K),\quad K=\{z:z^{2^k}=z\}.$$
--
--   The seed coordinates expand in that computed basis; $\theta$ is the residue class of the polynomial variable. For $N<h$ the map is constant zero. The supplied exponent witness is $\gamma=\tfrac12\min\{\tfrac12-\tfrac5{32}\log_2 9,\tfrac9{512}-\tfrac7{64h}\}$. This definition does not impose small bias on the zero padding, assume a sampling bound or assume the runtime conclusion.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Appendix A.2 Eqs. (48)–(49) and proof of Theorem 22, printed pp. 34–36; PDF pp. 36–38

import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Multiscale
import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

def InverseH : ℕ := 2^16

/-- Fixed deterministic Shoup constructor, unary input and little-endian output.
The published implementation includes its arithmetic and printing costs. -/
def FieldModulus (n : ℕ) : Polynomial (ZMod 2) :=
  MIPRE.LowDegree.polyOfBits (MIPRE.LowDegree.shoupIrreducible (MIPRE.Cost.unary n))

def WordPolynomial {n : ℕ} (x : Word n) : Polynomial (ZMod 2) :=
  ∑ i : Fin n, Polynomial.monomial i.val (x i)

/-- Remainder multiplication in the polynomial basis. A monic degree-n
modulus makes this the actual n-bit quotient-field multiplication. -/
def PolynomialMul (n : ℕ) (f : Polynomial (ZMod 2)) (x y : Word n) : Word n :=
  fun i => ((WordPolynomial x * WordPolynomial y) %ₘ f).coeff i.val

def FastPower {n : ℕ} (mul : Word n → Word n → Word n) (x : Word n) (e : ℕ) : Word n :=
  ((Nat.bits e).reverse).foldl
    (fun z b => if b then mul (mul z z) x else mul z z) (BasisWord n 0)

/-- Binary Gaussian elimination of the graph of a linear map: reduce each
image/domain pair against earlier pivots. Zero image rows give kernel vectors.
All scans and pivot choices have fixed coordinate order. -/
def KernelStep {n : ℕ}
    (state : List (Fin n × Word n × Word n) × List (Word n))
    (row : Word n × Word n) : List (Fin n × Word n × Word n) × List (Word n) :=
  let reduced := state.1.foldl (fun (r : Word n × Word n) (p : Fin n × Word n × Word n) =>
    if r.1 p.1 = 1 then (r.1 + p.2.1, r.2 + p.2.2) else r) row
  match (List.finRange n).find? (fun i => decide (reduced.1 i ≠ 0)) with
  | none => (state.1, state.2 ++ [reduced.2])
  | some i => (state.1 ++ [(i,reduced.1,reduced.2)], state.2)

def KernelBasis {n : ℕ} (L : Word n → Word n) : List (Word n) :=
  (((List.range n).map (fun i => (L (BasisWord n i), BasisWord n i))).foldl
    KernelStep ([],[])).2

def SubfieldBasis (n k : ℕ) : List (Word n) :=
  let mul := PolynomialMul n (FieldModulus n)
  KernelBasis (fun z => FastPower mul z (2^k) + z)

/-- Actual padded inverse-line map (49), with the subfield's deterministic
Gaussian-elimination basis. Inverse at zero is total; θ+X is nonzero here.
For N<h the prescribed target is the point mass at zero. -/
def InverseSampler (N : ℕ) (x : Word (N / InverseH)) : Word N :=
  if N < InverseH then 0 else
    let k := N / InverseH
    let n := InverseH * k
    let bs := SubfieldBasis n k
    let X : Word n := ∑ j : Fin k, (x j) • (bs.getD j.val 0)
    let θ := BasisWord n 1
    let y := FastPower (PolynomialMul n (FieldModulus n)) (θ+X) (2^n-2)
    fun i => if hi : i.val < n then y ⟨i.val,hi⟩ else 0

def InverseLaw (N : ℕ) : Word N → ℝ := samplerMass (InverseSampler N)

def InverseGamma : ℝ :=
  (1/2) * min (1/2 - (5/32) * LogTwo 9) (9/512 - 7/(64*InverseH))

end PolynomialSampling137.OneThird.Supplement


