-- Prove2me | Definitions.Def_ThomsonN7_core
-- name    : ThomsonN7_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-10T00:58:30.053165+00:00
-- url     : https://prove2.me/theorems/7d44831e-abc0-4c37-a277-2b3c1753e3b8
-- title:
--   Thomson $N=7$ proof package: core definitions (energy, kernels, certificate formats)
-- statement:
--   Core definitions of H. Tran's Lean proof that the pentagonal bipyramid minimises the Coulomb energy of seven points on $S^2$.
--
--   1. **Configurations and energy.** `R3` is Euclidean 3-space, `SphereConfig n` the set of injective maps $x:\{0,\dots,n-1\}\to S^2$, and `coulombEnergy x` $=\sum_{i<j}\|x_i-x_j\|^{-1}$. `pentBipyramid` lists the regular pentagon $(\cos\tfrac{2\pi k}5,\sin\tfrac{2\pi k}5,0)$, $k=0,\dots,4$, followed by the north and south poles.
--   2. **Kernels.** `phi` is $\varphi(t)=(2-2t)^{-1/2}$, so that $\|x-y\|^{-1}=\varphi(\langle x,y\rangle)$ for unit vectors; `c1`, `c2` are the two ring–ring inner products $\cos\tfrac{2\pi}5,\cos\tfrac{4\pi}5$ of the bipyramid. `ThreePoint.Y3`, `S3`, `Sk` are the three-point kernels of the semidefinite method on $S^2$, `GramOK u v t` says that $(u,v,t)$ is the off-diagonal part of a PSD $3\times3$ Gram matrix with unit diagonal, and `lamA`, `lamB`, `lamG` are the typed slack functions.
--   3. **Exact certificate formats.** Integer polynomial expressions (`Kron.Ex`), block-matrix encodings (`Cert.Blk`, `Cert.SBlk`, `Cert.TBlk`), the three-point certificate records `Cert.Cert3` and `Cert.TCert` and their Boolean checkers, and the one-dimensional interval certificates (`SlabOneD`, `CutOneD`), all designed to be checked by kernel computation.
--   4. **Cell specifications.** `Glue.cls3` assigns to each pair of a minimal-pair configuration its type (minimal pair, pairs meeting it, the rest); `Glue.SlabSpec lo hi` and `Glue.CapSpec a0` are the slab and cap specifications of paper §7, and `Glue.Concl y` is the per-configuration conclusion of the theorem.
--   5. **Local analysis.** Gram windows (`LocalGram`, `LocalGramA`, `InWindow`), local minimality (`LocalMinAt`), the tube-rigidity predicate `TubeRigid`, and the relabelling `T4.sig7` used in the rigidity argument (with its injectivity lemma, needed by a definition).
--
--   These definitions are shared by the solution files of the seven cell lemmas of the mission's decomposition (Case 1, the cap, five slabs).
--
--   **Formalization Note** The code is taken verbatim from the source file, restricted to the declarations needed here; the only edits for this Lean/Mathlib version are the lemma renames `ite_eq_left`→`if_pos`, `ite_eq_right`→`if_neg` and one rewrite of `IsHermitian.isSymm`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package (snapshot 2026-09-27), https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53, file formal/lean/ThomsonN7/Solution.lean (lines 1–15100, definitions only; paper/PAPER.md §2–§8)

import Mathlib

/-!
# Thomson problem for N = 7 (and the D3h stretch target for N = 9)

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`.

* `N = 7`: the unique minimiser (up to `O(3)` and relabelling) is the regular pentagonal bipyramid,
  with `E = 1/2 + 5√2 + 5/(2 sin(π/5)) + 5/(2 sin(2π/5)) = 14.452977414…`.
* `N = 9`: the (numerically known) minimiser is the D3h tricapped trigonal prism, which has one free
  parameter `z` (the height of the two triangular faces); numerically `z ≈ 0.70365`,
  `E ≈ 25.759986531`.
-/

open Real

namespace ThomsonN7

/-- Euclidean 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `n` pairwise distinct points on the unit sphere of `ℝ³`.
Injectivity is essential: with `1 / 0 = 0` in Lean, coincident points would otherwise be free. -/
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

/-- Coulomb (Riesz `s = 1`) energy `∑_{i<j} 1 / ‖x i - x j‖`. -/
noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- The point with cylindrical coordinates `(ρ, θ, h)`. -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

/-- The regular pentagonal bipyramid: indices `0..4` are the equatorial pentagon
(angles `2πk/5`), index `5` is the north pole and index `6` the south pole. -/
noncomputable def pentBipyramid : Fin 7 → R3 := fun i =>
  if (i : ℕ) < 5 then cyl 1 (2 * π * (i : ℕ) / 5) 0
  else if (i : ℕ) = 5 then cyl 0 0 1
  else cyl 0 0 (-1)

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

/- BEGIN M0 -/
namespace Base

open Finset

/-- The pair potential as a function of the inner product `t = ⟪x, y⟫` of two unit vectors:
`‖x - y‖⁻¹ = phi t`. -/
noncomputable def phi (t : ℝ) : ℝ := (√(2 - 2 * t))⁻¹

/-! ### Invariance -/

/-! ### Gram values of the pentagonal bipyramid -/

/-- `cos (2π/5)`. -/
noncomputable def c1 : ℝ := (√5 - 1) / 4

/-- `cos (4π/5)`. -/
noncomputable def c2 : ℝ := -(1 + √5) / 4

end Base
/- END M0 -/

/- BEGIN M1 -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

/-! # Bachoc–Vallentin three-point positivity on `S²` (any block size, any `k`)

`Q3 k u v t = ((1-u²)(1-v²))^{k/2} T_k((t-uv)/√((1-u²)(1-v²)))` via the Chebyshev recursion.
-/

/-- `Q_k(u,v,t)`: `Q_0 = 1`, `Q_1 = t - uv`,
`Q_{k+2} = 2 (t-uv) Q_{k+1} - (1-u²)(1-v²) Q_k`. -/
noncomputable def Q3 : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * Q3 (k + 1) u v t - (1 - u ^ 2) * (1 - v ^ 2) * Q3 k u v t

/-- `Y_k(u,v,t)_{ab} = uᵃ vᵇ Q_k(u,v,t)`, `a, b < m`. -/
noncomputable def Y3 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => u ^ (a : ℕ) * v ^ (b : ℕ) * Q3 k u v t

/-- The Bachoc–Vallentin matrix `S_k = (1/6) Σ_{σ ∈ S₃} Y_k ∘ σ`, symmetric in `(u,v,t)`. -/
noncomputable def S3 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 6 : ℝ) •
    (Y3 m k u v t + Y3 m k u t v + Y3 m k v u t + Y3 m k v t u + Y3 m k t u v + Y3 m k t v u)

/-- The Frobenius pairing `⟨A, B⟩ = Σ_{ab} A_{ab} B_{ab}`. -/
def matDot {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ a, ∑ b, A a b * B a b

/-! ### Addition theorem (de Moivre) -/

/-! ### Combinatorics of ordered triple sums -/

section Comb

variable {n : ℕ}

/-- Sum over ordered triples of pairwise distinct indices. -/
def dsum (f : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l, if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0

end Comb

section Comb2

variable {n : ℕ}

end Comb2

section Comb3

variable {n : ℕ}

end Comb3

section Comb4

variable {n : ℕ}

/-- The scalar reduced kernel: the marginal terms are chosen so that the sum over ordered
distinct triples is `(n - 2)` times the sum over all triples. -/
noncomputable def Rs (s : ℝ → ℝ → ℝ → ℝ) (n : ℕ) (u v t : ℝ) : ℝ :=
  ((n : ℝ) - 2) * s u v t + (s u u 1 + s v v 1 + s t t 1) + s 1 1 1 / ((n : ℝ) - 1)

end Comb4

section Final

variable {n : ℕ}

/-- The region of triples `(u, v, t)` of inner products of three unit vectors of `ℝ³`
(Gram matrix positive semidefinite). -/
def GramOK (u v t : ℝ) : Prop :=
  u ^ 2 ≤ 1 ∧ v ^ 2 ≤ 1 ∧ t ^ 2 ≤ 1 ∧ 0 ≤ 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2

/-- The reduced matrix kernel `R_k` for `n` points. -/
noncomputable def Rk (n m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((n : ℝ) - 2) • S3 m k u v t + (S3 m k u u 1 + S3 m k v v 1 + S3 m k t t 1)
    + (1 / ((n : ℝ) - 1)) • S3 m k 1 1 1

end Final

/-! ### The kernels at the diagonal `(1,1,1)` -/

section FinalZ

variable {n : ℕ}

end FinalZ

/- BEGIN M5 -/
section Critical

end Critical

section Critical

end Critical

section Critical

end Critical

section CriticalZ

variable {n : ℕ}

end CriticalZ

section CriticalZsym

variable {n : ℕ}

section Perm

variable (τ : Fin n → Fin n → ℝ) (hτ : ∀ i j, τ j i = τ i j) (f : ℝ → ℝ → ℝ → ℝ)

include hτ

end Perm

end CriticalZsym

section CriticalFinal

variable {n : ℕ}

end CriticalFinal

/- END M5 -/

end ThreePoint

/- BEGIN CERT3 -/

/-!
# Kronecker-substitution checking of polynomial identities

A polynomial `e : Ex` in three variables `u, v, t` with integer coefficients is given as an
expression tree.  To prove `∀ u v t : ℝ, e(u,v,t) = 0` it suffices to check, with kernel
(GMP) integer arithmetic, that
* every exponent of every variable is `< D`,
* the `ℓ¹`-norm of the (uncollected) coefficients is `< 2^w`,
* the value of `e` at the integers `u = 2^w`, `v = 2^(w D)`, `t = 2^(w D²)` is `0`.
-/

namespace Kron

/-- Polynomial expressions in three variables with integer coefficients. -/
inductive Ex where
  | c : ℤ → Ex
  | mon : ℕ → ℕ → ℕ → Ex
  | add : Ex → Ex → Ex
  | mul : Ex → Ex → Ex

namespace Ex

/-- Real value at `(u, v, t)`. -/
noncomputable def ev (u v t : ℝ) : Ex → ℝ
  | c n => (n : ℝ)
  | mon a b d => u ^ a * v ^ b * t ^ d
  | add p q => ev u v t p + ev u v t q
  | mul p q => ev u v t p * ev u v t q

/-- Integer value at the Kronecker point `u = 2^w, v = 2^(w D), t = 2^(w D²)`. -/
def kev (w D : ℕ) : Ex → ℤ
  | c n => n
  | mon a b d => ((2 ^ (w * (a + D * b + D * D * d)) : ℕ) : ℤ)
  | add p q => kev w D p + kev w D q
  | mul p q => kev w D p * kev w D q

/-- The `ℓ¹`-norm of the uncollected coefficients. -/
def l1 : Ex → ℕ
  | c n => n.natAbs
  | mon _ _ _ => 1
  | add p q => l1 p + l1 q
  | mul p q => l1 p * l1 q

/-- Degree in `u`. -/
def dx : Ex → ℕ
  | c _ => 0
  | mon a _ _ => a
  | add p q => max (dx p) (dx q)
  | mul p q => dx p + dx q

/-- Degree in `v`. -/
def dy : Ex → ℕ
  | c _ => 0
  | mon _ b _ => b
  | add p q => max (dy p) (dy q)
  | mul p q => dy p + dy q

/-- Degree in `t`. -/
def dz : Ex → ℕ
  | c _ => 0
  | mon _ _ d => d
  | add p q => max (dz p) (dz q)
  | mul p q => dz p + dz q

/-- A term `(coefficient, exponents)`. -/
abbrev Term := ℤ × ℕ × ℕ × ℕ

/-- The uncollected list of terms of an expression. -/
def toList : Ex → List Term
  | c n => [(n, 0, 0, 0)]
  | mon a b d => [(1, a, b, d)]
  | add p q => toList p ++ toList q
  | mul p q => (toList p).flatMap fun x => (toList q).map fun y =>
      (x.1 * y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)

end Ex

/-- The value of a list of terms under a weight function. -/
def sumT {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R) (L : List Ex.Term) : R :=
  (L.map fun x => (x.1 : R) * W x.2.1 x.2.2.1 x.2.2.2).sum

namespace Ex

/-- Generic evaluation under a weight function `W` on exponent triples. -/
def evalW {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R) : Ex → R
  | c n => (n : R)
  | mon a b d => W a b d
  | add p q => evalW W p + evalW W q
  | mul p q => evalW W p * evalW W q

/-- The real weight `u^a v^b t^d`. -/
noncomputable def Wr (u v t : ℝ) (a b d : ℕ) : ℝ := u ^ a * v ^ b * t ^ d

/-- The Kronecker weight `2^(w (a + D b + D² d))`. -/
def Wk (w D a b d : ℕ) : ℤ := ((2 ^ (w * (a + D * b + D * D * d)) : ℕ) : ℤ)

/-- Sum of absolute values of coefficients of a term list. -/
def sumAbs (L : List Term) : ℕ := (L.map fun x => x.1.natAbs).sum

end Ex

open Ex

/-- The base-`D` code of the exponent triple of a term. -/
def code (D : ℕ) (x : Term) : ℕ := x.2.1 + D * x.2.2.1 + D * D * x.2.2.2

/-- The collected coefficient of the monomial with code `k`. -/
def coefk (D : ℕ) : List Term → ℕ → ℤ
  | [], _ => 0
  | x :: L, k => (if code D x = k then x.1 else 0) + coefk D L k

end Kron

/-! ## Builders for `Ex` with evaluation lemmas -/

namespace Kron
namespace Ex

/-- The variable `u`. -/
def U : Ex := mon 1 0 0

/-- The variable `v`. -/
def V : Ex := mon 0 1 0

/-- The variable `t`. -/
def T : Ex := mon 0 0 1

/-- Negation. -/
def neg (e : Ex) : Ex := mul (c (-1)) e

/-- Subtraction. -/
def sub (e f : Ex) : Ex := add e (neg f)

/-- Scalar multiple by an integer. -/
def smul (a : ℤ) (e : Ex) : Ex := mul (c a) e

/-- Square. -/
def sq (e : Ex) : Ex := mul e e

/-- Sum of a list of expressions (right nested). -/
def sumE (l : List Ex) : Ex := l.foldr add (c 0)

/-- Sum of `f 0, …, f (r-1)`. -/
def sumRange (r : ℕ) (f : ℕ → Ex) : Ex := sumE ((List.range r).map f)

variable (u v t : ℝ)

/-! ### Substitution of variables by variables or `1` -/

/-- Value of the variable with code `i`. -/
def varVal : ℕ → ℝ
  | 0 => u
  | 1 => v
  | 2 => t
  | _ => 1

end Ex
end Kron

/- BEGIN CERT1 -/
section Cert1Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## `Q_k` as a polynomial expression -/

/-- `Q_k` as an expression. -/
def q3E : ℕ → Ex
  | 0 => c 1
  | 1 => sub T (mul U V)
  | k + 2 => sub (mul (smul 2 (sub T (mul U V))) (q3E (k + 1)))
      (mul (mul (sub (c 1) (sq U)) (sub (c 1) (sq V))) (q3E k))

/-! ## Quadratic forms: `L D Lᵀ` plus a diagonally dominant remainder -/

/-! ## Integer data of a positive semidefinite block -/

/-- Integer data of the block `M = ∑_q d_q l_q l_qᵀ + Δ`: pivots `d`, columns `l`, remainder `Δ`. -/
structure Blk where
  d : List ℤ
  l : List (List ℤ)
  Δ : List (List ℤ)

namespace Blk

/-- Pivot `q`. -/
def dq (b : Blk) (q : ℕ) : ℤ := b.d.getD q 0

/-- Entry `a` of column `q`. -/
def lq (b : Blk) (q a : ℕ) : ℤ := (b.l.getD q []).getD a 0

/-- Entry `(a, c)` of the remainder. -/
def del (b : Blk) (a c : ℕ) : ℤ := (b.Δ.getD a []).getD c 0

/-- The integer Gram matrix entry `∑_q d_q l_qa l_qc + Δ_ac` (`q < r`). -/
def ent (r : ℕ) (b : Blk) (a c : ℕ) : ℤ :=
  ((List.range r).map fun q => b.dq q * b.lq q a * b.lq q c).sum + b.del a c

/-- The computable check: pivots nonnegative, `Δ` symmetric and diagonally dominant. -/
def ok (r : ℕ) (b : Blk) : Bool :=
  (List.range r).all fun i =>
    decide (0 ≤ b.dq i) &&
    (List.range r).all (fun j => decide (b.del i j = b.del j i)) &&
    decide (((List.range r).map fun j => if i = j then (0 : ℤ) else |b.del i j|).sum ≤ b.del i i)

end Blk

end Cert

end Cert1Block

/- BEGIN CERT3FILE -/
section Cert3Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## Helpers: zero-skipping scaling, monomial-preserving substitution -/

/-- `a * e`, skipping the multiplication when `a = 0`. -/
def smulNZ (a : ℤ) (e : Ex) : Ex := if a = 0 then c 0 else smul a e

/-- Substitute the variables with codes `(i, j, k)` (`0, 1, 2 ↦ u, v, t`, otherwise `1`) for
`(u, v, t)`, monomial by monomial (so that no products of large monomials arise). -/
def sbst (i j k : ℕ) : Ex → Ex
  | .c n => .c n
  | .mon a b d =>
    .mon ((if i = 0 then a else 0) + (if j = 0 then b else 0) + (if k = 0 then d else 0))
      ((if i = 1 then a else 0) + (if j = 1 then b else 0) + (if k = 1 then d else 0))
      ((if i = 2 then a else 0) + (if j = 2 then b else 0) + (if k = 2 then d else 0))
  | .add p q => .add (sbst i j k p) (sbst i j k q)
  | .mul p q => .mul (sbst i j k p) (sbst i j k q)

/-! ## The `F`-blocks: `Λ · Fp(u,v)` -/

/-- `Λ · Fp(u, v)` for the block `F = M / Λ`, as an expression. -/
def fpE (r : ℕ) (b : Blk) : Ex :=
  add (sumRange r fun q => smulNZ (b.dq q)
        (mul (sumRange r fun a => smulNZ (b.lq q a) (mon a 0 0))
             (sumRange r fun a => smulNZ (b.lq q a) (mon 0 a 0))))
      (sumRange r fun a => sumRange r fun c => smulNZ (b.del a c) (mon a c 0))

/-! ## Block matrices and their quadratic forms -/

/-- `Λ · Fp_k(u,v,t)`, where `Fp_k = ∑_{ab} F_{ab} uᵃ vᵇ Q_k`. -/
def fkE (r : ℕ) (b : Blk) (k : ℕ) : Ex := mul (fpE r b) (q3E k)

/-- The real matrix of an `F`-block: `(∑_q d_q l_q l_qᵀ + Δ) / Λ`. -/
noncomputable def fmat (r Lam : ℕ) (b : Blk) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun a c => (b.ent r a c : ℝ) / Lam

/-! ## Symmetrisation and the `F`-part of the identity -/

/-- The sum over the six orderings of the arguments. -/
def six (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  f x y z + f x z y + f y x z + f y z x + f z x y + f z y x

/-- The six-fold sum of `e` at the variables with codes `(i, j, k)`. -/
def sixE (i j k : ℕ) (e : Ex) : Ex :=
  add (add (add (add (add (sbst i j k e) (sbst i k j e)) (sbst j i k e)) (sbst j k i e))
    (sbst k i j e)) (sbst k j i e)

/-- The `F`-part of the identity, `6 (n-1) Λ ∑_k ⟨F_k, R_k⟩`, from the expressions
`Λ · Fp_k` (`fs k`). -/
def ftotE (n K : ℕ) (fs : ℕ → Ex) : Ex :=
  sumRange K fun k =>
    add (add (smul (((n : ℤ) - 1) * ((n : ℤ) - 2)) (sixE 0 1 2 (fs k)))
      (smul ((n : ℤ) - 1) (add (add (sixE 0 0 3 (fs k)) (sixE 1 1 3 (fs k)))
        (sixE 2 2 3 (fs k)))))
      (sixE 3 3 3 (fs k))

/-- The value of the `k`-th summand of `ftotE`. -/
noncomputable def ftotTerm (n : ℕ) (g : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  ((n : ℝ) - 1) * ((n : ℝ) - 2) * six g u v t
    + ((n : ℝ) - 1) * (six g u u 1 + six g v v 1 + six g t t 1) + six g 1 1 1

/-! ## SOS blocks with multipliers -/

/-- The exponent triple of the `a`-th basis monomial. -/
def zt (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) : ℕ × ℕ × ℕ := zs.getD a (0, 0, 0)

/-- The `a`-th basis monomial as an expression. -/
def zmon (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) : Ex := mon (zt zs a).1 (zt zs a).2.1 (zt zs a).2.2

/-- The product of the `a`-th and `c`-th basis monomials, as a single monomial. -/
def zzmon (zs : List (ℕ × ℕ × ℕ)) (a c : ℕ) : Ex :=
  mon ((zt zs a).1 + (zt zs c).1) ((zt zs a).2.1 + (zt zs c).2.1) ((zt zs a).2.2 + (zt zs c).2.2)

/-- The value of the `a`-th basis monomial. -/
noncomputable def zval (zs : List (ℕ × ℕ × ℕ)) (u v t : ℝ) (a : ℕ) : ℝ :=
  u ^ (zt zs a).1 * v ^ (zt zs a).2.1 * t ^ (zt zs a).2.2

/-- The quadratic form `∑_q d_q (l_q · z)² + zᵀ Δ z` of a block in the monomials `zs`. -/
def sqfE (b : Blk) (zs : List (ℕ × ℕ × ℕ)) : Ex :=
  add (sumRange zs.length fun q => smulNZ (b.dq q)
        (Ex.sq (sumRange zs.length fun a => smulNZ (b.lq q a) (zmon zs a))))
      (sumRange zs.length fun a => sumRange zs.length fun c =>
        smulNZ (b.del a c) (zzmon zs a c))

/-- Gram triples inside the cut `a = an / ad`: all three entries are `≥ a` (the plain case is
`an = -1`, `ad = 1`). -/
def GramCut (an : ℤ) (ad : ℕ) (u v t : ℝ) : Prop :=
  GramOK u v t ∧ (an : ℝ) ≤ ad * u ∧ (an : ℝ) ≤ ad * v ∧ (an : ℝ) ≤ ad * t

/-- The multiplier with code `j`: `1-u²`, `1-v²`, `1-t²`, the Gram determinant, `1∓u`, `1∓v`,
`1∓t` (codes `0`-`9`), and the cut multipliers `ad·u-an`, `ad·v-an`, `ad·t-an` (codes `10`-`12`);
every other code is the constant `1`. -/
def codeE (an : ℤ) (ad : ℕ) : ℕ → Ex
  | 0 => sub (c 1) (Ex.sq U)
  | 1 => sub (c 1) (Ex.sq V)
  | 2 => sub (c 1) (Ex.sq T)
  | 3 => sub (add (c 1) (smul 2 (mul U (mul V T)))) (add (Ex.sq U) (add (Ex.sq V) (Ex.sq T)))
  | 4 => sub (c 1) U
  | 5 => add (c 1) U
  | 6 => sub (c 1) V
  | 7 => add (c 1) V
  | 8 => sub (c 1) T
  | 9 => add (c 1) T
  | 10 => sub (smul ad U) (c an)
  | 11 => sub (smul ad V) (c an)
  | 12 => sub (smul ad T) (c an)
  | _ => c 1

/-- The product of the multipliers with the given codes (`[]` is `1`). -/
def gE (an : ℤ) (ad : ℕ) (g : List ℕ) : Ex :=
  g.foldr (fun code acc => mul (codeE an ad code) acc) (c 1)

/-- The variable permutation with code `s` (`0, …, 5`), as a triple of variable codes. -/
def perm3 : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 1, 2)
  | 1 => (0, 2, 1)
  | 2 => (1, 0, 2)
  | 3 => (1, 2, 0)
  | 4 => (2, 0, 1)
  | _ => (2, 1, 0)

/-- An SOS block: multiplier codes `g`, variable permutation `σ`, monomial basis `z`, and the
positive semidefinite Gram data `B`. -/
structure SBlk where
  g : List ℕ
  σ : ℕ
  z : List (ℕ × ℕ × ℕ)
  B : Blk

/-- The polynomial `Λ · g(σx) · (zᵀ S z)(σx)` of an SOS block. -/
def sblkE (an : ℤ) (ad : ℕ) (s : SBlk) : Ex :=
  sbst (perm3 s.σ).1 (perm3 s.σ).2.1 (perm3 s.σ).2.2 (mul (gE an ad s.g) (sqfE s.B s.z))

/-! ## The certificate and its soundness -/

open scoped RealInnerProductSpace

/-- The empty block. -/
def Blk.empty : Blk := ⟨[], [], []⟩

/-- The polynomial `∑_j h_j (u^j + v^j + t^j)`. -/
def hE (h : List ℤ) : Ex :=
  sumRange h.length fun j => smulNZ (h.getD j 0) (add (add (mon j 0 0) (mon 0 j 0)) (mon 0 0 j))

/-- A three-point certificate for `n` points: `H(x) = ∑_j h_j x^j / Λ`, `e = eps / Λ`, the cut
`a = an / ad` (`an = -1`, `ad = 1` for no cut), the `F`-blocks `F_k` (in the basis `uᵃ vᵇ Q_k`) and
the SOS blocks, all over the common denominator `Λ = Lam`. -/
structure Cert3 where
  n : ℕ
  Lam : ℕ
  an : ℤ
  ad : ℕ
  h : List ℤ
  eps : ℤ
  F : List Blk
  S : List SBlk

namespace Cert3

/-- The `k`-th `F`-block. -/
def blk (cf : Cert3) (k : ℕ) : Blk := cf.F.getD k Blk.empty

/-- The size of the `k`-th `F`-block. -/
def m (cf : Cert3) (k : ℕ) : ℕ := (cf.blk k).Δ.length

/-- The number of `F`-blocks. -/
def K (cf : Cert3) : ℕ := cf.F.length

/-- The `k`-th `F`-matrix. -/
noncomputable def Fm (cf : Cert3) (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blk k)

/-- The polynomial minorant `H`. -/
noncomputable def Hf (cf : Cert3) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range cf.h.length, (cf.h.getD j 0 : ℝ) * x ^ j) / cf.Lam

/-- The polynomial identity, scaled by `6 (n-1) C(n,2) Λ`, as an expression. -/
def idE (cf : Cert3) : Ex :=
  sub (sub (sub (smul (2 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (hE cf.h))
        (c (6 * ((cf.n : ℤ) - 1) * cf.eps)))
      (smul (cf.n.choose 2 : ℕ) (ftotE cf.n cf.K fun k => fkE (cf.m k) (cf.blk k) k)))
    (smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (sumE (cf.S.map (sblkE cf.an cf.ad))))

end Cert3

/-- The Kronecker check that an expression vanishes identically. -/
def chk (e : Ex) : Bool :=
  decide (e.kev (Nat.log2 e.l1 + 1) (max e.dx (max e.dy e.dz) + 1) = 0)

namespace Cert3

/-- The computable check. -/
def check (cf : Cert3) : Bool :=
  decide (3 ≤ cf.n) && decide (0 < cf.Lam) && decide (0 < cf.ad) &&
  (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) &&
  cf.S.all (fun s => s.B.ok s.z.length) && chk cf.idE

end Cert3

namespace Cert3

end Cert3

end Cert

end Cert3Block

/- END CERT3 -/

/- BEGIN M2 -/
namespace M2

/-! ## The number field `ℚ(√2, 2 sin (π/5))` -/

/-- Elements `∑ x_(4i+j) a^i b^j` of `ℚ(a, b)`, `a = √2`, `b = 2 sin (π/5)`. -/
structure K8 where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ
  x6 : ℚ
  x7 : ℚ
  deriving DecidableEq

namespace K8

/-! ### Rational enclosures and positivity of elements of `K8` -/

end K8

namespace K8

end K8

/-! ### Polynomials with `K8` coefficients: dense lists, lowest degree first -/

namespace Pl

end Pl

open Pl

end M2
/- END M2 -/

/- BEGIN M3 -/
namespace M3

open scoped InnerProductSpace

/-- colour of the pair (k,l) in the pentagonal bipyramid (0:-1, 1:a, 2:0, 3:b) -/
def cP (k l : Fin 7) : Fin 4 :=
  if k.val < 5 ∧ l.val < 5 then
    (if (k.val + 5 - l.val) % 5 = 1 ∨ (l.val + 5 - k.val) % 5 = 1 then 3 else 1)
  else if k.val = 5 ∧ l.val = 6 then 0
  else if k.val = 6 ∧ l.val = 5 then 0
  else 2

/-- The Gram determinant of four unit vectors, written with a free diagonal entry `δ` so that it
is homogeneous of degree four. -/
def det4h {R : Type*} [CommRing R] (δ p01 p02 p03 p12 p13 p23 : R) : R :=
  δ ^ 4 - δ ^ 2 * (p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2)
    + (p01 ^ 2 * p23 ^ 2 + p02 ^ 2 * p13 ^ 2 + p03 ^ 2 * p12 ^ 2)
    + 2 * δ * (p01 * p12 * p02 + p01 * p13 * p03 + p02 * p23 * p03 + p12 * p23 * p13)
    - 2 * (p01 * p02 * p13 * p23 + p01 * p03 * p12 * p23 + p02 * p03 * p12 * p13)

/-- `cos (4π/5) = -(1 + √5)/4`, the second contact value. -/
noncomputable def cosA : ℝ := -(1 + √5) / 4

/-- `cos (2π/5) = (√5 - 1)/4`, the fourth contact value. -/
noncomputable def cosB : ℝ := (√5 - 1) / 4

/-- The four contact values `-1, cos (4π/5), 0, cos (2π/5)` indexed by `Fin 4`. -/
noncomputable def val : Fin 4 → ℝ := ![-1, cosA, 0, cosB]

end M3

/- BEGIN P3ext -/

/-! ## P3: Bregman (Taylor) lower bounds for the Coulomb pair potential (agent7) -/

namespace Base

end Base

/- END P3ext -/

/- BEGIN P1 -/

/-! ## P1: the bipyramid is a critical point of the Coulomb energy on the constraint set (agent7) -/

namespace Reg

open Base

/-- `sin (2π/5)`. -/
noncomputable def s1 : ℝ := sin (2 * π / 5)
/-- `sin (4π/5)`. -/
noncomputable def s2 : ℝ := sin (4 * π / 5)

/-- Pair weights `φ'(⟪P_i, P_j⟫) = φ(⟪P_i, P_j⟫)³` of the bipyramid (zero on the diagonal). -/
noncomputable def W (i j : Fin 7) : ℝ :=
  if i = j then 0 else phi (inner ℝ (pentBipyramid i) (pentBipyramid j)) ^ 3

/-- Lagrange multiplier of the unit-norm constraint at vertex `i` of the bipyramid. -/
noncomputable def muP (i : Fin 7) : ℝ :=
  ∑ j, W i j * inner ℝ (pentBipyramid i) (pentBipyramid j)

end Reg

/- END P1 -/

/- BEGIN GAUGE -/

/-! ## G: gauge (Procrustes) lemma `exists_gauge` (agent7) -/

namespace Reg

open scoped RealInnerProductSpace

/-- Rotation by the angle `(c, s)` (`c² + s² = 1`) in the plane spanned by orthonormal `u, v`. -/
noncomputable def planeRot (u v : R3) (c s : ℝ) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3
    + (c - 1) • ((innerSL ℝ u).smulRight u + (innerSL ℝ v).smulRight v)
    + s • ((innerSL ℝ u).smulRight v - (innerSL ℝ v).smulRight u)

/-- The linear isometries of `ℝ³`, as a subset of the continuous linear maps. -/
def IsoSet : Set (R3 →L[ℝ] R3) := {A | ∀ x, ‖A x‖ = ‖x‖}

/-- Procrustes score `A ↦ ∑ᵢ ⟪P i, A (y i)⟫`. -/
noncomputable def procScore {n : ℕ} (P y : Fin n → R3) (A : R3 →L[ℝ] R3) : ℝ :=
  ∑ i, ⟪P i, A (y i)⟫

/-- A linear isometry (as a continuous linear map) upgraded to an isometry equivalence. -/
noncomputable def isoOfMem (A : R3 →L[ℝ] R3) (hA : A ∈ IsoSet) : R3 ≃ₗᵢ[ℝ] R3 :=
  LinearIsometry.toLinearIsometryEquiv { toLinearMap := A.toLinearMap, norm_map' := hA } rfl

end Reg

/- END GAUGE -/

/- BEGIN P2 -/

/- BEGIN RegB (P2: exact energy identity; needs M0 = namespace Base and the Challenge preamble) -/
namespace RegB

open Base Finset

section vectors

variable (y : Fin 7 → R3)

end vectors

end RegB
/- END RegB -/

/- END P2 -/

/- BEGIN GV -/

namespace GV

open Base

open scoped InnerProductSpace

/-- The (2,2) entry of the Cholesky factor of a unit-diagonal Gram matrix. -/
noncomputable def L22 (g01 : ℝ) : ℝ := √(1 - g01 ^ 2)

/-- The (3,2) entry of the Cholesky factor. -/
noncomputable def L32 (g01 g05 g15 : ℝ) : ℝ := (g15 - g01 * g05) / L22 g01

/-- The (3,3) entry of the Cholesky factor. -/
noncomputable def L33 (g01 g05 g15 : ℝ) : ℝ := √(1 - g05 ^ 2 - L32 g01 g05 g15 ^ 2)

/-- Lower-triangular frame with the prescribed Gram matrix `[[1,g01,g05],[g01,1,g15],[g05,g15,1]]`. -/
noncomputable def frame (g01 g05 g15 : ℝ) : Fin 3 → R3 :=
  ![!₂[1, 0, 0], !₂[g01, L22 g01, 0], !₂[g05, L32 g01 g05 g15, L33 g01 g05 g15]]

end GV

/- END GV -/

/- BEGIN TWOREGIME -/

namespace TwoRegime

open scoped InnerProductSpace

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- **Local statement** (radius `d`, sup-norm): every unit configuration within `d` of the
labelled `P` has energy at least `E(P)`, with equality only on the `O(3)`-orbit of `P`. -/
def LocalMinAt (d : ℝ) : Prop :=
  ∀ z ∈ SphereConfig 7, (∀ i, ‖z i - pentBipyramid i‖ ≤ d) →
    coulombEnergy pentBipyramid ≤ coulombEnergy z ∧
    (coulombEnergy z = coulombEnergy pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (pentBipyramid i))

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- **Local statement, Gram-window form.** Every unit configuration whose off-diagonal Gram
entries are within the window `ω (⟪P i, P j⟫)` of those of the labelled `P` has energy at least
`E(P)`, with equality only on the `O(3)`-orbit of `P`.  The window is allowed to depend on the
nominal value `⟪P i, P j⟫ ∈ {-1, 0, c₁, c₂}` of the pair. -/
def LocalGram (ω : ℝ → ℝ) : Prop :=
  ∀ y ∈ SphereConfig 7,
    (∀ i j, i ≠ j → |⟪y i, y j⟫_ℝ - ⟪pentBipyramid i, pentBipyramid j⟫_ℝ|
      ≤ ω ⟪pentBipyramid i, pentBipyramid j⟫_ℝ) →
    coulombEnergy pentBipyramid ≤ coulombEnergy y ∧
    (coulombEnergy y = coulombEnergy pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, y i = g (pentBipyramid i))

end TwoRegime

/- END TWOREGIME -/

/- BEGIN TR_D -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_D -/

/- BEGIN TR_E -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

section FinalCut

variable {n : ℕ}

end FinalCut

end ThreePoint

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_E -/

/- BEGIN TR_G -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- BEGIN TR_G3 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- **Asymmetric Gram window.** The configuration `y` lies in the window around the Gram matrix of
the relabelled pentagonal bipyramid `P ∘ σ`: for every pair `i ≠ j` the inner product `⟪y i, y j⟫`
lies in `[t - lo t, t + hi t]` where `t = ⟪P (σ i), P (σ j)⟫` is the nominal value. -/
def InWindow (lo hi : ℝ → ℝ) (y : Fin 7 → R3) (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ i j, i ≠ j →
    ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ - lo ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ
      ≤ ⟪y i, y j⟫_ℝ ∧
    ⟪y i, y j⟫_ℝ
      ≤ ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ + hi ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ

/-- **Local statement, asymmetric Gram-window form.** Every unit configuration in the window
`[t - lo t, t + hi t]` around the Gram matrix of the labelled `P` has energy at least `E(P)`, with
equality only on the `O(3)`-orbit of `P`. -/
def LocalGramA (lo hi : ℝ → ℝ) : Prop :=
  ∀ y ∈ SphereConfig 7, InWindow lo hi y (Equiv.refl (Fin 7)) →
    coulombEnergy pentBipyramid ≤ coulombEnergy y ∧
    (coulombEnergy y = coulombEnergy pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, y i = g (pentBipyramid i))

end TwoRegime
/- END TR_G3 -/
/- BEGIN TR_G4 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime
/- END TR_G4 -/
/- END TR_G -/

/- BEGIN INTERFACES -/
namespace Interfaces

open Finset Base

end Interfaces
/- END INTERFACES -/

/- BEGIN GLUE -/
namespace Glue

open Finset Base Interfaces

end Glue
/- END GLUE -/

/- BEGIN TR_F -/
namespace EPBounds

open Real

end EPBounds
/- END TR_F -/
end ThomsonN7

section RegLocalSection
/- BEGIN REGLOCAL (agent7): perturbative strict local minimality of the pentagonal bipyramid.
   Splice AFTER Level1d (needs GAUGE = exists_gauge, P1/P3ext, Base, TwoRegime.LocalMinAt).
   Pieces in order: Loc1 (H, B3) | QCore1 (certificate defs/lemmas) | Q2 (expansion) | QCore2 (core) | Loc2 (glue). -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
/- BEGIN LOC1 (agent7): exact chart identity (H) and cubic Bregman lower bound (B3) in h = y - P.
   Splice AFTER the GAUGE block (needs P1, P3ext); compiles against Level1b.lean lines 1-3641. -/
namespace Reg
open Base

/-- Gram matrix entry `⟪P_i, P_j⟫` of the bipyramid. -/
noncomputable def gP (i j : Fin 7) : ℝ := inner ℝ (pentBipyramid i) (pentBipyramid j)

/-- The Gram increment `⟪y_i, y_j⟫ - ⟪P_i, P_j⟫`. -/
noncomputable def tau (y : Fin 7 → R3) (i j : Fin 7) : ℝ := inner ℝ (y i) (y j) - gP i j

end Reg

/- END LOC1 -/

end ThomsonN7

/- BEGIN QCORE1 -/
namespace ThomsonN7
namespace Reg

noncomputable def CP_0 (c s p q r : ℝ) : ℝ := (2) + (1 / 2) * q ^ 3 + (3 / 4) * q ^ 5 + c * q ^ 3 + (3) * c * q ^ 5 - c * p ^ 3 + (3) * c ^ 2 * q ^ 5 + (3) * c ^ 2 * p ^ 5
noncomputable def CP_1 (c s p q r : ℝ) : ℝ := p ^ 3 + (3) * c * p ^ 5
noncomputable def CP_2 (c s p q r : ℝ) : ℝ := q ^ 3 + (-3 / 2) * q ^ 5 + (-3) * c * q ^ 5
noncomputable def CP_3 (c s p q r : ℝ) : ℝ := r ^ 3
noncomputable def CP_4 (c s p q r : ℝ) : ℝ := (2) + (1 / 2) * q ^ 3 + (3) * s ^ 2 * p ^ 5 + c * q ^ 3 - c * p ^ 3 + (12) * c ^ 2 * s ^ 2 * q ^ 5
noncomputable def CP_5 (c s p q r : ℝ) : ℝ := (-4) * s + (3) * s * p ^ 5
noncomputable def CP_6 (c s p q r : ℝ) : ℝ := p ^ 3 + (4) * c
noncomputable def CP_7 (c s p q r : ℝ) : ℝ := (-8) * c * s + (6) * c * s * q ^ 5
noncomputable def CP_8 (c s p q r : ℝ) : ℝ := (-2) + q ^ 3 + (-4) * c
noncomputable def CP_9 (c s p q r : ℝ) : ℝ := (8) * c * s + (-6) * c * s * q ^ 5
noncomputable def CP_10 (c s p q r : ℝ) : ℝ := (4) * s + (-3) * s * p ^ 5
noncomputable def CP_11 (c s p q r : ℝ) : ℝ := (2) + (3) * r ^ 5 + (1 / 2) * q ^ 3 + c * q ^ 3 - c * p ^ 3
noncomputable def CP_12 (c s p q r : ℝ) : ℝ := (-4) + (3) * r ^ 5
noncomputable def CP_13 (c s p q r : ℝ) : ℝ := (4) + (-3) * r ^ 5
noncomputable def CP_14 (c s p q r : ℝ) : ℝ := (1 / 2) * q ^ 3 + (3 / 8) * q ^ 5 + (15 / 8) * p ^ 5 + (2) * s ^ 2 + c * q ^ 3 + (3 / 2) * c * q ^ 5 - c * p ^ 3 + (3 / 2) * c * p ^ 5 + (2) * c ^ 2 + (3) * c ^ 2 * q ^ 5 + (3 / 2) * c ^ 2 * p ^ 5
noncomputable def CP_15 (c s p q r : ℝ) : ℝ := (-3) * c * s * p ^ 5 + (6) * c ^ 2 * s * q ^ 5 + (-6) * c ^ 2 * s * p ^ 5
noncomputable def CP_16 (c s p q r : ℝ) : ℝ := p ^ 3 + (-3 / 2) * c * p ^ 5 + (8) * c * s ^ 2 + (-3) * c ^ 2 * p ^ 5
noncomputable def CP_17 (c s p q r : ℝ) : ℝ := (2) * s + (-3 / 2) * s * p ^ 5 + (4) * c * s + (-3) * c * s * p ^ 5
noncomputable def CP_18 (c s p q r : ℝ) : ℝ := q ^ 3 + (-3 / 2) * c * q ^ 5 + (-8) * c * s ^ 2 + (-3) * c ^ 2 * q ^ 5
noncomputable def CP_19 (c s p q r : ℝ) : ℝ := (2) * s + (-3 / 2) * s * q ^ 5 + (4) * c * s + (-3) * c * s * q ^ 5
noncomputable def CP_20 (c s p q r : ℝ) : ℝ := q ^ 3 + (-4) * s ^ 2 + (3) * c ^ 2 * q ^ 5
noncomputable def CP_21 (c s p q r : ℝ) : ℝ := (-4) * c * s + (3) * c * s * q ^ 5
noncomputable def CP_22 (c s p q r : ℝ) : ℝ := (1 / 2) * q ^ 3 + (2) * s ^ 2 + (3 / 2) * s ^ 2 * q ^ 5 + c * q ^ 3 - c * p ^ 3 + (2) * c ^ 2 + (6) * c ^ 2 * s ^ 2 * q ^ 5 + (6) * c ^ 2 * s ^ 2 * p ^ 5
noncomputable def CP_23 (c s p q r : ℝ) : ℝ := (-8) * c ^ 2 * s + (6) * c ^ 2 * s * p ^ 5
noncomputable def CP_24 (c s p q r : ℝ) : ℝ := p ^ 3 + (-2) * c + (6) * c * s ^ 2 * p ^ 5 + (-4) * c ^ 2
noncomputable def CP_25 (c s p q r : ℝ) : ℝ := (8) * c ^ 2 * s + (-6) * c ^ 2 * s * q ^ 5
noncomputable def CP_26 (c s p q r : ℝ) : ℝ := q ^ 3 + (-2) * c + (-6) * c * s ^ 2 * q ^ 5 + (-4) * c ^ 2
noncomputable def CP_27 (c s p q r : ℝ) : ℝ := (4) * c * s + (-3) * c * s * q ^ 5
noncomputable def CP_28 (c s p q r : ℝ) : ℝ := q ^ 3 + (-3) * s ^ 2 * q ^ 5 + (4) * c ^ 2
noncomputable def CP_29 (c s p q r : ℝ) : ℝ := (3) * r ^ 5 + (1 / 2) * q ^ 3 + (2) * s ^ 2 + c * q ^ 3 - c * p ^ 3 + (2) * c ^ 2
noncomputable def CP_30 (c s p q r : ℝ) : ℝ := p ^ 3 + (-2) * c + (8) * c * s ^ 2 + (-4) * c ^ 2
noncomputable def CP_31 (c s p q r : ℝ) : ℝ := q ^ 3 + (-2) * c + (-8) * c * s ^ 2 + (-4) * c ^ 2
noncomputable def CP_32 (c s p q r : ℝ) : ℝ := q ^ 3 + (-4) * s ^ 2 + (4) * c ^ 2
noncomputable def CP_33 (c s p q r : ℝ) : ℝ := (-4) * c + (3) * c * r ^ 5
noncomputable def CP_34 (c s p q r : ℝ) : ℝ := (-4) * s + (3) * s * r ^ 5
noncomputable def CP_35 (c s p q r : ℝ) : ℝ := (4) * c + (-3) * c * r ^ 5
noncomputable def CP_36 (c s p q r : ℝ) : ℝ := (4) * s + (-3) * s * r ^ 5
noncomputable def CP_37 (c s p q r : ℝ) : ℝ := (1 / 2) + (1 / 2) * q ^ 3 + (3 / 2) * q ^ 5 + (3 / 8) * p ^ 5 + (2) * c + c * q ^ 3 - c * p ^ 3 + (3 / 2) * c * p ^ 5 + (2) * c ^ 2 + (3 / 2) * c ^ 2 * q ^ 5 + (3) * c ^ 2 * p ^ 5 + (8) * c ^ 2 * s ^ 2
noncomputable def CP_38 (c s p q r : ℝ) : ℝ := (-3) * c * s * q ^ 5 + (6) * c * s * p ^ 5 + (6) * c ^ 2 * s * p ^ 5
noncomputable def CP_39 (c s p q r : ℝ) : ℝ := p ^ 3 + (3 / 4) * p ^ 5 + (3) * c * p ^ 5 + (3) * c ^ 2 * p ^ 5 + (-16) * c ^ 2 * s ^ 2
noncomputable def CP_40 (c s p q r : ℝ) : ℝ := (4) * c * s + (-3) * c * s * p ^ 5 + (8) * c ^ 2 * s + (-6) * c ^ 2 * s * p ^ 5
noncomputable def CP_41 (c s p q r : ℝ) : ℝ := (-8) * c ^ 2 * s + (6) * c ^ 2 * s * q ^ 5
noncomputable def CP_42 (c s p q r : ℝ) : ℝ := (1 / 2) + (1 / 2) * q ^ 3 + (3 / 2) * s ^ 2 * q ^ 5 + (3 / 2) * s ^ 2 * p ^ 5 + (2) * c + c * q ^ 3 - c * p ^ 3 + (2) * c ^ 2 + (8) * c ^ 2 * s ^ 2 + (6) * c ^ 2 * s ^ 2 * p ^ 5
noncomputable def CP_43 (c s p q r : ℝ) : ℝ := (-4) * c * s + (3) * c * s * p ^ 5 + (-8) * c ^ 2 * s + (6) * c ^ 2 * s * p ^ 5
noncomputable def CP_44 (c s p q r : ℝ) : ℝ := (1) + p ^ 3 + (4) * c + (4) * c ^ 2 + (-12) * c ^ 2 * s ^ 2 * p ^ 5
noncomputable def CP_45 (c s p q r : ℝ) : ℝ := (-2) * s + (3 / 2) * s * q ^ 5 + (-4) * c * s + (3) * c * s * q ^ 5
noncomputable def CP_46 (c s p q r : ℝ) : ℝ := (1 / 2) + (3) * r ^ 5 + (1 / 2) * q ^ 3 + (2) * c + c * q ^ 3 - c * p ^ 3 + (2) * c ^ 2 + (8) * c ^ 2 * s ^ 2
noncomputable def CP_47 (c s p q r : ℝ) : ℝ := (1) + p ^ 3 + (4) * c + (4) * c ^ 2 + (-16) * c ^ 2 * s ^ 2
noncomputable def CP_48 (c s p q r : ℝ) : ℝ := (2) + (-3 / 2) * r ^ 5 + (4) * c + (-3) * c * r ^ 5
noncomputable def CP_49 (c s p q r : ℝ) : ℝ := (-8) * c * s + (6) * c * s * r ^ 5
noncomputable def CP_50 (c s p q r : ℝ) : ℝ := (-2) + (3 / 2) * r ^ 5 + (-4) * c + (3) * c * r ^ 5
noncomputable def CP_51 (c s p q r : ℝ) : ℝ := (8) * c * s + (-6) * c * s * r ^ 5
noncomputable def CP_52 (c s p q r : ℝ) : ℝ := (3) * c * s * q ^ 5 + (-6) * c * s * p ^ 5 + (-6) * c ^ 2 * s * p ^ 5
noncomputable def CP_53 (c s p q r : ℝ) : ℝ := (8) * c ^ 2 * s + (-6) * c ^ 2 * s * p ^ 5
noncomputable def CP_54 (c s p q r : ℝ) : ℝ := (-2) * s + (3 / 2) * s * p ^ 5 + (-4) * c * s + (3) * c * s * p ^ 5
noncomputable def CP_55 (c s p q r : ℝ) : ℝ := (3) * c * s * p ^ 5 + (-6) * c ^ 2 * s * q ^ 5 + (6) * c ^ 2 * s * p ^ 5
noncomputable def CP_56 (c s p q r : ℝ) : ℝ := (33 / 16) + (9 / 4) * r ^ 5 + (3) * c * r ^ 5 + (6) * c ^ 2 * r ^ 5
noncomputable def CP_57 (c s p q r : ℝ) : ℝ := (-31 / 8)
noncomputable def CP_58 (c s p q r : ℝ) : ℝ := (33 / 16) + (3) * s ^ 2 * r ^ 5 + (12) * c ^ 2 * s ^ 2 * r ^ 5
noncomputable def CP_59 (c s p q r : ℝ) : ℝ := (135 / 64)
noncomputable def CP_60 (c s p q r : ℝ) : ℝ := (1 / 32)

noncomputable def Fq (c s p q r : ℝ) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : ℝ :=
  CP_0 c s p q r * (x0 ^ 2)
  + CP_1 c s p q r * (x0 * x3)
  + CP_2 c s p q r * (x0 * x6)
  + CP_2 c s p q r * (x0 * x9)
  + CP_1 c s p q r * (x0 * x12)
  + CP_3 c s p q r * (x0 * x15)
  + CP_3 c s p q r * (x0 * x18)
  + CP_4 c s p q r * (x1 ^ 2)
  + CP_5 c s p q r * (x1 * x3)
  + CP_6 c s p q r * (x1 * x4)
  + CP_7 c s p q r * (x1 * x6)
  + CP_8 c s p q r * (x1 * x7)
  + CP_9 c s p q r * (x1 * x9)
  + CP_8 c s p q r * (x1 * x10)
  + CP_10 c s p q r * (x1 * x12)
  + CP_6 c s p q r * (x1 * x13)
  + CP_3 c s p q r * (x1 * x16)
  + CP_3 c s p q r * (x1 * x19)
  + CP_11 c s p q r * (x2 ^ 2)
  + CP_6 c s p q r * (x2 * x5)
  + CP_8 c s p q r * (x2 * x8)
  + CP_8 c s p q r * (x2 * x11)
  + CP_6 c s p q r * (x2 * x14)
  + CP_12 c s p q r * (x2 * x15)
  + CP_3 c s p q r * (x2 * x17)
  + CP_13 c s p q r * (x2 * x18)
  + CP_3 c s p q r * (x2 * x20)
  + CP_14 c s p q r * (x3 ^ 2)
  + CP_15 c s p q r * (x3 * x4)
  + CP_16 c s p q r * (x3 * x6)
  + CP_17 c s p q r * (x3 * x7)
  + CP_18 c s p q r * (x3 * x9)
  + CP_19 c s p q r * (x3 * x10)
  + CP_20 c s p q r * (x3 * x12)
  + CP_21 c s p q r * (x3 * x13)
  + CP_3 c s p q r * (x3 * x15)
  + CP_3 c s p q r * (x3 * x18)
  + CP_22 c s p q r * (x4 ^ 2)
  + CP_23 c s p q r * (x4 * x6)
  + CP_24 c s p q r * (x4 * x7)
  + CP_25 c s p q r * (x4 * x9)
  + CP_26 c s p q r * (x4 * x10)
  + CP_27 c s p q r * (x4 * x12)
  + CP_28 c s p q r * (x4 * x13)
  + CP_3 c s p q r * (x4 * x16)
  + CP_3 c s p q r * (x4 * x19)
  + CP_29 c s p q r * (x5 ^ 2)
  + CP_30 c s p q r * (x5 * x8)
  + CP_31 c s p q r * (x5 * x11)
  + CP_32 c s p q r * (x5 * x14)
  + CP_33 c s p q r * (x5 * x15)
  + CP_34 c s p q r * (x5 * x16)
  + CP_3 c s p q r * (x5 * x17)
  + CP_35 c s p q r * (x5 * x18)
  + CP_36 c s p q r * (x5 * x19)
  + CP_3 c s p q r * (x5 * x20)
  + CP_37 c s p q r * (x6 ^ 2)
  + CP_38 c s p q r * (x6 * x7)
  + CP_39 c s p q r * (x6 * x9)
  + CP_40 c s p q r * (x6 * x10)
  + CP_18 c s p q r * (x6 * x12)
  + CP_41 c s p q r * (x6 * x13)
  + CP_3 c s p q r * (x6 * x15)
  + CP_3 c s p q r * (x6 * x18)
  + CP_42 c s p q r * (x7 ^ 2)
  + CP_43 c s p q r * (x7 * x9)
  + CP_44 c s p q r * (x7 * x10)
  + CP_45 c s p q r * (x7 * x12)
  + CP_26 c s p q r * (x7 * x13)
  + CP_3 c s p q r * (x7 * x16)
  + CP_3 c s p q r * (x7 * x19)
  + CP_46 c s p q r * (x8 ^ 2)
  + CP_47 c s p q r * (x8 * x11)
  + CP_31 c s p q r * (x8 * x14)
  + CP_48 c s p q r * (x8 * x15)
  + CP_49 c s p q r * (x8 * x16)
  + CP_3 c s p q r * (x8 * x17)
  + CP_50 c s p q r * (x8 * x18)
  + CP_51 c s p q r * (x8 * x19)
  + CP_3 c s p q r * (x8 * x20)
  + CP_37 c s p q r * (x9 ^ 2)
  + CP_52 c s p q r * (x9 * x10)
  + CP_16 c s p q r * (x9 * x12)
  + CP_53 c s p q r * (x9 * x13)
  + CP_3 c s p q r * (x9 * x15)
  + CP_3 c s p q r * (x9 * x18)
  + CP_42 c s p q r * (x10 ^ 2)
  + CP_54 c s p q r * (x10 * x12)
  + CP_24 c s p q r * (x10 * x13)
  + CP_3 c s p q r * (x10 * x16)
  + CP_3 c s p q r * (x10 * x19)
  + CP_46 c s p q r * (x11 ^ 2)
  + CP_30 c s p q r * (x11 * x14)
  + CP_48 c s p q r * (x11 * x15)
  + CP_51 c s p q r * (x11 * x16)
  + CP_3 c s p q r * (x11 * x17)
  + CP_50 c s p q r * (x11 * x18)
  + CP_49 c s p q r * (x11 * x19)
  + CP_3 c s p q r * (x11 * x20)
  + CP_14 c s p q r * (x12 ^ 2)
  + CP_55 c s p q r * (x12 * x13)
  + CP_3 c s p q r * (x12 * x15)
  + CP_3 c s p q r * (x12 * x18)
  + CP_22 c s p q r * (x13 ^ 2)
  + CP_3 c s p q r * (x13 * x16)
  + CP_3 c s p q r * (x13 * x19)
  + CP_29 c s p q r * (x14 ^ 2)
  + CP_33 c s p q r * (x14 * x15)
  + CP_36 c s p q r * (x14 * x16)
  + CP_3 c s p q r * (x14 * x17)
  + CP_35 c s p q r * (x14 * x18)
  + CP_34 c s p q r * (x14 * x19)
  + CP_3 c s p q r * (x14 * x20)
  + CP_56 c s p q r * (x15 ^ 2)
  + CP_57 c s p q r * (x15 * x18)
  + CP_58 c s p q r * (x16 ^ 2)
  + CP_57 c s p q r * (x16 * x19)
  + CP_59 c s p q r * (x17 ^ 2)
  + CP_60 c s p q r * (x17 * x20)
  + CP_56 c s p q r * (x18 ^ 2)
  + CP_58 c s p q r * (x19 ^ 2)
  + CP_59 c s p q r * (x20 ^ 2)

/-- The box in which the five atoms live. -/
def InBox (c s p q r : ℝ) : Prop :=
  (30901699 / 100000000 : ℝ) ≤ c ∧ c ≤ (309017 / 1000000 : ℝ) ∧ (95105651 / 100000000 : ℝ) ≤ s ∧ s ≤ (23776413 / 25000000 : ℝ) ∧ (2126627 / 2500000 : ℝ) ≤ p ∧ p ≤ (85065081 / 100000000 : ℝ) ∧
    (52573111 / 100000000 : ℝ) ≤ q ∧ q ≤ (6571639 / 12500000 : ℝ) ∧ (35355339 / 50000000 : ℝ) ≤ r ∧ r ≤ (70710679 / 100000000 : ℝ)

end Reg
end ThomsonN7
/- END QCORE1 -/

/- BEGIN Q2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

/-- Quadratic part of the second-order lower bound for the energy at the bipyramid, in the chart
`y = P + h`. -/
noncomputable def Qhess (h : Fin 7 → R3) : ℝ :=
  1 / 2 * ∑ i, ∑ j, W i j * inner ℝ (h i) (h j) - 1 / 2 * ∑ i, muP i * ‖h i‖ ^ 2
    + ∑ i, ∑ j ∈ Finset.Ioi i, 3 / 2 * phi (gP i j) ^ 5
        * (inner ℝ (pentBipyramid i) (h j) + inner ℝ (h i) (pentBipyramid j)) ^ 2

/-- The `(a, b)` entry of the antisymmetric part of `∑ᵢ Pᵢ ⊗ hᵢ` (rotation gauge functional). -/
noncomputable def gaugeG (h : Fin 7 → R3) (a b : Fin 3) : ℝ :=
  ∑ i, (pentBipyramid i a * h i b - pentBipyramid i b * h i a)

/-- Penalty: normal components `⟪Pᵢ, hᵢ⟫` and the rotation gauge. -/
noncomputable def Pen (h : Fin 7 → R3) : ℝ :=
  ∑ i, inner ℝ (pentBipyramid i) (h i) ^ 2
    + gaugeG h 0 1 ^ 2 + gaugeG h 0 2 ^ 2 + gaugeG h 1 2 ^ 2

end Reg
end ThomsonN7

/- END Q2 -/

/- BEGIN QCORE2 -/
namespace ThomsonN7
namespace Reg

end Reg
end ThomsonN7
/- END QCORE2 -/

/- BEGIN LOC2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

/-! ### The atom box for the penalised Hessian certificate -/

/-- The `(i, j)` remainder: the cubic Bregman lower bound term minus its quadratic part. -/
noncomputable def Dpair (y : Fin 7 → R3) (i j : Fin 7) : ℝ :=
  3 / 2 * phi (gP i j) ^ 5 * tau y i j ^ 2 + 5 / 2 * phi (gP i j) ^ 7 * tau y i j ^ 3
    - 3 / 2 * phi (gP i j) ^ 5
      * (inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
          + inner ℝ (y i - pentBipyramid i) (pentBipyramid j)) ^ 2

end Reg
end ThomsonN7

/- END LOC2 -/

namespace ThomsonN7
namespace Reg

end Reg

end ThomsonN7

/- END REGLOCAL -/
end RegLocalSection

/- BEGIN CASE1 -/
namespace ThomsonN7
namespace CutOneD

/-- Integer polynomial (low degree first) evaluated at a real point. -/
def peval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, y => (a : ℝ) + y * peval as y

/-- Sum of integer polynomials. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- Scalar multiple. -/
def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

/-- Negation. -/
def pneg (p : List ℤ) : List ℤ := p.map (- ·)

/-- Product. -/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, q => padd (pscale a q) (0 :: pmul as q)

/-- `Q(1 - 2 y²)` for `Q` given by its coefficient list. -/
def compQ : List ℤ → List ℤ
  | [] => []
  | c :: cs => padd [c] (pmul [1, 0, -2] (compQ cs))

/-- Weighted sum of squares `Σ d ρ²` (integer polynomial). -/
def sqSum : List (ℕ × List ℤ) → List ℤ
  | [] => []
  | (d, r) :: rs => padd (pscale d (pmul r r)) (sqSum rs)

/-- Real-valued weighted sum of squares. -/
def sqEval (L : List (ℕ × List ℤ)) (y : ℝ) : ℝ := (L.map fun x => (x.1 : ℝ) * peval x.2 y ^ 2).sum

/-- Data of the certificate for `H = Q / Lam` on `{ν y² ≤ μ}`. -/
structure Cert where
  Lam : ℕ
  Q : List ℤ
  A0 : List (ℕ × List ℤ)
  A1 : List (ℕ × List ℤ)
  A2 : List (ℕ × List ℤ)
  A3 : List (ℕ × List ℤ)

/-- The polynomial `Lam - 2 y Q(1 - 2y²) - (A0 + y A1 + (μ - ν y²) A2 + y (μ - ν y²) A3)`. -/
def Cert.diff (mu nu : ℤ) (c : Cert) : List ℤ :=
  padd (padd [(c.Lam : ℤ)] (pneg (pmul [0, 2] (compQ c.Q))))
    (pneg (padd (padd (sqSum c.A0) (pmul [0, 1] (sqSum c.A1)))
      (padd (pmul [mu, 0, -nu] (sqSum c.A2)) (pmul [0, mu, 0, -nu] (sqSum c.A3)))))

/-- The check (positivity of the scale, vanishing of all coefficients). -/
def Cert.check (mu nu : ℤ) (c : Cert) : Bool := 0 < c.Lam && (c.diff mu nu).all (· == 0)

/-- Exact data of the one-dimensional certificate (generated). -/
def cutCert : Cert where
  Lam := 1461501637330902918203684832716283019655932542976
  Q := [1033429565797810028242136385456139960160197017600, 516738619187048425029386827906950920139408670722, 386721746872820607749170206421320440977876320258, 323589702097575287657044527725205868806913654782, 297159272854125446375965699970024547334267863042, 267079512659567484484003393692239640166649561088, 165044719006786182005861671268474532475573370880, 29901494154292147095883329121317011208007581696, -25983765825260590146197679491475372665848463358, -9262669364589662002327432043744621045229813762, 2671910827434195023430173697867124853564243970]
  A0 := [(2747837390130, [144115188075855872, -530222120307978377, 500983509204429715, 95278021200381386, -226143307183296218, 155589112702820178, -127238190180130140, -338547783112190245, 340249001846739896, 50745940767846733, -64145589083848554]),
    (1193268944300, [0, 144115188075855872, -455485363194430330, 262657142802090179, 232246418391755433, -14829823659840796, -141446812038135199, 42340825049342546, -166788762161156608, -91564566037486841, 189954013508781772]),
    (3987459286060, [0, 0, 72057594037927936, -240783285061920106, 163910012073105082, 102663879173941022, 32020696965185493, -139306841269211009, -98040494312113020, 83309536703984784, 24562929208443820]),
    (3928775678327, [0, 0, 0, 72057594037927936, -279367097683353467, 304408522119933163, 41310175525894763, -194166297846182771, 16343337997559576, 31555934962299306, 8109308342812972]),
    (1221193040324, [0, 0, 0, 0, 144115188075855872, -409918720943067296, 171035544831835053, 369495593751407036, -139752569099734287, -318552385553293374, 184249711207251580]),
    (1126043715512, [0, 0, 0, 0, 0, 144115188075855872, -370641664508381944, 224435987974892157, 37503400284208330, 38661195916654213, -73428520197396258]),
    (2378677265665, [0, 0, 0, 0, 0, 0, 144115188075855872, -369653013486479329, 191177876883937371, 164776877718758276, -129915791879821261]),
    (4383396068799, [0, 0, 0, 0, 0, 0, 0, 72057594037927936, -177614070698181215, 137175634825283180, -30966879651148048]),
    (1335894547995, [0, 0, 0, 0, 0, 0, 0, 0, 144115188075855872, -301190571315721955, 158535503097888044]),
    (1729842893137, [0, 0, 0, 0, 0, 0, 0, 0, 0, 18014398509481984, -16870707667435898]),
    (1561085017744, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2251799813685248]),
    (696898203281335971332886176264251301061956, [1]),
    (696898076104248045035353226429408601993470, [0, 1]),
    (696898083355296840443743998193173106528622, [0, 0, 1]),
    (696898207314599817295079818946699014762588, [0, 0, 0, 1]),
    (696897957678102079193514145938274336082256, [0, 0, 0, 0, 1]),
    (696897847253694499364966079182232129987428, [0, 0, 0, 0, 0, 1]),
    (696898133372541807529427917749079190693244, [0, 0, 0, 0, 0, 0, 1]),
    (696897863911857602129373490198515282226931, [0, 0, 0, 0, 0, 0, 0, 1]),
    (696897949611355952190113032553626116566202, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (696897944812590565124847603417288247992519, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (696897977858448910802988395418483618952679, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (19531529776280509172455008226288812, [1, -1]),
    (18454637968296142623716641976042116, [1, 0, 1]),
    (3509673559402671564998301815779594, [1, 0, 0, 1]),
    (8330333777502110053226885015892874, [1, 0, 0, 0, -1]),
    (5731425451166934171811966842782066, [1, 0, 0, 0, 0, 1]),
    (4687066090430216072818713383277442, [1, 0, 0, 0, 0, 0, -1]),
    (12470924420714555630194340838050858, [1, 0, 0, 0, 0, 0, 0, -1]),
    (12533653406085662843297247858143030, [1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1869282403727044342999853274436810, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (2362963388240951234922694548182698, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]),
    (72361979051233612250775905182986986, [0, 1, -1]),
    (10337766285098497460709025874755298, [0, 1, 0, -1]),
    (32924978496999496692713952563267828, [0, 1, 0, 0, 1]),
    (21231966245933971495713949118123516, [0, 1, 0, 0, 0, -1]),
    (15857711421636802534051571398418098, [0, 1, 0, 0, 0, 0, 1]),
    (46297151405524504925659790374565386, [0, 1, 0, 0, 0, 0, 0, 1]),
    (47747839922613538411110777905107174, [0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (7774931140070088169446460254041012, [0, 1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (10555648512276982796362548402247542, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (10106097435447062843451616383174988, [0, 0, 1, -1]),
    (26508643442629704152891854944873452, [0, 0, 1, 0, -1]),
    (26424509761795490104245494373201072, [0, 0, 1, 0, 0, 1]),
    (10026764722905426590339840905034700, [0, 0, 1, 0, 0, 0, -1]),
    (52861809510530930545327549917998164, [0, 0, 1, 0, 0, 0, 0, -1]),
    (42968739309202865486431122484898282, [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (14237419539158613709733148401154270, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (12653937810297579729240549224511146, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (46066773363466422514865081027108002, [0, 0, 0, 1, -1]),
    (3065522511916453675022329907486008, [0, 0, 0, 1, 0, -1]),
    (10077249352786233804992804516692538, [0, 0, 0, 1, 0, 0, -1]),
    (11231690465013646106578720973323376, [0, 0, 0, 1, 0, 0, 0, 1]),
    (25314089609609980776058780479612710, [0, 0, 0, 1, 0, 0, 0, 0, 1]),
    (15372061129593351437569899268731014, [0, 0, 0, 1, 0, 0, 0, 0, 0, -1]),
    (2636276620502530277773351053399526, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (96805059496936252032418997406006757, [0, 0, 0, 0, 1, -1]),
    (22532847406870694043680553735168051, [0, 0, 0, 0, 1, 0, 1]),
    (79025971386743550097674899448692011, [0, 0, 0, 0, 1, 0, 0, 1]),
    (54826025714680599692653634107622294, [0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (36463220646209848122467367783234150, [0, 0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (30438779815401831544991208400608518, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (99541485310083183333979207032308391, [0, 0, 0, 0, 0, 1, -1]),
    (157725451896634770345922878047750521, [0, 0, 0, 0, 0, 1, 0, -1]),
    (60495323642681873583789702627462980, [0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (127429418922565084515022134644335168, [0, 0, 0, 0, 0, 1, 0, 0, 0, 1]),
    (70687564875901325973327911698076280, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (55687896697462518633313169199478671, [0, 0, 0, 0, 0, 0, 1, -1]),
    (25086220022177186983421180628229338, [0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (39362344386007107445924969601300864, [0, 0, 0, 0, 0, 0, 1, 0, 0, -1]),
    (38607468470550951693570382653838614, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]),
    (107499636612429640012852007190687437, [0, 0, 0, 0, 0, 0, 0, 1, -1]),
    (144757170766940705490736378398035356, [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (75264128015979436981615417148193553, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (27656717836016013650841858697672678, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1]),
    (36293501523886318397317714030238421, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (91659505163136706082109809662048638, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1])]
  A1 := [(2429043016818, [72057594037927936, -247485185172667688, 187207682985521150, 92955437043716422, -32895472742999665, -52399351409588658, -94010611873226418, 66550524130154419, -13276049488934071, -750045860873896, 22546447455253222]),
    (1401043487167, [0, 144115188075855872, -509817237368808421, 413115032960537609, 238552807272435092, -330936455862138536, 149632263984032515, -58350976599771876, -337174588060045183, 328173056102691271, -36467515899294368]),
    (3917931501315, [0, 0, 72057594037927936, -253117178678385055, 168138605856160536, 235475576636535111, -180279809260624465, -182922063253054192, 118490178830899921, 34113918461940257, -11698805855853317]),
    (2477833370988, [0, 0, 0, 72057594037927936, -227412627803350576, 163229665261553641, 56472259020513469, 26912964377135588, -93410166237460891, -75578967345103221, 78045069379416841]),
    (1310990663071, [0, 0, 0, 0, 144115188075855872, -478629616943756989, 413512563360140957, 155164457569343824, -298722812625996877, 16147296329399566, 48866412509221714]),
    (1371335359789, [0, 0, 0, 0, 0, 144115188075855872, -332133762402817299, 80276575407169438, 219963817044762793, -45412056910783374, -66218247873502794]),
    (1309744262537, [0, 0, 0, 0, 0, 0, 144115188075855872, -402621163887923111, 327828903737836234, -14359470760112598, -54237043080558093]),
    (1536735037935, [0, 0, 0, 0, 0, 0, 0, 144115188075855872, -350776984881723238, 265042773555302736, -57100957634466880]),
    (1186165872246, [0, 0, 0, 0, 0, 0, 0, 0, 144115188075855872, -300020683206881352, 157319531059727766]),
    (1876932900973, [0, 0, 0, 0, 0, 0, 0, 0, 0, 18014398509481984, -16975922303693234]),
    (1626535510962, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2251799813685248]),
    (696898264996719961033250609544689815107660, [1]),
    (696897966431075077502405986741739830188808, [0, 1]),
    (696897501599047154843681152848298369142459, [0, 0, 1]),
    (696897596952365940662001452671281069257881, [0, 0, 0, 1]),
    (696897830850974343357601393986340874625842, [0, 0, 0, 0, 1]),
    (696897422278768256916863684219292216734835, [0, 0, 0, 0, 0, 1]),
    (696897678736103958149317607182855347098948, [0, 0, 0, 0, 0, 0, 1]),
    (696898086964168966448439527348902745499342, [0, 0, 0, 0, 0, 0, 0, 1]),
    (696897425022189526873190460960957074977350, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (696897674940198912459365584949290376011421, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (696898185405951703904765783180312425833988, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (7530738967970783711305210180059248, [1, -1]),
    (5696679930355830818825865315731570, [1, 0, 1]),
    (2828575070177937505002863589603522, [1, 0, 0, 1]),
    (1001001919739363798264073390217198, [1, 0, 0, 0, -1]),
    (1594555863917558346549081326890280, [1, 0, 0, 0, 0, -1]),
    (2860723212797254861102205308681382, [1, 0, 0, 0, 0, 0, -1]),
    (2025014881340956904196200555400078, [1, 0, 0, 0, 0, 0, 0, 1]),
    (403900894895738762365464398464786, [1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (22811550413590817909485963378942, [1, 0, 0, 0, 0, 0, 0, 0, 0, -1]),
    (686028236587701606579888464060112, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (90393879356116517892967284990454802, [0, 1, -1]),
    (47679173501019079850854864093983972, [0, 1, 0, 1]),
    (36579977873502444159984531193431054, [0, 1, 0, 0, 1]),
    (40500231735972481714541538314352280, [0, 1, 0, 0, 0, -1]),
    (30613422188610470817546851570809630, [0, 1, 0, 0, 0, 0, 1]),
    (15061675760347639108870905672112078, [0, 1, 0, 0, 0, 0, 0, -1]),
    (45456293522136209133305614846051010, [0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (45671177119620936585336921660245726, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (7422680160799190057814962207452174, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]),
    (211955496584575165250859286570891595, [0, 0, 1, -1]),
    (109035435045142796362121836163357822, [0, 0, 1, 0, -1]),
    (173638387185956069008969705481194556, [0, 0, 1, 0, 0, 1]),
    (92559721769414224593779782756177199, [0, 0, 1, 0, 0, 0, -1]),
    (22181784142404347721438474670835876, [0, 0, 1, 0, 0, 0, 0, 1]),
    (172278584167623764697807982683688013, [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (159154042279576005657411504416396449, [0, 0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (18953540234357336111221244139770112, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (54610753791757342742615885815892290, [0, 0, 0, 1, 1]),
    (186201890632190694861970708146322805, [0, 0, 0, 1, 0, -1]),
    (96887539311280483450461620999805664, [0, 0, 0, 1, 0, 0, 1]),
    (20809330058016359455884946322912684, [0, 0, 0, 1, 0, 0, 0, 1]),
    (162022059925858973507368920337356646, [0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (122584338257674482745759682742367088, [0, 0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (10606448618318270860454856226674445, [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (95742123964812762267968174609975500, [0, 0, 0, 0, 1, -1]),
    (53663818966705461094336353167500944, [0, 0, 0, 0, 1, 0, 1]),
    (24988400579306525127933671042270820, [0, 0, 0, 0, 1, 0, 0, -1]),
    (91250102221088307547183305910925472, [0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (83582379097800856902429326239167072, [0, 0, 0, 0, 1, 0, 0, 0, 0, 1]),
    (6266083876397178593752059221340502, [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]),
    (260943865523193177352898720640519112, [0, 0, 0, 0, 0, 1, -1]),
    (71936591677080370464950984778135960, [0, 0, 0, 0, 0, 1, 0, -1]),
    (258777914509310691205101564931423984, [0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (107834149067172154723021472058291067, [0, 0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (13564922491084606645117900197348969, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (46273296495873540142273364715736398, [0, 0, 0, 0, 0, 0, 1, 1]),
    (195922432869288094145370393511738796, [0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (54562615856105544187681316270251296, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (22414612983938316619581358633210903, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]),
    (52895335108555488457492149880103278, [0, 0, 0, 0, 0, 0, 0, 1, -1]),
    (16514364723497595669089086022367638, [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (8956408975012624709836393538111681, [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (133119674388983381724522795174801084, [0, 0, 0, 0, 0, 0, 0, 0, 1, -1]),
    (5596407160378758971638846557661737, [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (17028960122438121089273329434335869, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1])]
  A2 := [(3558991230905, [144115188075855872, -302047877302316653, -233252781201717235, 483869079132312095, 416326137485436293, -314965571008324065, -197019042162027737, -150626528986341207, -105150889559301545, 253282283259980657]),
    (3484965961950, [0, 72057594037927936, -220810820996606969, 103713390540841533, 185741373952737577, -137300987604179760, 38141587985529598, 9171387600378965, -140768713243762492, 86158358973943675]),
    (3674625923348, [0, 0, 36028797018963968, -89005579237905456, -4095981062178708, 96876911698401800, 19604331373099136, -47290588445231018, -16106555944707448, 786992367500048]),
    (3505657090297, [0, 0, 0, 36028797018963968, -88326935770233626, 17831702822358422, 34842666662819917, 23376730542218872, 50534955343085777, -78201378596946065]),
    (1104136723367, [0, 0, 0, 0, 72057594037927936, -195359119786259472, 39225837347770065, 201543179421814192, -45049080598553316, -76779085506793851]),
    (4095668876805, [0, 0, 0, 0, 0, 18014398509481984, -50852402520197470, 40560790553490987, -2108381237301281, -5126745759641031]),
    (2671598483716, [0, 0, 0, 0, 0, 0, 36028797018963968, -88674956997489445, 54459770933685753, 91997344904236]),
    (2142757372540, [0, 0, 0, 0, 0, 0, 0, 36028797018963968, -83531182023591777, 48723921515194256]),
    (1390396801444, [0, 0, 0, 0, 0, 0, 0, 0, 18014398509481984, -19838014380145684]),
    (3649986307662, [0, 0, 0, 0, 0, 0, 0, 0, 0, 562949953421312]),
    (43555814193967151957057432812996629702904, [1]),
    (43555607551980650569443559297443159769023, [0, 1]),
    (43555587722203016631310434313720755681275, [0, 0, 1]),
    (43555315695694853153914644796425849456553, [0, 0, 0, 1]),
    (43555354339084914148976257411197357132527, [0, 0, 0, 0, 1]),
    (43555510183342488548226107068947588022947, [0, 0, 0, 0, 0, 1]),
    (43555742842483413129863390298276629246984, [0, 0, 0, 0, 0, 0, 1]),
    (43555854612017066252433654474261427542182, [0, 0, 0, 0, 0, 0, 0, 1]),
    (43555836029185626291573070665572758471977, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (43555576802966271539550692954743917469969, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (42944306361102915205346337201268834, [1, -1]),
    (33163010650601914644578936416219756, [1, 0, -1]),
    (68794537044197185348442862411094456, [1, 0, 0, 1]),
    (59191626263714030791434118992399324, [1, 0, 0, 0, 1]),
    (44780615092645332976261215163403394, [1, 0, 0, 0, 0, -1]),
    (28011519806264670630489244297555888, [1, 0, 0, 0, 0, 0, -1]),
    (21415368046744962003064729031193432, [1, 0, 0, 0, 0, 0, 0, -1]),
    (14949884803742111967065624074159586, [1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (36010824744913141849077943021324106, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (54887938875317203435750200868249901, [0, 1, 1]),
    (137319733134913845113500774963109065, [0, 1, 0, -1]),
    (111762491194395097754487917653491899, [0, 1, 0, 0, -1]),
    (84765585532640358747210540123590199, [0, 1, 0, 0, 0, 1]),
    (61234210432859874130052382931105421, [0, 1, 0, 0, 0, 0, 1]),
    (45491490853138931297012731256680369, [0, 1, 0, 0, 0, 0, 0, 1]),
    (22014106085076529937624016663904275, [0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (69770914270585106047489231223466893, [0, 1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (132829716759163302657210211955837307, [0, 0, 1, -1]),
    (133503977858833775914447079238551711, [0, 0, 1, 0, -1]),
    (100816188076318352455645047370533447, [0, 0, 1, 0, 0, 1]),
    (37697035895309857833685237676778251, [0, 0, 1, 0, 0, 0, 1]),
    (32563754449290256325222449154887167, [0, 0, 1, 0, 0, 0, 0, 1]),
    (52673335179075170204554156066533171, [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (75758384814658003898845653931243951, [0, 0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (215292481975651934089579700853101967, [0, 0, 0, 1, 1]),
    (164389687106614220464307382015555245, [0, 0, 0, 1, 0, -1]),
    (90185791128134642341845230498690081, [0, 0, 0, 1, 0, 0, -1]),
    (70128278014568160478609175123311185, [0, 0, 0, 1, 0, 0, 0, -1]),
    (62726158045692528440279019844305763, [0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (128049952373125652655772030138084941, [0, 0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (160985830948919625332746554606034479, [0, 0, 0, 0, 1, -1]),
    (74061152044161110437582957123762895, [0, 0, 0, 0, 1, 0, -1]),
    (53262126824868565921868647025586713, [0, 0, 0, 0, 1, 0, 0, -1]),
    (70613854909496236092147043564226779, [0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (118354889876986835503115814645468439, [0, 0, 0, 0, 1, 0, 0, 0, 0, 1]),
    (52687142785020500831803877124520637, [0, 0, 0, 0, 0, 1, 1]),
    (24147550575380250209556979669035437, [0, 0, 0, 0, 0, 1, 0, 1]),
    (55264891281042108500168953127287605, [0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (82052541952233285152812292452439139, [0, 0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (33454705291374174702741532112035365, [0, 0, 0, 0, 0, 0, 1, 1]),
    (15378307843302007405329559647089108, [0, 0, 0, 0, 0, 0, 1, 0, 1]),
    (48813277270388377273005650757522283, [0, 0, 0, 0, 0, 0, 1, 0, 0, -1]),
    (8667069078777550416333359378828138, [0, 0, 0, 0, 0, 0, 0, 1, 1]),
    (45356141473471014129244914490316782, [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (38661329587852986567400041340932085, [0, 0, 0, 0, 0, 0, 0, 0, 1, -1])]
  A3 := [(3245441846980, [72057594037927936, -179591780850547098, -63255461780810123, 304709564500502677, 37220111825845641, -83294046514193410, -1339497267101440, -218787181004976020, -128974108557772692, 269146655340877867]),
    (1593496145674, [0, 36028797018963968, -113630404688905391, 48373192777747284, 80868377911300794, 32355710648171177, -23425241398536217, -121185698980086953, -45052947861793932, 108367551295508575]),
    (2763175388163, [0, 0, 36028797018963968, -131259436178204969, 97403709908351842, 112974965987573973, -113833779006138961, -47934868748804567, 25407279300467178, 21608832491323555]),
    (1521228463559, [0, 0, 0, 36028797018963968, -79435554616493932, -10675352795065511, 54911326603421071, 42981359377706860, 23644142212239786, -71627202494590437]),
    (1538403637742, [0, 0, 0, 0, 36028797018963968, -118573573083657366, 92933267879374749, 40381564639807366, -49948573064427223, -2035006531791838]),
    (1281469980203, [0, 0, 0, 0, 0, 36028797018963968, -87549875296988680, 9236961195882921, 109207516464674002, -67142219285557961]),
    (1332098424728, [0, 0, 0, 0, 0, 0, 36028797018963968, -86251696566734997, 53449503965287402, -1780926745602630]),
    (3292949471075, [0, 0, 0, 0, 0, 0, 0, 36028797018963968, -83827934701112346, 49024118678960944]),
    (3383845490514, [0, 0, 0, 0, 0, 0, 0, 0, 9007199254740992, -9802111465655305]),
    (3646132387796, [0, 0, 0, 0, 0, 0, 0, 0, 0, 562949953421312]),
    (43556130993307752238132770527805930143564, [1]),
    (43556126022670600397889906687221086881822, [0, 1]),
    (43556111175731235668798088533386453700280, [0, 0, 1]),
    (43556101694124584239692912716326960653057, [0, 0, 0, 1]),
    (43556121825254557252523602523870243944896, [0, 0, 0, 0, 1]),
    (43556114566059735752722364112126955775192, [0, 0, 0, 0, 0, 1]),
    (43556116325076249083879246138051859315510, [0, 0, 0, 0, 0, 0, 1]),
    (43556096458681421691094159834218506369129, [0, 0, 0, 0, 0, 0, 0, 1]),
    (43556100620345486501101140124899870728022, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (43556089732997842018861807054725802334964, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1770780513517416691509938850050026, [1, -1]),
    (623729298963438541151290004041294, [1, 0, -1]),
    (3004393809075575888783048357146070, [1, 0, 0, 1]),
    (367087649805921245990145706498912, [1, 0, 0, 0, 1]),
    (821208874066969701254351146395766, [1, 0, 0, 0, 0, -1]),
    (13116944068164878605591500832020, [1, 0, 0, 0, 0, 0, -1]),
    (2157264588364907008871458699555200, [1, 0, 0, 0, 0, 0, 0, -1]),
    (1271625473983951936655780224494568, [1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (2653847758809599125217812101871966, [1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1170186825575408747793928032948890, [0, 1, -1]),
    (6328129639335721302831720750016790, [0, 1, 0, -1]),
    (1024226200324383943083720655297798, [0, 1, 0, 0, 1]),
    (2822604589279704614494493809140052, [0, 1, 0, 0, 0, 1]),
    (529037000217100736470323962753264, [0, 1, 0, 0, 0, 0, -1]),
    (2470768709941102226657333431297124, [0, 1, 0, 0, 0, 0, 0, 1]),
    (2089011346887381222736213247398600, [0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (4015822522759719842472451646369172, [0, 1, 0, 0, 0, 0, 0, 0, 0, -1]),
    (7840107576557226310405389924165256, [0, 0, 1, -1]),
    (5292083147294962153335040887112354, [0, 0, 1, 0, -1]),
    (396774099249175067910591158079978, [0, 0, 1, 0, 0, -1]),
    (443792061973378753746648501001864, [0, 0, 1, 0, 0, 0, 1]),
    (10494853034722381698848526740424834, [0, 0, 1, 0, 0, 0, 0, 1]),
    (4822582957760157337819957892581004, [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (10271086263725735316237587258456552, [0, 0, 1, 0, 0, 0, 0, 0, 0, -1]),
    (145631824098679753329374616662288, [0, 0, 0, 1, -1]),
    (7290533388754333358225300568436027, [0, 0, 0, 1, 0, -1]),
    (4157105218568848567014705460079375, [0, 0, 0, 1, 0, 0, 1]),
    (10900893869757586157329808660725541, [0, 0, 0, 1, 0, 0, 0, -1]),
    (7879227058581748618894489918394526, [0, 0, 0, 1, 0, 0, 0, 0, -1]),
    (13671020231287796067735681953679401, [0, 0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (1188535757729468360316765894126190, [0, 0, 0, 0, 1, 1]),
    (2134422880996829710155567274300146, [0, 0, 0, 0, 1, 0, -1]),
    (8032080707973293357998752824908550, [0, 0, 0, 0, 1, 0, 0, -1]),
    (3940341311311239140518909670035936, [0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (8077532611444090208319259984341880, [0, 0, 0, 0, 1, 0, 0, 0, 0, 1]),
    (17301017690269441250751630349855436, [0, 0, 0, 0, 0, 1, -1]),
    (5814130316043565967262321165613933, [0, 0, 0, 0, 0, 1, 0, -1]),
    (10240693104396175852793715850194894, [0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (1905506273501764483020988136548582, [0, 0, 0, 0, 0, 1, 0, 0, 0, -1]),
    (6150717276382093093252002269857103, [0, 0, 0, 0, 0, 0, 1, 1]),
    (12860026766631619478281554455948684, [0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (2495693301245275380333649573415182, [0, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    (3890988620567479007348469505273116, [0, 0, 0, 0, 0, 0, 0, 1, 1]),
    (16694992210719465232261569657622130, [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]),
    (17386816999005137076740614757288084, [0, 0, 0, 0, 0, 0, 0, 0, 1, -1])]

end CutOneD
end ThomsonN7

namespace ThomsonN7

namespace Case1Data
open ThomsonN7 ThomsonN7.Cert

end Case1Data

end ThomsonN7

namespace ThomsonN7
namespace Case1

open scoped InnerProductSpace
open ThomsonN7.Cert ThomsonN7.Cert.Cert3

/-! ### Chunked evaluation of the Kronecker check for `Case1Data.cf`

The identity expression `Case1Data.cf.idE` has about 147 000 nodes.  Evaluating `chk` on it in one
kernel call is correct but keeps every intermediate kernel term alive until the end of the
declaration.  Here the same check is split into separate declarations, one per piece of the
expression (`hE`, four `F`-blocks, eight `S`-blocks).  For every expression `e`, `c1Stat w D e`
computes, in one structural pass, the tuple `(ℓ¹-norm, deg u, deg v, deg t, Kronecker value)`
(`c1Stat_eq`).  The 13 pieces are evaluated by `decide +kernel` against exact literals, in 13
separate declarations; the statistics of `Case1Data.cf.idE` follow by the composition lemma
`c1Stat_idE` and closed arithmetic on the literals, and `chk` is then decided by its own definition
(`Nat.log2 ℓ¹ + 1 = 179`, `max deg + 1 = 11`, Kronecker value `0`).  The statement of `cf_ok` is
unchanged; the literals are data found by a program outside Lean and are only ever checked. -/

/-- The five statistics of an expression tree that the Kronecker check needs, in the order
`(ℓ¹-norm, degree in u, degree in v, degree in t, Kronecker value)`. -/
abbrev C1Stat : Type := ℕ × ℕ × ℕ × ℕ × ℤ

/-- Statistics of a sum. -/
def c1Add (s t : C1Stat) : C1Stat :=
  (s.1 + t.1, max s.2.1 t.2.1, max s.2.2.1 t.2.2.1, max s.2.2.2.1 t.2.2.2.1,
    s.2.2.2.2 + t.2.2.2.2)

/-- Statistics of a product. -/
def c1Mul (s t : C1Stat) : C1Stat :=
  (s.1 * t.1, s.2.1 + t.2.1, s.2.2.1 + t.2.2.1, s.2.2.2.1 + t.2.2.2.1, s.2.2.2.2 * t.2.2.2.2)

/-- Statistics of the constant `a`. -/
def c1C (a : ℤ) : C1Stat := (a.natAbs, 0, 0, 0, a)

/-- All five statistics of an expression tree, computed in one structural pass. -/
def c1Stat (w D : ℕ) : Kron.Ex → C1Stat
  | .c n => c1C n
  | .mon a b d => (1, a, b, d, ((2 ^ (w * (a + D * b + D * D * d)) : ℕ) : ℤ))
  | .add p q => c1Add (c1Stat w D p) (c1Stat w D q)
  | .mul p q => c1Mul (c1Stat w D p) (c1Stat w D q)

/-- Statistics of a difference. -/
def c1Sub (s t : C1Stat) : C1Stat := c1Add s (c1Mul (c1C (-1)) t)

/-- Statistics of an integer multiple. -/
def c1Smul (a : ℤ) (s : C1Stat) : C1Stat := c1Mul (c1C a) s

/-- Statistics of a sum of a list (right fold). -/
def c1Sum (l : List C1Stat) : C1Stat := l.foldr c1Add (c1C 0)

/-- The summand of `ftotE` belonging to one `F`-expression. -/
def c1FtotK (n : ℕ) (e : Kron.Ex) : Kron.Ex :=
  Kron.Ex.add
    (Kron.Ex.add (Kron.Ex.smul (((n : ℤ) - 1) * ((n : ℤ) - 2)) (sixE 0 1 2 e))
      (Kron.Ex.smul ((n : ℤ) - 1)
        (Kron.Ex.add (Kron.Ex.add (sixE 0 0 3 e) (sixE 1 1 3 e)) (sixE 2 2 3 e))))
    (sixE 3 3 3 e)

/-! The 13 pieces, each evaluated in its own declaration (`w = 179`, `D = 11`). -/

end Case1
end ThomsonN7

/- END CASE1 -/

/- BEGIN CASE2RED -/
namespace ThomsonN7
namespace Case1

section Case2Red

open scoped InnerProductSpace
open Base

end Case2Red

end Case1
end ThomsonN7
/- END CASE2RED -/

section Asm_Typed
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed (root-dependent) three-point bound

Every root `i` carries its own kernel `s i`; every pair `{i, j}` carries its own minorant `H i j`.
-/

section TypedRoot

end TypedRoot

section TypedComb

variable {n : ℕ}

/-- The marginal kernel of root `i` at a pair value `t`. -/
noncomputable def mrg (s : Fin n → ℝ → ℝ → ℝ → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  s i 1 t t + s i t 1 t + s i t t 1

end TypedComb

end ThreePoint
end ThomsonN7

end Asm_Typed

section Asm_Typed2
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed three-point bound with free pair shares

Each triple `{i, j, l}` receives a share `W i j l` of the pair function of `{i, j}` (and
similarly for the constant), so that the total over the triples containing a pair is prescribed.
-/

section TypedComb2

variable {n : ℕ}

end TypedComb2

end ThreePoint
end ThomsonN7

end Asm_Typed2

section Asm_Typed7
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

section Sym

end Sym

/-! # The `n = 7` typed instance: two poles (indices `0, 1`) and five ring points (`2..6`) -/

section Typed7

/-- The pole indicator: indices `0` and `1` are the poles. -/
def isP (i : Fin 7) : Prop := i.val < 2

instance (i : Fin 7) : Decidable (isP i) := by unfold isP; infer_instance

/-- Pair functions by colour: `A` pole-pole, `B` pole-ring, `C` ring-ring. -/
noncomputable def H7 (HA HB HC : ℝ → ℝ) (i j : Fin 7) (t : ℝ) : ℝ :=
  if isP i then (if isP j then HA t else HB t) else (if isP j then HB t else HC t)

/-- Root kernels by colour. -/
noncomputable def s7 (SP SR : ℝ → ℝ → ℝ → ℝ) (i : Fin 7) : ℝ → ℝ → ℝ → ℝ :=
  if isP i then SP else SR

/-- The marginal of a pole. -/
noncomputable def gm (S : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : ℝ := S 1 t t + S t 1 t + S t t 1

/-- The pair-share of the pair `{i, j}` at the third vertex `l`. -/
noncomputable def W7 (SP SR : ℝ → ℝ → ℝ → ℝ) (HA HB HC ψBa ψCb : ℝ → ℝ)
    (i j l : Fin 7) (t : ℝ) : ℝ :=
  let PsiA := HA t - 2 * gm SP t
  let PsiB := HB t - gm SP t - gm SR t
  let PsiC := HC t - 2 * gm SR t
  if isP i then
    (if isP j then (if isP l then 0 else PsiA / 5)
     else (if isP l then ψBa t else (PsiB - ψBa t) / 4))
  else
    (if isP j then (if isP l then ψBa t else (PsiB - ψBa t) / 4)
     else (if isP l then ψCb t else (PsiC - 2 * ψCb t) / 3))

/-- The triple constants by colour pattern. -/
noncomputable def c7 (e sP sR cal cbe : ℝ) (i j l : Fin 7) : ℝ :=
  if isP i then
    (if isP j then (if isP l then 0 else cal)
     else (if isP l then cal else cbe))
  else
    (if isP j then (if isP l then cal else cbe)
     else (if isP l then cbe else (e + 2 * sP + 5 * sR - 5 * cal - 20 * cbe) / 10))

/-- The pole-pole-ring slack. -/
noncomputable def lamA (SP SR : ℝ → ℝ → ℝ → ℝ) (HA ψBa : ℝ → ℝ) (cal : ℝ) (u v t : ℝ) : ℝ :=
  (HA u - 2 * gm SP u) / 5 + ψBa v + ψBa t - cal - 2 * (SP u v t + SP u t v + SR v t u)

/-- The pole-ring-ring slack. -/
noncomputable def lamB (SP SR : ℝ → ℝ → ℝ → ℝ) (HB ψBa ψCb : ℝ → ℝ) (cbe : ℝ) (u v t : ℝ) : ℝ :=
  ((HB u - gm SP u - gm SR u) - ψBa u) / 4 + ((HB v - gm SP v - gm SR v) - ψBa v) / 4
    + ψCb t - cbe - 2 * (SP u v t + SR u t v + SR v t u)

/-- The ring-ring-ring slack. -/
noncomputable def lamG (SR : ℝ → ℝ → ℝ → ℝ) (HC ψCb : ℝ → ℝ) (cga : ℝ) (u v t : ℝ) : ℝ :=
  ((HC u - 2 * gm SR u) - 2 * ψCb u) / 3 + ((HC v - 2 * gm SR v) - 2 * ψCb v) / 3
    + ((HC t - 2 * gm SR t) - 2 * ψCb t) / 3 - cga - 2 * (SR u v t + SR u t v + SR v t u)

/-- A finite family of matrix kernel pairings. -/
noncomputable def Sk (K : ℕ) (m : ℕ → ℕ) (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (u v t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, matDot (F k) (Y3 (m k) k u v t)

end Typed7

end ThreePoint
end ThomsonN7

end Asm_Typed7

section Asm_T4
namespace ThomsonN7
namespace M6

/-! ### Integer interval arithmetic (exact, no rounding) -/

/-- membership of a real number in a closed interval with integer endpoints -/
def Imem (I : ℤ × ℤ) (x : ℝ) : Prop := (I.1 : ℝ) ≤ x ∧ x ≤ (I.2 : ℝ)

def iadd (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 + b.1, a.2 + b.2)

def imul (a b : ℤ × ℤ) : ℤ × ℤ :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))

def isq (a : ℤ × ℤ) : ℤ × ℤ :=
  if 0 ≤ a.1 then (a.1 * a.1, a.2 * a.2)
  else if a.2 ≤ 0 then (a.2 * a.2, a.1 * a.1)
  else (0, max (a.1 * a.1) (a.2 * a.2))

def iscale (c : ℤ) (a : ℤ × ℤ) : ℤ × ℤ :=
  if 0 ≤ c then (c * a.1, c * a.2) else (c * a.2, c * a.1)

/-! ### Homogeneous Gram determinants and their interval enclosures -/

/-- Gram determinant of three unit vectors, homogenised by `δ` (the diagonal entry) -/
def det3h {R : Type*} [CommRing R] (δ a b c : R) : R :=
  δ ^ 3 + 2 * a * b * c - δ * (a ^ 2 + b ^ 2 + c ^ 2)

/-- Gram determinant of four unit vectors, homogenised (same as `M3.det4h`) -/
def det4h {R : Type*} [CommRing R] (δ p01 p02 p03 p12 p13 p23 : R) : R :=
  δ ^ 4 - δ ^ 2 * (p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2)
    + (p01 ^ 2 * p23 ^ 2 + p02 ^ 2 * p13 ^ 2 + p03 ^ 2 * p12 ^ 2)
    + 2 * δ * (p01 * p12 * p02 + p01 * p13 * p03 + p02 * p23 * p03 + p12 * p23 * p13)
    - 2 * (p01 * p02 * p13 * p23 + p01 * p03 * p12 * p23 + p02 * p03 * p12 * p13)

def idet3 (δ : ℤ) (A B C : ℤ × ℤ) : ℤ × ℤ :=
  iadd (iadd (δ ^ 3, δ ^ 3) (iscale 2 (imul (imul A B) C)))
    (iscale (-δ) (iadd (iadd (isq A) (isq B)) (isq C)))

def idet4 (δ : ℤ) (A B C D E F : ℤ × ℤ) : ℤ × ℤ :=
  let s := iadd (iadd (iadd (isq A) (isq B)) (isq C)) (iadd (iadd (isq D) (isq E)) (isq F))
  let q := iadd (iadd (imul (isq A) (isq F)) (imul (isq B) (isq E))) (imul (isq C) (isq D))
  let t := iadd (iadd (imul (imul A D) B) (imul (imul A E) C))
    (iadd (imul (imul B F) C) (imul (imul D F) E))
  let u := iadd (iadd (imul (imul A B) (imul E F)) (imul (imul A C) (imul D F)))
    (imul (imul B C) (imul D E))
  iadd (iadd (iadd (δ ^ 4, δ ^ 4) (iscale (-(δ ^ 2)) s)) (iadd q (iscale (2 * δ) t))) (iscale (-2) u)

/-! ### Boxes, bisection and the two refutation checkers -/

structure Box6 where
  A : ℤ × ℤ
  B : ℤ × ℤ
  C : ℤ × ℤ
  D : ℤ × ℤ
  E : ℤ × ℤ
  F : ℤ × ℤ

def Box6.Mem (b : Box6) (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ) : Prop :=
  Imem b.A a₁ ∧ Imem b.B a₂ ∧ Imem b.C a₃ ∧ Imem b.D a₄ ∧ Imem b.E a₅ ∧ Imem b.F a₆

def mid (I : ℤ × ℤ) : ℤ := (I.1 + I.2) / 2

/-- the coordinate (0..5) with the widest interval -/
def widest (b : Box6) : ℕ :=
  let w : List ℤ := [b.A.2 - b.A.1, b.B.2 - b.B.1, b.C.2 - b.C.1, b.D.2 - b.D.1,
    b.E.2 - b.E.1, b.F.2 - b.F.1]
  ((List.range 6).foldl (fun (best : ℕ × ℤ) i =>
    if best.2 < w.getD i 0 then (i, w.getD i 0) else best) (0, w.getD 0 0)).1

def Box6.split (j : ℕ) (b : Box6) : Box6 × Box6 :=
  match j with
  | 0 => ({ b with A := (b.A.1, mid b.A) }, { b with A := (mid b.A, b.A.2) })
  | 1 => ({ b with B := (b.B.1, mid b.B) }, { b with B := (mid b.B, b.B.2) })
  | 2 => ({ b with C := (b.C.1, mid b.C) }, { b with C := (mid b.C, b.C.2) })
  | 3 => ({ b with D := (b.D.1, mid b.D) }, { b with D := (mid b.D, b.D.2) })
  | 4 => ({ b with E := (b.E.1, mid b.E) }, { b with E := (mid b.E, b.E.2) })
  | _ => ({ b with F := (b.F.1, mid b.F) }, { b with F := (mid b.F, b.F.2) })

/-- refutation checker for a 4-subset: on the whole box either the Gram determinant `det4h`
has no zero or one of the four `det3h` is negative. -/
def chk4 (δ : ℤ) : ℕ → Box6 → Bool
  | 0, _ => false
  | n + 1, b =>
    decide (0 < (idet4 δ b.A b.B b.C b.D b.E b.F).1) ||
    decide ((idet4 δ b.A b.B b.C b.D b.E b.F).2 < 0) ||
    decide ((idet3 δ b.A b.B b.D).2 < 0) || decide ((idet3 δ b.A b.C b.E).2 < 0) ||
    decide ((idet3 δ b.B b.C b.F).2 < 0) || decide ((idet3 δ b.D b.E b.F).2 < 0) ||
    (chk4 δ n (b.split (widest b)).1 && chk4 δ n (b.split (widest b)).2)

end M6
end ThomsonN7

open scoped InnerProductSpace

namespace ThomsonN7
namespace T4

open M6

/-! ### Combinatorics of the ring: a 2-colouring of `K₅` without monochromatic triangle is a pentagon -/

/-- index of the pair `a < b` in a fixed enumeration of the ten pairs of `Fin 5` -/
def pidx (a b : ℕ) : ℕ := a * (9 - a) / 2 + (b - a - 1)

/-- colouring of the complete graph on `Fin 5` given by ten Booleans (list indexed by `pidx`) -/
def mk10 (l : List Bool) (a b : Fin 5) : Bool :=
  if (a : ℕ) < b then l.getD (pidx a b) false
  else if (b : ℕ) < a then l.getD (pidx b a) false
  else false

/-- the pentagon colouring: `true` on cyclically adjacent pairs -/
def pentc (i j : Fin 5) : Bool := decide (((i : ℕ) + 5 - j) % 5 = 1 ∨ ((j : ℕ) + 5 - i) % 5 = 1)

/-- no monochromatic triangle in a colouring of `K₅` -/
def triFree (x : Fin 5 → Fin 5 → Bool) : Bool :=
  decide (∀ a b c : Fin 5, a < b → b < c → ¬ (x a b = true ∧ x a c = true ∧ x b c = true)) &&
  decide (∀ a b c : Fin 5, a < b → b < c → ¬ (x a b = false ∧ x a c = false ∧ x b c = false))

/-- the colouring is a relabelled pentagon colouring -/
def isPent (x : Fin 5 → Fin 5 → Bool) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 5), ∀ a b : Fin 5, a < b → x a b = pentc (σ a) (σ b))

/-! ### The ring colouring of a configuration -/

/-- ring colour: `true` iff the inner product of the ring vectors `a`, `b` (indices `a + 2`,
`b + 2`) is within `τ` of `cos (2π/5)`. -/
noncomputable def col (τ : ℝ) (y : Fin 7 → R3) (a b : Fin 5) : Bool :=
  decide (|⟪y a.succ.succ, y b.succ.succ⟫_ℝ - M3.cosB| ≤ τ)

/-! ### The relabelling of the bipyramid -/

/-- pentagon vertex `a : Fin 5` as an index `0..4` of `Fin 7` -/
def pentIdx (a : Fin 5) : Fin 7 := ⟨a.val, by omega⟩

/-- The relabelling of `Fin 7` induced by a permutation `s` of the ring `Fin 5`:
the poles `0, 1` go to the pole indices `5, 6` and the ring vertex `a + 2` goes to `s a`. -/
def sig7 (s : Equiv.Perm (Fin 5)) (i : Fin 7) : Fin 7 :=
  if h : i.val < 2 then ⟨i.val + 5, by omega⟩
  else pentIdx (s ⟨i.val - 2, by omega⟩)

lemma sig7_injective (s : Equiv.Perm (Fin 5)) : Function.Injective (sig7 s) := by
  intro i j h
  unfold sig7 at h
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2 <;>
    simp only [hi, hj, dite_true, dite_false, pentIdx] at h
  · have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  · exfalso
    have := congrArg Fin.val h
    simp only at this
    have := (s ⟨j.val - 2, by omega⟩).isLt
    omega
  · exfalso
    have := congrArg Fin.val h
    simp only at this
    have := (s ⟨i.val - 2, by omega⟩).isLt
    omega
  · have h1 := congrArg Fin.val h
    simp only at h1
    have h2 := s.injective (Fin.ext h1)
    have h3 := congrArg Fin.val h2
    simp only at h3
    exact Fin.ext (by omega)

/-- `sig7 s` as a permutation of `Fin 7` -/
noncomputable def sigEquiv (s : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective (sig7 s) ⟨sig7_injective s, Finite.injective_iff_surjective.1 (sig7_injective s)⟩

/-! ### Nominal Gram entries of the relabelled bipyramid -/

/-! ### Ring rigidity -/

end T4
end ThomsonN7

end Asm_T4

section Asm_Glue1
/-!
# Glue for the near-antipodal case (Case 2)

Abstract, numerics-independent assembly:

* `Glue.exists_minpair_perm`: every 7-configuration is a relabelling of one whose pair `(0,1)` has the
  smallest inner product;
* `Glue.RootedClaim`, `Glue.case2_of_rooted`, `Glue.seven_of_rooted`: the rooted claim implies both
  Challenge statements (through `Case1.seven_of_case2`);
* `Glue.rooted_of_cap_slabs`: a cap certificate plus finitely many slab certificates give the rooted
  claim;
* `Glue.slab_of_typed`, `Glue.cap_of_typed`: a typed pair-minorant bound gives the slab / cap claims
  (with the equality analysis through `M3.contact_rigidity`).
-/

namespace ThomsonN7
namespace Glue

section Rooted

open scoped InnerProductSpace
open Base

/-- The conclusion of the Thomson `N = 7` statement for a single configuration. -/
def Concl (y : Fin 7 → R3) : Prop :=
  coulombEnergy pentBipyramid ≤ coulombEnergy y ∧
  (coulombEnergy y = coulombEnergy pentBipyramid →
    ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, y i = g (pentBipyramid (σ i)))

end Rooted

section Typed

open scoped InnerProductSpace
open Base

/-- Class selector for a pair `{i, j}`: `A` for the pole pair `{0, 1}`, `B` for pole--ring pairs
and `C` for ring--ring pairs. -/
def cls3 {α : Sort*} (A B C : α) (i j : Fin 7) : α :=
  if i.val ≤ 1 ∧ j.val ≤ 1 then A else if i.val ≤ 1 ∨ j.val ≤ 1 then B else C

end Typed

end Glue
end ThomsonN7

end Asm_Glue1

section Asm_Glue2
/-!
# Glue for the near-sharp (tube) cap certificate, route S2

A typed pair-minorant bound `e <= sum_{i<j} H_cls(<y_i, y_j>)` which is only *near*-sharp
(`E(P) <= e + delta`) still gives the cap claim, provided

* the pair slacks `phi - H_cls` control the distance to the nodes (`slack <= delta` puts the inner
  product within `tau` of a node of its class);
* the tube rigidity `TubeRigid tau` (closeness of all 21 inner products to the class nodes gives a
  relabelling of the pentagonal bipyramid within `tau` in every Gram entry);
* the local statement `LocalGramA` holds on the window `tau` (Regime B).

The proof is: `E(y) <= E(P)` implies `sum of slacks <= delta`, hence every slack `<= delta`, hence the
tube, hence the window, hence the local statement.
-/

namespace ThomsonN7
namespace Glue

section Tube

open scoped InnerProductSpace
open Base

/-- **Tube rigidity (ring part).**  A unit configuration whose pole pair `(0,1)` is within `tau`
of antipodal, whose pole--ring inner products are within `tau` of `0` and whose ring--ring inner
products are within `tau` of the two ring nodes `c1, c2`, is within `tau` in every Gram entry of a
relabelling of the pentagonal bipyramid. -/
def TubeRigid (τ : ℝ) : Prop :=
  ∀ y : Fin 7 → R3, (∀ i, ‖y i‖ = 1) →
    |⟪y 0, y 1⟫_ℝ + 1| ≤ τ →
    (∀ r : Fin 7, 2 ≤ r.val → |⟪y 0, y r⟫_ℝ| ≤ τ) →
    (∀ r : Fin 7, 2 ≤ r.val → |⟪y 1, y r⟫_ℝ| ≤ τ) →
    (∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - c1| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - c2| ≤ τ) →
    ∃ σ : Equiv.Perm (Fin 7), ∀ i j, i ≠ j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ| ≤ τ

end Tube

end Glue
end ThomsonN7

end Asm_Glue2

section Asm_Glue2b
namespace ThomsonN7
namespace Glue
section TubeFromT4
open scoped RealInnerProductSpace

end TubeFromT4
end Glue
end ThomsonN7

end Asm_Glue2b

section Asm_Glue3
/-!
# Glue3: the typed three-point bound (`Typed7`) feeds the cap / slab glue (`Glue1`, `Glue2`)

`ThreePoint.typed7_bound` bounds `e` by the typed double sum `∑ i<j, H7 HA HB HC i j ⟪x i, x j⟫`.
Here we identify `H7` with the class selector `Glue.cls3` (poles are the indices `0, 1`) and
restate the bound in exactly the shape needed by `Glue.cap_of_typed`, `Glue.cap_of_typed_tube`
and `Glue.slab_of_typed`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

end Bridge

section Assembly

open scoped InnerProductSpace
open Base

end Assembly

end Glue
end ThomsonN7

end Asm_Glue3

section Asm_Glue4
/-!
# Glue4: the final interface (`CapSpec`, `SlabSpec`) and the assembly `seven_of_specs`

The near-sharp cap and the margin slabs are certified by *typed* three-point data
(`Typed7`): PSD blocks `FP FR`, class minorants `HA HB HC`, multipliers `ψBa ψCb`, constants
`cal cbe`, together with one-dimensional facts on the minorants.  `CapSpec a0` (resp.
`SlabSpec lo hi`) is the proposition "such data exist"; every certificate producer has to prove
one of these propositions and nothing else.  `seven_of_specs` is the assembly: a cap spec at
`a 0` and slab specs on `[a k, a (k+1)]` for `k < K`, with `a K ≥ -9/10`, give both Challenge
statements for `N = 7`.

The tube-rigidity hypothesis of the near-sharp cap and the local (Regime B) statement are
discharged here once and for all (`Glue.tubeRigid_of_le`, `Glue.localGramA_of_le`).
-/

namespace ThomsonN7
namespace Glue

section Final

open scoped InnerProductSpace
open Base

/-- **Cap specification.**  A near-sharp cap certificate on the cap `⟪y 0, y 1⟫ ≤ a0`: class
minorants `HA HB HC` whose typed sum is bounded below by `e` on minimal-pair configurations of the
cap, with `E(P) ≤ e + δ`, a tube width `τ ≤ 1/165000`, and the one-dimensional facts that the
minorants lie below `phi` and that a slack `≤ δ` puts the inner product within `τ` of the class
nodes (`-1`, `0`, `c1`/`c2`). -/
def CapSpec (a0 : ℝ) : Prop :=
  ∃ (e δ τ : ℝ) (HA HB HC : ℝ → ℝ),
    τ ≤ 1 / 165000 ∧ coulombEnergy pentBipyramid ≤ e + δ ∧
    (∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ phi t ∧ (phi t - HA t ≤ δ → |t + 1| ≤ τ)) ∧
    (∀ t, -1 ≤ t → t < 1 → HB t ≤ phi t ∧ (phi t - HB t ≤ δ → |t| ≤ τ)) ∧
    (∀ t, -1 ≤ t → t < 1 →
      HC t ≤ phi t ∧ (phi t - HC t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ))

/-- **Slab specification.**  A margin certificate on the slab `lo ≤ ⟪y 0, y 1⟫ ≤ hi`: class
minorants `HA HB HC` below `phi` whose typed sum is bounded below by some `e > E(P)` on
minimal-pair configurations of the slab. -/
def SlabSpec (lo hi : ℝ) : Prop :=
  ∃ (e : ℝ) (HA HB HC : ℝ → ℝ),
    coulombEnergy pentBipyramid < e ∧
    (∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, lo ≤ t → t ≤ hi → HA t ≤ phi t) ∧
    (∀ t, lo ≤ t → t < 1 → HB t ≤ phi t) ∧
    (∀ t, lo ≤ t → t < 1 → HC t ≤ phi t)

end Final

end Glue
end ThomsonN7

end Asm_Glue4

section Asm_EPEnc
/-!  agent9: 40-digit enclosure of the minimal energy `E(P)` (for the near-sharp cap route).  -/

namespace ThomsonN7
namespace Glue
section EPEnc
open Real

end EPEnc
end Glue
end ThomsonN7

end Asm_EPEnc

section Asm_Coerce
/-!
# One-dimensional facts for the typed cap / slab certificates (CoerceCert)

The typed three-point bound uses class minorants `H_cls ≤ phi` of the pair potential
`phi t = (√(2 - 2t))⁻¹`.  For a polynomial `H = Q / Dq` write `y = √(2 - 2t) / 2 ∈ (0, 1]`, so
`t = 1 - 2 y²`, `phi = 1 / (2 y)` and

  `phi t - H t = F(y) / (2 y Dq)`,   `F(y) = Dq - 2 y Q(1 - 2 y²)`,

a *polynomial* in `y` (no square roots, no sign case split).  Hence

* `H ≤ phi` on a `y`-interval is the polynomial inequality `F ≥ 0` (`PlainCert`);
* exact double contact at a rational node `y = p / q` is the factorisation `F = (q y - p)² G`
  (`Contact1`; two nodes: `Contact2`; simple contact at the boundary `y = 1`: `ContactA`), and
  `G ≥ g0 > 0` gives *coercivity*: `phi - H ≤ δ` forces `y` (hence `t`) close to the node.

Positivity of a polynomial on a rational `y`-interval is certified by exact Bernstein pieces
(`BPiece`), checked by list arithmetic in the kernel (no SDP data, no rounding).
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. Polynomial helpers and Bernstein pieces -/

/-- Power of an integer polynomial. -/
def ppow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => pmul p (ppow p n)

/-- The Bernstein sum `Σ_i β_i a^i b^(n-i)` (`i` is the running index). -/
def bernSum (a b : List ℤ) (n : ℕ) : ℕ → List ℕ → List ℤ
  | _, [] => []
  | i, β :: bs =>
    padd (pscale (β : ℤ) (pmul (ppow a i) (ppow b (n - i)))) (bernSum a b n (i + 1) bs)

/-- A Bernstein piece on the rational interval `[u1/u2, w1/w2]`:
`Lam * P = Σ_i β_i (u2 y - u1)^i (w1 - w2 y)^(n-i)` with `β_i ≥ 0` and `n = length β - 1`. -/
structure BPiece where
  u1 : ℤ
  u2 : ℕ
  w1 : ℤ
  w2 : ℕ
  Lam : ℕ
  β : List ℕ

/-- The difference polynomial `Lam * P - Σ β_i (u2 y - u1)^i (w1 - w2 y)^(n-i)`. -/
def BPiece.diff (P : List ℤ) (c : BPiece) : List ℤ :=
  padd (pscale (c.Lam : ℤ) P)
    (pneg (bernSum [-c.u1, (c.u2 : ℤ)] [c.w1, -(c.w2 : ℤ)] (c.β.length - 1) 0 c.β))

/-- The check of one piece: positive scales and vanishing difference. -/
def BPiece.check (P : List ℤ) (c : BPiece) : Bool :=
  0 < c.Lam && 0 < c.u2 && 0 < c.w2 && (c.diff P).all (· == 0)

/-- A chain of Bernstein pieces covering the rational `y`-interval `[l1/l2, r1/r2]`: every piece
passes, the first starts at or before `l`, each next piece starts at or before the end of the
previous one, and the last one ends at or after `r`. -/
def chainOK (P : List ℤ) : List BPiece → ℤ → ℕ → ℤ → ℕ → Bool
  | [], _, _, _, _ => false
  | c :: cs, l1, l2, r1, r2 =>
    c.check P && decide (c.u1 * l2 ≤ l1 * c.u2) &&
      (decide (r1 * c.w2 ≤ c.w1 * r2) || chainOK P cs c.w1 c.w2 r1 r2)

/-! ## B. The substitution `y = √(2 - 2t) / 2` -/

/-- `y = √(2 - 2t) / 2`, so that `t = 1 - 2 y²` and `phi t = 1 / (2 y)`. -/
noncomputable def yOf (t : ℝ) : ℝ := √(2 - 2 * t) / 2

/-- The polynomial `F(y) = Dq - 2 y Q(1 - 2 y²)`. -/
def Fpoly (Q : List ℤ) (Dq : ℕ) : List ℤ := padd [(Dq : ℤ)] (pneg (pmul [0, 2] (compQ Q)))

/-! ## C. Plain certificates: `H ≤ phi` on a `y`-interval -/

/-! ## D. Contact certificates with coercivity -/

/-- The linear factor `q y - p`. -/
def lin (p q : ℕ) : List ℤ := [-(p : ℤ), (q : ℤ)]

/-- Certificate with a simple contact at the boundary node `y = 1` (`t = -1`, class `A`,
pole--pole): `F = (1 - y) G` and `G ≥ g0 > 0` on `[ya1/ya2, 1]`. -/
structure ContactA where
  Dq : ℕ
  Q : List ℤ
  G : List ℤ
  g0n : ℕ
  g0d : ℕ
  ya1 : ℤ
  ya2 : ℕ
  pieces : List BPiece

/-- The check of a boundary-node certificate. -/
def ContactA.check (c : ContactA) : Bool :=
  0 < c.Dq && 0 < c.g0n && 0 < c.g0d && 0 < c.ya2 &&
    (padd (Fpoly c.Q c.Dq) (pneg (pmul [1, -1] c.G))).all (· == 0) &&
    chainOK (padd (pscale (c.g0d : ℤ) c.G) (pneg [(c.g0n : ℤ)])) c.pieces c.ya1 c.ya2 1 1

/-! ## E. Shapes of the hypotheses `hA hB hC` of `cap_of_typed_tube7` and closeness of the nodes -/

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce

section Asm_Coerce2
/-!
# Relaxed contact certificates (Coerce2)

`Coerce.Contact1` / `Contact2` need an *exact* double root of `F` at a rational node, which integer
SDP data cannot provide.  Here the factorisation is relaxed to

  `s · F = (q y - p)² · G + R`   (resp. `(q1 y - p1)² (q2 y - p2)² · G + R`)

with integers `s > 0`, polynomials `G, R` with `G ≥ g0 > 0` and `R ≥ 0` on `[0, 1]` (both by exact
Bernstein chains).  Then `F ≥ 0` on `[0, 1]` (so `H ≤ phi`), and `F ≤ 2 Dq δ` forces
`g0 (q y - p)² ≤ 2 s Dq δ`, i.e. the same coercivity as in the exact case with `Dq` replaced by
`s Dq`.
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. One node -/

/-- Relaxed one-node certificate (class `B`): `s F = (q y - p)² G + R`, `G ≥ g0`, `R ≥ 0`. -/
structure Contact1R where
  Dq : ℕ
  Q : List ℤ
  p : ℕ
  q : ℕ
  s : ℕ
  G : List ℤ
  R : List ℤ
  g0n : ℕ
  g0d : ℕ
  pieces : List BPiece
  piecesR : List BPiece

/-- The check of a relaxed one-node certificate. -/
def Contact1R.check (c : Contact1R) : Bool :=
  0 < c.Dq && 0 < c.q && 0 < c.s && 0 < c.g0n && 0 < c.g0d &&
    (padd (pscale (c.s : ℤ) (Fpoly c.Q c.Dq))
      (pneg (padd (pmul (pmul (lin c.p c.q) (lin c.p c.q)) c.G) c.R))).all (· == 0) &&
    chainOK (padd (pscale (c.g0d : ℤ) c.G) (pneg [(c.g0n : ℤ)])) c.pieces 0 1 1 1 &&
    chainOK c.R c.piecesR 0 1 1 1

/-! ## B. Two nodes -/

/-- Relaxed two-node certificate (class `C`): `s F = (q1 y - p1)² (q2 y - p2)² G + R`. -/
structure Contact2R where
  Dq : ℕ
  Q : List ℤ
  p1 : ℕ
  q1 : ℕ
  p2 : ℕ
  q2 : ℕ
  s : ℕ
  G : List ℤ
  R : List ℤ
  g0n : ℕ
  g0d : ℕ
  pieces : List BPiece
  piecesR : List BPiece

/-- The check of a relaxed two-node certificate. -/
def Contact2R.check (c : Contact2R) : Bool :=
  0 < c.Dq && 0 < c.q1 && 0 < c.q2 && 0 < c.s && 0 < c.g0n && 0 < c.g0d &&
    (padd (pscale (c.s : ℤ) (Fpoly c.Q c.Dq))
      (pneg (padd (pmul (pmul (pmul (lin c.p1 c.q1) (lin c.p1 c.q1))
        (pmul (lin c.p2 c.q2) (lin c.p2 c.q2))) c.G) c.R))).all (· == 0) &&
    chainOK (padd (pscale (c.g0d : ℤ) c.G) (pneg [(c.g0n : ℤ)])) c.pieces 0 1 1 1 &&
    chainOK c.R c.piecesR 0 1 1 1

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce2

section Asm_CertF
/-! # Fast (linear-traversal) checking of sum-of-squares blocks

The blocks `⟨d, l, Δ⟩` of `Cert1` are read by random access (`List.getD`), which costs `O(r³)`
kernel steps per block.  Here the same quadratic form and the same positivity check are
implemented by traversing the coefficient lists once, and proved equivalent to the random-access
versions.  Also: packed integer data (one natural-number literal per array, decoded in the kernel).
-/

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Packed integer data -/

/-- `n` signed fields of `B` bits (offset binary, least significant first) packed in `x`. -/
def unpackI (B : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | n + 1, x =>
    (((x % (1 <<< B) : ℕ) : ℤ) - ((1 <<< (B - 1) : ℕ) : ℤ)) :: unpackI B n (x >>> B)

/-- `rows` rows of `cols` fields of `B` bits each. -/
def unpackM (B cols : ℕ) : ℕ → ℕ → List (List ℤ)
  | 0, _ => []
  | rows + 1, x =>
    unpackI B cols (x % (1 <<< (B * cols))) :: unpackM B cols rows (x >>> (B * cols))

/-- A block `⟨d, l, Δ⟩` of size `r` from three packed integers with field widths `Bd Bl BD`. -/
def mkBlk (r Bd Bl BD xd xl xD : ℕ) : Blk :=
  ⟨unpackI Bd r xd, unpackM Bl r r xl, unpackM BD r r xD⟩

/-! ## The quadratic form of a block, by list traversal -/

/-- The value of the monomial with exponent triple `τ`. -/
noncomputable def mv (u v t : ℝ) (τ : ℕ × ℕ × ℕ) : ℝ := u ^ τ.1 * v ^ τ.2.1 * t ^ τ.2.2

/-- `∑_a x_a z_a` where `z_a` runs through the monomials `τs` (missing `x_a` count as `0`). -/
def linF : List (ℕ × ℕ × ℕ) → List ℤ → Ex
  | [], _ => c 0
  | τ :: τs, xs => add (smulNZ (xs.headD 0) (mon τ.1 τ.2.1 τ.2.2)) (linF τs xs.tail)

/-- `∑_q d_q (l_q · z)²` with `q` running through the list `fs` (only its length matters). -/
def sqF (zs : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → List ℤ → List (List ℤ) → Ex
  | [], _, _ => c 0
  | _ :: fs, ds, ls =>
    add (smulNZ (ds.headD 0) (sq (linF zs (ls.headD [])))) (sqF zs fs ds.tail ls.tail)

/-- `∑_c x_c z_a z_c` along a row. -/
def rowF (ta : ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) → List ℤ → Ex
  | [], _ => c 0
  | τ :: τs, xs =>
    add (smulNZ (xs.headD 0) (mon (ta.1 + τ.1) (ta.2.1 + τ.2.1) (ta.2.2 + τ.2.2)))
      (rowF ta τs xs.tail)

/-- `∑_{a,c} Δ_{ac} z_a z_c`. -/
def quadF (zs : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → List (List ℤ) → Ex
  | [], _ => c 0
  | ta :: tas, rows => add (rowF ta zs (rows.headD [])) (quadF zs tas rows.tail)

/-- The quadratic form `∑_q d_q (l_q · z)² + zᵀ Δ z` of a block, built by list traversal. -/
def sqfF (b : Blk) (zs : List (ℕ × ℕ × ℕ)) : Ex :=
  add (sqF zs zs b.d b.l) (quadF zs zs b.Δ)

/-! ## The positivity check, by list traversal -/

/-- The first `n` columns of a matrix, as rows (short rows padded with `0`). -/
def transposeSq : ℕ → List (List ℤ) → List (List ℤ)
  | 0, _ => []
  | n + 1, M => (M.map fun row => row.headD 0) :: transposeSq n (M.map List.tail)

/-- `∑_{j ≠ i} |x_j|` along a list whose first position is `k`. -/
def offAbs (i : ℕ) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | k, x :: xs => (if i = k then 0 else |x|) + offAbs i (k + 1) xs

/-- Diagonal dominance of all rows (row `i` counted from `k`). -/
def domAll : ℕ → List (List ℤ) → Bool
  | _, [] => true
  | k, row :: rows => decide (offAbs k 0 row ≤ row.getD k 0) && domAll (k + 1) rows

/-- The fast computable check: pivots nonnegative, `Δ` symmetric and diagonally dominant. -/
def okF (r : ℕ) (b : Blk) : Bool :=
  b.d.all (fun x => decide (0 ≤ x)) &&
  decide (b.Δ.map (List.take r) = transposeSq r b.Δ) &&
  domAll 0 b.Δ

end Cert
end ThomsonN7

end Asm_CertF

section Asm_CertT
namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Multiplier atoms of the typed certificates -/

/-- The multiplier with code `j`: those of `codeE` (`G` is code `3`, `1 - x` are codes `4, 6, 8`,
the cut `ad·x - an` are codes `10, 11, 12`), and code `13`, the band `bn - bd·u`. -/
def codeT (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (j : ℕ) : Ex :=
  if j = 13 then sub (c bn) (smul bd U) else codeE an ad j

/-- The product of the multipliers with the given codes (`[]` is `1`). -/
def gT (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (g : List ℕ) : Ex :=
  g.foldr (fun code acc => mul (codeT an ad bn bd code) acc) (c 1)

/-- A typed SOS block: multiplier codes `g`, monomial basis `z`, and the Gram data (pivots `d`,
columns `l`, remainder `Δ`) packed into three integers `xd xl xD` with field widths `Bd Bl BD`
(`r` is the size of the block). -/
structure TBlk where
  g : List ℕ
  z : List (ℕ × ℕ × ℕ)
  r : ℕ
  Bd : ℕ
  Bl : ℕ
  BD : ℕ
  xd : ℕ
  xl : ℕ
  xD : ℕ

/-- The Gram data of a typed block. -/
def TBlk.B (s : TBlk) : Blk := mkBlk s.r s.Bd s.Bl s.BD s.xd s.xl s.xD

/-- The polynomial `g · (zᵀ M z)` of a typed SOS block. -/
def tblkE (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlk) : Ex :=
  mul (gT an ad bn bd s.g) (sqfF s.B s.z)

/-! ## Kronecker values of the quadratic form of a block -/

/-- The Kronecker weight `2^(w · code)` of the `a`-th basis monomial. -/
def kw (w D : ℕ) (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) : ℤ :=
  ((2 ^ (w * ((zt zs a).1 + D * (zt zs a).2.1 + D * D * (zt zs a).2.2)) : ℕ) : ℤ)

/-- The value of the quadratic form `∑_q d_q (l_q · P)² + Pᵀ Δ P` of a block at the weights `P`. -/
def sqfVal (b : Blk) (n : ℕ) (P : ℕ → ℤ) : ℤ :=
  ∑ q ∈ Finset.range n, b.dq q * (∑ a ∈ Finset.range n, b.lq q a * P a) ^ 2
    + ∑ a ∈ Finset.range n, ∑ c ∈ Finset.range n, P a * b.del a c * P c

/-! ## Size bounds of packed blocks -/

/-! ### Degrees -/

/-- The coordinate `k` (`0, 1, 2`) of an exponent triple. -/
def proj (k : ℕ) (τ : ℕ × ℕ × ℕ) : ℕ := if k = 0 then τ.1 else if k = 1 then τ.2.1 else τ.2.2

/-- The degree of an expression in the variable with code `k`. -/
def degK (k : ℕ) : Ex → ℕ
  | .c _ => 0
  | .mon a b d => proj k (a, b, d)
  | .add p q => max (degK k p) (degK k q)
  | .mul p q => degK k p + degK k q

/-- The largest coordinate `k` among the exponent triples `zs`. -/
def mxs (k : ℕ) (zs : List (ℕ × ℕ × ℕ)) : ℕ := (zs.map (proj k)).foldr max 0

/-! ## Analytic bounds of typed blocks -/

/-- Well-formedness of the packed data of a block (positive widths, size matches the basis). -/
def TBlk.wf (s : TBlk) : Bool :=
  decide (0 < s.Bd) && decide (0 < s.Bl) && decide (0 < s.BD) && decide (s.z.length = s.r)

/-- An analytic bound on the `ℓ¹`-norm of the quadratic form of a packed block. -/
def TBlk.l1B (s : TBlk) : ℕ :=
  s.z.length * (2 ^ (s.Bd - 1) * (s.z.length * 2 ^ (s.Bl - 1)) ^ 2)
    + s.z.length * (s.z.length * 2 ^ (s.BD - 1))

/-! ## Sums of expressions -/

/-! ## The hybrid check -/

/-- The identity tree `Fx - ∑ g · Q` (never evaluated by the kernel: only its proof-level
properties are used). -/
def idT (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk) : Ex :=
  sub Fx (sumE (S.map (tblkE an ad bn bd)))

/-- The analytic bound on the `ℓ¹`-norm of the identity. -/
def idL (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk) : ℕ :=
  Fx.l1 + (S.map fun s => (gT an ad bn bd s.g).l1 * s.l1B).sum

/-- The analytic bound on the degree of the identity in the variable `k`. -/
def idDeg (k : ℕ) (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk) : ℕ :=
  max (degK k Fx) ((S.map fun s => degK k (gT an ad bn bd s.g) + 2 * mxs k s.z).foldr max 0)

/-- The Kronecker digit width. -/
def hybW (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk) : ℕ :=
  Nat.log2 (idL Fx an ad bn bd S) + 1

/-- The Kronecker degree bound. -/
def hybD (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk) : ℕ :=
  max (idDeg 0 Fx an ad bn bd S) (max (idDeg 1 Fx an ad bn bd S) (idDeg 2 Fx an ad bn bd S)) + 1

/-- The Kronecker value of the identity, the quadratic forms of the `S`-blocks being evaluated
by `fq`. -/
def hybVal (fq : ℕ → ℕ → TBlk → ℤ) (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ)
    (S : List TBlk) : ℤ :=
  Fx.kev (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S)
    - (S.map fun s => (gT an ad bn bd s.g).kev (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S)
        * fq (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S) s).sum

/-- The hybrid Kronecker check. -/
def hybChk (fq : ℕ → ℕ → TBlk → ℤ) (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ)
    (S : List TBlk) : Bool :=
  S.all TBlk.wf && decide (hybVal fq Fx an ad bn bd S = 0)

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

/-! # Flat (Nat-only inner loops) evaluation of the quadratic form of a packed block -/

/-- The offset of `B`-bit offset-binary fields. -/
def offB (B : ℕ) : ℤ := ((1 <<< (B - 1) : ℕ) : ℤ)

/-- `∑_a f_a * ps_a`, where `f_a` are the successive `B`-bit fields of `x`. -/
def dotN (B : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, x => (x % (1 <<< B)) * p + dotN B ps (x >>> B)

/-- One `dotN` for each of `rows` rows of `cols` fields of `B` bits. -/
def rowsN (B cols : ℕ) (ps : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | rows + 1, x => dotN B ps (x % (1 <<< (B * cols))) :: rowsN B cols ps rows (x >>> (B * cols))

/-- The `q`-th term: `(dfield_q - offd) * (L_q - offl * Pt)²`. -/
def comb1 (Bd Bl : ℕ) (Pt : ℤ) : List ℕ → ℕ → ℤ
  | [], _ => 0
  | L :: Ls, xd =>
    (((xd % (1 <<< Bd) : ℕ) : ℤ) - offB Bd)
        * (((L : ℤ) - offB Bl * Pt) * ((L : ℤ) - offB Bl * Pt))
      + comb1 Bd Bl Pt Ls (xd >>> Bd)

/-- `∑_a P_a * (D_a - offD * Pt)`. -/
def comb2 (BD : ℕ) (Pt : ℤ) : List ℕ → List ℕ → ℤ
  | p :: ps, Dv :: Ds => (p : ℤ) * ((Dv : ℤ) - offB BD * Pt) + comb2 BD Pt ps Ds
  | _, _ => 0

/-- The Kronecker weights `2^(w (x + D y + D² z))` of the monomials. -/
def weights (w D : ℕ) (z : List (ℕ × ℕ × ℕ)) : List ℕ :=
  z.map fun τ => 2 ^ (w * (τ.1 + D * τ.2.1 + D * D * τ.2.2))

/-- The Kronecker value of the quadratic form of a packed block, by flat Nat folds. -/
def fqFlat (w D : ℕ) (s : TBlk) : ℤ :=
  comb1 s.Bd s.Bl ((weights w D s.z).sum : ℕ) (rowsN s.Bl s.r (weights w D s.z) s.r s.xl) s.xd
    + comb2 s.BD ((weights w D s.z).sum : ℕ) (weights w D s.z)
      (rowsN s.BD s.r (weights w D s.z) s.r s.xD)

/-- The evaluator used by the certificates: the flat `Nat`-only version. -/
def fqCur (w D : ℕ) (s : TBlk) : ℤ := fqFlat w D s

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint
open scoped RealInnerProductSpace

/-! ## One-variable polynomials, marginals, kernel sums -/

/-- `∑_j h_j x^j` in the first variable. -/
def h1E (h : List ℤ) : Ex :=
  sumRange h.length fun j => smulNZ (h.getD j 0) (mon j 0 0)

/-- `∑_j h_j x^j` at the variable with code `i`. -/
def hvE (h : List ℤ) (i : ℕ) : Ex := sbst i 3 3 (h1E h)

/-- The marginal `S(1,x,x) + S(x,1,x) + S(x,x,1)` at the variable with code `i`. -/
def gmE (S : Ex) (i : ℕ) : Ex := add (add (sbst 3 i i S) (sbst i 3 i S)) (sbst i i 3 S)

/-- `Λ · ∑_{k<K} Fp_k`, for the blocks `bl` (of sizes `m k`). -/
def SE (K : ℕ) (m : ℕ → ℕ) (bl : ℕ → Blk) : Ex := sumRange K fun k => fkE (m k) (bl k) k

/-- The real polynomial `x ↦ (∑_j h_j x^j) / Λ`. -/
noncomputable def polyR (Lam : ℕ) (h : List ℤ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * x ^ j) / Lam

/-! ## The three type slacks, scaled to integer polynomials -/

/-- `5 Λ · lamA` as an expression. -/
def lamAE (HA ψBa : List ℤ) (cal : ℤ) (SP SR : Ex) : Ex :=
  sub (add (add (sub (hvE HA 0) (smul 2 (gmE SP 0))) (smul 5 (hvE ψBa 1))) (smul 5 (hvE ψBa 2)))
    (add (c (5 * cal))
      (smul 10 (add (add (sbst 0 1 2 SP) (sbst 0 2 1 SP)) (sbst 1 2 0 SR))))

/-- `4 Λ · lamB` as an expression. -/
def lamBE (HB ψBa ψCb : List ℤ) (cbe : ℤ) (SP SR : Ex) : Ex :=
  sub (add (add
      (sub (sub (sub (hvE HB 0) (gmE SP 0)) (gmE SR 0)) (hvE ψBa 0))
      (sub (sub (sub (hvE HB 1) (gmE SP 1)) (gmE SR 1)) (hvE ψBa 1)))
      (smul 4 (hvE ψCb 2)))
    (add (c (4 * cbe))
      (smul 8 (add (add (sbst 0 1 2 SP) (sbst 0 2 1 SR)) (sbst 1 2 0 SR))))

/-- The ring-vertex term `(HC - 2 gm SR - 2 ψCb)(x_i)`. -/
def tgE (HC ψCb : List ℤ) (SR : Ex) (i : ℕ) : Ex :=
  sub (sub (hvE HC i) (smul 2 (gmE SR i))) (smul 2 (hvE ψCb i))

/-- `30 Λ · lamG` as an expression. -/
def lamGE (HC ψCb : List ℤ) (e cal cbe : ℤ) (SP SR : Ex) : Ex :=
  sub (smul 10 (add (add (tgE HC ψCb SR 0) (tgE HC ψCb SR 1)) (tgE HC ψCb SR 2)))
    (add (smul 3 (add (add (add (c e) (smul 2 (sbst 3 3 3 SP))) (smul 5 (sbst 3 3 3 SR)))
        (c (-5 * cal - 20 * cbe))))
      (smul 60 (add (add (sbst 0 1 2 SR) (sbst 0 2 1 SR)) (sbst 1 2 0 SR))))

section RealSide

variable (K : ℕ) (m : ℕ → ℕ) (Lam : ℕ) (blP blR : ℕ → Blk)

end RealSide

/-! ## The certificate -/

/-- A typed three-point certificate for `n = 7` (poles `0, 1`, ring points `2..6`), all over the
common denominator `Λ = Lam`: the cut is `a = an / ad ≤ ` every pair value, and the pole-pole value
lies in `[a, b]`, `b = bn / bd`.  `HA, HB, HC, ψBa, ψCb` are the integer coefficient lists of the
polynomials (times `Λ`); `e, cal, cbe` are integers (times `Λ`); `FP, FR` are the `F`-blocks of
sizes `dd + 1 - k`, `k = 0, …, dd`; `SA, SB, SG` are the typed SOS blocks, with the positive
integer scalings `mA, mB, mG` of the three identities. -/
structure TCert where
  dd : ℕ
  Lam : ℕ
  an : ℤ
  ad : ℕ
  bn : ℤ
  bd : ℕ
  e : ℤ
  cal : ℤ
  cbe : ℤ
  HA : List ℤ
  HB : List ℤ
  HC : List ℤ
  ψBa : List ℤ
  ψCb : List ℤ
  FP : List Blk
  FR : List Blk
  mA : ℕ
  mB : ℕ
  mG : ℕ
  SA : List TBlk
  SB : List TBlk
  SG : List TBlk

namespace TCert

variable (cf : TCert)

/-- The number of `F`-blocks. -/
def K : ℕ := cf.dd + 1

/-- The size of the `k`-th `F`-block. -/
def m (k : ℕ) : ℕ := cf.dd + 1 - k

/-- The `k`-th `F`-block of the pole colour. -/
def blkP (k : ℕ) : Blk := cf.FP.getD k Blk.empty

/-- The `k`-th `F`-block of the ring colour. -/
def blkR (k : ℕ) : Blk := cf.FR.getD k Blk.empty

/-- `Λ ·` (pole kernel) as an expression. -/
def SPE : Ex := SE cf.K cf.m cf.blkP

/-- `Λ ·` (ring kernel) as an expression. -/
def SRE : Ex := SE cf.K cf.m cf.blkR

/-- The left-hand side of the identity for the pole-pole-ring slack. -/
def FA : Ex := smul cf.mA (lamAE cf.HA cf.ψBa cf.cal cf.SPE cf.SRE)

/-- The left-hand side of the identity for the pole-ring-ring slack. -/
def FB : Ex := smul cf.mB (lamBE cf.HB cf.ψBa cf.ψCb cf.cbe cf.SPE cf.SRE)

/-- The left-hand side of the identity for the ring-ring-ring slack. -/
def FG : Ex := smul cf.mG (lamGE cf.HC cf.ψCb cf.e cf.cal cf.cbe cf.SPE cf.SRE)

/-- The identity for the pole-pole-ring slack. -/
def idA : Ex := idT cf.FA cf.an cf.ad cf.bn cf.bd cf.SA

/-- The identity for the pole-ring-ring slack (no band: `bn = bd = 1`). -/
def idB : Ex := idT cf.FB cf.an cf.ad 1 1 cf.SB

/-- The identity for the ring-ring-ring slack (no band: `bn = bd = 1`). -/
def idG : Ex := idT cf.FG cf.an cf.ad 1 1 cf.SG

/-- The Kronecker check of the identity `idA`. -/
def chkA : Bool := hybChk fqCur cf.FA cf.an cf.ad cf.bn cf.bd cf.SA

/-- The Kronecker check of the identity `idB`. -/
def chkB : Bool := hybChk fqCur cf.FB cf.an cf.ad 1 1 cf.SB

/-- The Kronecker check of the identity `idG`. -/
def chkG : Bool := hybChk fqCur cf.FG cf.an cf.ad 1 1 cf.SG

/-- The cheap checks: positivity of the denominators and scalings, and the positive semidefinite
certificates of all blocks. -/
def checkMeta : Bool :=
  decide (0 < cf.Lam) && (decide (0 < cf.ad) && (decide (0 < cf.bd) &&
  (decide (0 < cf.mA) && (decide (0 < cf.mB) && (decide (0 < cf.mG) &&
  ((List.range cf.K).all (fun k => (cf.blkP k).ok (cf.m k)) &&
  ((List.range cf.K).all (fun k => (cf.blkR k).ok (cf.m k)) &&
  (cf.SA.all (fun s => okF s.z.length s.B) &&
  (cf.SB.all (fun s => okF s.z.length s.B) &&
  cf.SG.all (fun s => okF s.z.length s.B))))))))))

/-! ### The real data of a certificate -/

/-- The pole-colour `F`-matrices. -/
noncomputable def FPm (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blkP k)

/-- The ring-colour `F`-matrices. -/
noncomputable def FRm (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blkR k)

/-- The polynomial `H_A`. -/
noncomputable def HAf : ℝ → ℝ := polyR cf.Lam cf.HA

/-- The polynomial `H_B`. -/
noncomputable def HBf : ℝ → ℝ := polyR cf.Lam cf.HB

/-- The polynomial `H_C`. -/
noncomputable def HCf : ℝ → ℝ := polyR cf.Lam cf.HC

/-- The polynomial `ψ_Ba`. -/
noncomputable def ψBaf : ℝ → ℝ := polyR cf.Lam cf.ψBa

/-- The polynomial `ψ_Cb`. -/
noncomputable def ψCbf : ℝ → ℝ := polyR cf.Lam cf.ψCb

/-- The constant `e`. -/
noncomputable def ef : ℝ := (cf.e : ℝ) / cf.Lam

/-- The constant `cal`. -/
noncomputable def calf : ℝ := (cf.cal : ℝ) / cf.Lam

/-- The constant `cbe`. -/
noncomputable def cbef : ℝ := (cf.cbe : ℝ) / cf.Lam

/-- The lower cut `alo = amin = an / ad`. -/
noncomputable def alo : ℝ := (cf.an : ℝ) / cf.ad

/-- The upper cut `ahi = bn / bd` on the pole-pole value. -/
noncomputable def ahi : ℝ := (cf.bn : ℝ) / cf.bd

end TCert

end Cert
end ThomsonN7

end Asm_CertT

section Asm_SlabHead
/-!
# One-dimensional facts for the typed slab certificates: `H ≤ φ` on an interval

`φ(t) = (√(2 - 2t))⁻¹`.  For `t < 1` put `y = √((1 - t)/2) > 0`, so that `t = 1 - 2 y²` and
`φ(t) = 1/(2y)`.  A polynomial `H(t) = Q(t)/Lam` satisfies `H ≤ φ` iff `q(y) = Lam - 2 y Q(1 - 2y²) ≥ 0`.

A certificate for `q ≥ 0` on `{ν₂ y² ≤ μ₂}` (i.e. `t ≥ lo`) or `{ν₂ y² ≤ μ₂, μ₁ ≤ ν₁ y²}`
(i.e. `lo ≤ t ≤ hi`) is an exact polynomial identity

  `m · Lam · q(y) = Σ_T mult_T(y) · Σ (weight · square)`

where `mult_T` is a product of a subset of the atoms `y`, `μ₂ - ν₂ y²`, `ν₁ y² - μ₁`, and all
weights are natural numbers.  The identity is checked by kernel evaluation of integer polynomials.
-/

namespace ThomsonN7
namespace SlabOneD

/-- Integer polynomial (low degree first) evaluated at a real point. -/
def peval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, y => (a : ℝ) + y * peval as y

/-- Sum of integer polynomials. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- Scalar multiple. -/
def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

/-- Negation. -/
def pneg (p : List ℤ) : List ℤ := p.map (- ·)

/-- Product. -/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, q => padd (pscale a q) (0 :: pmul as q)

/-- `Q(1 - 2 y²)` for `Q` given by its coefficient list. -/
def compQ : List ℤ → List ℤ
  | [] => []
  | c :: cs => padd [c] (pmul [1, 0, -2] (compQ cs))

/-- Weighted sum of squares `Σ d ρ²` (integer polynomial). -/
def sqSum : List (ℕ × List ℤ) → List ℤ
  | [] => []
  | (d, r) :: rs => padd (pscale d (pmul r r)) (sqSum rs)

/-- Real-valued weighted sum of squares. -/
def sqEval (L : List (ℕ × List ℤ)) (y : ℝ) : ℝ := (L.map fun x => (x.1 : ℝ) * peval x.2 y ^ 2).sum

/-- The interval parameters: `t ≥ lo` reads `ν₂ (1 - t) ≤ 2 μ₂` and `t ≤ hi` reads `2 μ₁ ≤ ν₁ (1 - t)`. -/
structure Par where
  mu2 : ℤ
  nu2 : ℤ
  mu1 : ℤ
  nu1 : ℤ

/-- One multiplier term: the flags say which of the atoms `y`, `μ₂ - ν₂ y²`, `ν₁ y² - μ₁`
occur in the multiplier; `sq` is the weighted sum of squares it multiplies. -/
structure Term where
  fy : Bool
  f2 : Bool
  f1 : Bool
  sq : List (ℕ × List ℤ)

/-- The multiplier polynomial of a term. -/
def Term.mult (P : Par) (T : Term) : List ℤ :=
  pmul (if T.fy then [0, 1] else [1])
    (pmul (if T.f2 then [P.mu2, 0, -P.nu2] else [1]) (if T.f1 then [-P.mu1, 0, P.nu1] else [1]))

/-- Sum over the terms of `mult * sqSum`. -/
def sumTerms (P : Par) : List Term → List ℤ
  | [] => []
  | T :: Ts => padd (pmul (T.mult P) (sqSum T.sq)) (sumTerms P Ts)

/-- Data of a certificate for `H = Q / Lam`. -/
structure Cert where
  m : ℕ
  Lam : ℕ
  Q : List ℤ
  terms : List Term

/-- `m (Lam - 2 y Q(1 - 2y²)) - Σ mult * squares`. -/
def Cert.diff (P : Par) (c : Cert) : List ℤ :=
  padd (pscale c.m (padd [(c.Lam : ℤ)] (pneg (pmul [0, 2] (compQ c.Q)))))
    (pneg (sumTerms P c.terms))

/-! ## Fast check by evaluation at a large integer point (Kronecker substitution)

If an integer polynomial `R` satisfies `R(X) = 0` and all its coefficients have absolute value
`< X`, then `R = 0`.  The coefficient bound is obtained from `ℓ¹`-norm majorants along the same
expression tree as the identity, so the kernel only evaluates a few hundred big-integer operations
instead of expanding all polynomial products. -/

/-- Horner evaluation of an integer polynomial at an integer point. -/
def evalZ : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: as, x => a + x * evalZ as x

/-- Evaluation of `Σ d ρ²` at an integer point. -/
def sqSumZ (X : ℤ) : List (ℕ × List ℤ) → ℤ
  | [] => 0
  | (d, r) :: rs => (d : ℤ) * (evalZ r X * evalZ r X) + sqSumZ X rs

/-- Evaluation of the multiplier of a term at an integer point. -/
def multZ (P : Par) (X : ℤ) (T : Term) : ℤ :=
  cond T.fy X 1 * (cond T.f2 (P.mu2 - P.nu2 * (X * X)) 1 * cond T.f1 (P.nu1 * (X * X) - P.mu1) 1)

/-- Evaluation of `Σ mult * squares` at an integer point. -/
def sumTermsZ (P : Par) (X : ℤ) : List Term → ℤ
  | [] => 0
  | T :: Ts => multZ P X T * sqSumZ X T.sq + sumTermsZ P X Ts

/-- The identity `m (Lam - 2 y Q(1 - 2y²)) - Σ mult * squares` evaluated at `y = X`. -/
def Cert.diffZ (P : Par) (c : Cert) (X : ℤ) : ℤ :=
  (c.m : ℤ) * ((c.Lam : ℤ) - 2 * X * evalZ c.Q (1 - 2 * (X * X))) - sumTermsZ P X c.terms

/-- The `ℓ¹` norm of an integer polynomial. -/
def l1 : List ℤ → ℕ
  | [] => 0
  | a :: as => a.natAbs + l1 as

/-- Majorant of `ℓ¹ (compQ Q)`. -/
def cqB : List ℤ → ℕ
  | [] => 0
  | c :: cs => c.natAbs + 3 * cqB cs

/-- Majorant of `ℓ¹ (sqSum L)`. -/
def sqSumB : List (ℕ × List ℤ) → ℕ
  | [] => 0
  | (d, r) :: rs => d * (l1 r * l1 r) + sqSumB rs

/-- Majorant of `ℓ¹` of the multiplier of a term. -/
def multB (P : Par) (T : Term) : ℕ :=
  cond T.f2 (P.mu2.natAbs + P.nu2.natAbs) 1 * cond T.f1 (P.mu1.natAbs + P.nu1.natAbs) 1

/-- Majorant of `ℓ¹ (sumTerms P Ts)`. -/
def sumTermsB (P : Par) : List Term → ℕ
  | [] => 0
  | T :: Ts => multB P T * sqSumB T.sq + sumTermsB P Ts

/-- A bound for the absolute values of all coefficients of the identity polynomial. -/
def Cert.bound (P : Par) (c : Cert) : ℕ := c.m * (c.Lam + 2 * cqB c.Q) + sumTermsB P c.terms

/-- The check: positivity of the scales and vanishing of the identity at `y = 2 bound + 2`, a point
larger than twice every coefficient of the identity polynomial. -/
def Cert.check (P : Par) (c : Cert) : Bool :=
  0 < c.m && 0 < c.Lam && c.diffZ P (2 * (c.bound P : ℤ) + 2) == 0

end SlabOneD
end ThomsonN7

end Asm_SlabHead

section Asm_Bridge
/-!
# Bridge: the certificate checker `Cert.TCert.sound_lo` feeds `Glue.SlabSpec` / `Glue.CapSpec`

`TCert.sound_lo` bounds `ef` by the typed double sum `∑ i<j, H7 HAf HBf HCf i j ⟪x i, x j⟫`.
Here we restate it with the class selector `Glue.cls3` (via `Glue3.sum_H7_eq_sum_cls3`) and, for a
certificate whose four boolean checks hold, produce the final interface of `Glue4`.  The remaining
inputs are the one-dimensional facts about the minorants (`HAf ≤ phi`, ...) and the numerical
comparison of `ef` with the energy `E(P)`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

end Bridge

end Glue
end ThomsonN7

end Asm_Bridge

section Asm_Bridge1D
/-!
# Bridge1D: agent2's one-dimensional slab facts (`SlabOneD`) feed `Bridge`

`SlabOneD.peval Q t / Lam` is the polynomial `polyR Lam Q t` of `CertT`; a generated slab
`SlabOneD.Slab_x.HA_le_phi` therefore gives `HAf ≤ phi` on the slab of a certificate whose
`HA`, `Lam` are the data of `Slab_x.certHA`.
-/

namespace ThomsonN7
namespace Glue

section Bridge1D

open scoped InnerProductSpace
open Base

end Bridge1D

end Glue
end ThomsonN7

end Asm_Bridge1D

section Asm_Bridge2
/-!
# Bridge2: near-sharp cap specification from a certificate and its contact factorisations

`Bridge.capSpec_of_tcert` asks for coercive one-dimensional facts about the three minorants
`HAf, HBf, HCf` of a cap certificate.  `Coerce` produces exactly these facts from an exact
factorisation of `F = Dq - 2 y Q(1 - 2 y²)` at rational `y`-nodes (`ContactA`, `Contact1`,
`Contact2`).  Here the two are glued: the contact data are attached to a certificate `cf` by the
equalities `c.Q = cf.HX`, `c.Dq = cf.Lam`.
-/

namespace ThomsonN7
namespace Glue

section Bridge2

open scoped InnerProductSpace
open Base

end Bridge2

end Glue
end ThomsonN7

end Asm_Bridge2

section Asm_Bridge3
/-!
# Bridge3: near-sharp cap specification with relaxed contacts

Same as `Bridge2.capSpec_of_contacts`, but the pole--ring and ring--ring minorants come with the
*relaxed* factorisations `s F = (q y - p)² G + R` (`Coerce.Contact1R`, `Coerce.Contact2R`), which
integer SDP data can satisfy; the pole--pole minorant keeps the exact simple contact at `y = 1`.
-/

namespace ThomsonN7
namespace Glue

section Bridge3

open scoped InnerProductSpace
open Base

end Bridge3

end Glue
end ThomsonN7

end Asm_Bridge3

section Asm_cap_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_cap_tc

section Asm_cap_ct
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_cap_ct

section Asm_cap_capspec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_cap_capspec

section Asm_s99_98_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s99_98_tc

section Asm_s99_98_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s99_98

end Slab_s99_98

end SlabOneD
end ThomsonN7

end Asm_s99_98_1d

section Asm_s99_98_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s99_98_spec

section Asm_s98_96_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s98_96_tc

section Asm_s98_96_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s98_96

end Slab_s98_96

end SlabOneD
end ThomsonN7

end Asm_s98_96_1d

section Asm_s98_96_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s98_96_spec

section Asm_s96_94_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s96_94_tc

section Asm_s96_94_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s96_94

end Slab_s96_94

end SlabOneD
end ThomsonN7

end Asm_s96_94_1d

section Asm_s96_94_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s96_94_spec

section Asm_s94_93_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s94_93_tc

section Asm_s94_93_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s94_93

end Slab_s94_93

end SlabOneD
end ThomsonN7

end Asm_s94_93_1d

section Asm_s94_93_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s94_93_spec

section Asm_s93_90_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s93_90_tc

section Asm_s93_90_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s93_90

end Slab_s93_90

end SlabOneD
end ThomsonN7

end Asm_s93_90_1d

section Asm_s93_90_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s93_90_spec

section Asm_Final
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_Final

namespace ThomsonN7

end ThomsonN7


