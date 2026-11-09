-- Prove2me | Definitions.Def_UniformADProbes_Trace_algebra
-- name    : UniformADProbes_Trace_algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:22.64427+00:00
-- url     : https://prove2.me/theorems/ddb936ec-4087-4e16-962d-bf2f36b2b978
-- title:
--   Words, cyclic representations, differential connection, and trace polynomial
-- statement:
--   Let $x,y$ be two noncommuting generators. Integer polynomials are finite integer linear combinations of words, including the empty word $1$; their adjoint reverses words. Evaluation preserves the written multiplication order. The fixed probes are
--   $$U_{0,0}=1,\qquad U_{i+1,j}=(y+N^2(j-i))U_{i,j}+N^2xU_{i,j-1},$$
--   with zero values outside $0\le j\le i$, and lexicographic enumeration by increasing $i$, then $j$.
--
--   For real symmetric matrices $H,K$ and a seed $v$, the joint cyclic module is
--   $$\mathcal M(H,K;v)=\operatorname{span}_{\mathbb R}\{w(H,K)v:w\in\{x,y\}^*\}.$$
--   The three Gram arrays record inner products and the two generator actions on a common polynomial-response list. Pointed equivalence is a linear bijection of cyclic modules preserving the Euclidean inner product, the seed, and both generator actions. It permits different ambient dimensions and zero seeds.
--
--   The rational connection is $\nabla f=f'+(B/t+H)f$, where rational differentiation uses the polynomial quotient rule on the canonical numerator and denominator. Scalar extension is the rational-function span of constant vectors in a real subspace. Spectral diameter is the supremum minus infimum of the real spectrum, used for symmetric matrices; in zero ambient dimension its empty-spectrum value is zero.
--
--   The distance polynomials have $P_0=1$, $P_1=x$, $P_2=x^2-y$ and $P_k=xP_{k-1}-(y-1)P_{k-2}$ for $k\ge3$; $J_N=\sum_{k<N}P_k$. Set $M=N(N+1)/2$, $b_N=2N^2(3N^3)^{2(N-1)}+1$, $Y_N=\sum_{j<M}b_N^jU_j$, $Z_N=\sum_{i<M}b_N^{iM}U_i$, and $W_N=1+b_N^{M^2}x+b_N^{2M^2}y$. The defined output is
--   $$p_1=1,\qquad p_N=J_NZ_N^*W_NY_N+Y_N^*W_NZ_NJ_N^*\quad(N\ge2).$$
--
--   Adjacency is the integer $0/1$ matrix of a simple graph and the degree matrix is diagonal with its actual neighbor counts. These definitions provide the common mathematical interface of every statement; none assumes spanning, reconstruction, or a resource bound.
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), §1 equation (1); Lemma 2.1; §3 equations (7)–(12), p. 1–2, 5, 8–9 (PDF p. 2–3, 6, 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Mathlib

set_option autoImplicit false
noncomputable section

namespace UniformADProbes.Trace

abbrev Word := FreeMonoid Bool
abbrev NCPoly := MonoidAlgebra ℤ Word

def x : NCPoly := MonoidAlgebra.ofCoeff (Finsupp.single (FreeMonoid.ofList [false]) 1)
def y : NCPoly := MonoidAlgebra.ofCoeff (Finsupp.single (FreeMonoid.ofList [true]) 1)

def adjoint (p : NCPoly) : NCPoly :=
  p.coeff.sum fun w c => MonoidAlgebra.ofCoeff (Finsupp.single (FreeMonoid.ofList w.toList.reverse) c)

def wordEval {R : Type} [Ring R] (H K : R) (w : Word) : R :=
  w.toList.foldr (fun b z => (if b then K else H) * z) 1

def polyEval {R : Type} [Ring R] (H K : R) (p : NCPoly) : R :=
  p.coeff.sum fun w c => c • wordEval H K w

def probes (N : ℕ) : ℕ → ℤ → NCPoly
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j => if j < 0 ∨ (i + 1 : ℤ) < j then 0 else
      (y + ((N : ℤ)^2 * (j - (i : ℤ))) • (1 : NCPoly)) * probes N i j +
        (N : ℤ)^2 • (x * probes N i (j - 1))

def probeIndices (N : ℕ) : List (ℕ × ℕ) :=
  (List.range N).flatMap fun i => (List.range (i + 1)).map fun j => (i, j)

def probeList (N : ℕ) : List NCPoly :=
  (probeIndices N).map fun ij => probes N ij.1 (ij.2 : ℤ)

def distancePoly : ℕ → NCPoly
  | 0 => 1
  | 1 => x
  | 2 => x * x - y
  | k + 3 => x * distancePoly (k + 2) - (y - 1) * distancePoly (k + 1)

def distanceSum (N : ℕ) : NCPoly :=
  ((List.range N).map distancePoly).sum

def packingBase (N : ℕ) : ℕ :=
  2 * (N^2 * ((3 * N^3)^(N - 1))^2) + 1

def packedPoly (N : ℕ) : NCPoly :=
  if N ≤ 1 then 1 else
  let U := probeList N
  let M := N * (N + 1) / 2
  let b : ℤ := packingBase N
  let Y := ((List.range M).map fun j => b^j • U[j]!).sum
  let Z := ((List.range M).map fun i => b^(i*M) • U[i]!).sum
  let W := 1 + b^(M^2) • x + b^(2*M^2) • y
  let J := distanceSum N
  J * adjoint Z * W * Y + adjoint Y * W * Z * adjoint J

noncomputable def adjacency {n : ℕ} (T : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  by
    classical
    exact fun i j => if T.Adj i j then 1 else 0

noncomputable def degreeMatrix {n : ℕ} (T : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun i => (Set.ncard (T.neighborSet i) : ℤ)

def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map Int.cast

def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

def dot {n : ℕ} (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

def cyclicModule {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun w : Word => (wordEval H K w).mulVec v)

def responseSpan {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (U : List NCPoly) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {z | ∃ p ∈ U, z = (polyEval H K p).mulVec v}

def gramData {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (U : List NCPoly) : Fin 3 → Fin U.length → Fin U.length → ℝ :=
  fun s i j =>
    let zi := (polyEval H K U[i]).mulVec v
    let zj := (polyEval H K U[j]).mulVec v
    dot zi ((if s.val = 0 then 1 else if s.val = 1 then H else K).mulVec zj)

/-- A linear bijection preserving Euclidean inner products, the seed, and both actions.
The explicit membership clauses avoid assuming invariance of the cyclic modules. -/
def PointedEquivalent {n m : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (H' K' : Matrix (Fin m) (Fin m) ℝ) (v' : Fin m → ℝ) : Prop :=
  ∃ e : cyclicModule H K v ≃ₗ[ℝ] cyclicModule H' K' v',
    (∀ u w, dot (e u).val (e w).val = dot u.val w.val) ∧
    (∃ hv : v ∈ cyclicModule H K v, ∃ hv' : v' ∈ cyclicModule H' K' v',
      e ⟨v, hv⟩ = ⟨v', hv'⟩) ∧
    (∀ u : cyclicModule H K v,
      ∃ hH : H.mulVec u.val ∈ cyclicModule H K v,
      ∃ hK : K.mulVec u.val ∈ cyclicModule H K v,
        (e ⟨H.mulVec u.val, hH⟩).val = H'.mulVec (e u).val ∧
        (e ⟨K.mulVec u.val, hK⟩).val = K'.mulVec (e u).val)

noncomputable def spectralDiameter {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (spectrum ℝ B) - sInf (spectrum ℝ B)

noncomputable def rationalDerivative (f : RatFunc ℝ) : RatFunc ℝ :=
  (algebraMap (Polynomial ℝ) (RatFunc ℝ)
    (f.num.derivative * f.denom - f.num * f.denom.derivative)) /
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) f.denom)^2

noncomputable def connection {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → RatFunc ℝ) : Fin n → RatFunc ℝ :=
  fun i => rationalDerivative (f i) + ∑ j,
    ((algebraMap ℝ (RatFunc ℝ) (B i j)) / RatFunc.X +
      algebraMap ℝ (RatFunc ℝ) (H i j)) * f j

def scalarExtension {n : ℕ} (W : Submodule ℝ (Fin n → ℝ)) :
    Submodule (RatFunc ℝ) (Fin n → RatFunc ℝ) :=
  Submodule.span (RatFunc ℝ) {f | ∃ w ∈ W,
    f = fun i => algebraMap ℝ (RatFunc ℝ) (w i)}

def MatrixInvariant {n : ℕ} (W : Submodule ℝ (Fin n → ℝ))
    (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ w ∈ W, B.mulVec w ∈ W

end UniformADProbes.Trace


