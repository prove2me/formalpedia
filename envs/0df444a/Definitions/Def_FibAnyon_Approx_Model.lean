-- Prove2me | Definitions.Def_FibAnyon_Approx_Model
-- name    : FibAnyon_Approx_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:37.592096+00:00
-- url     : https://prove2.me/theorems/c2f14cc5-e82e-472c-bee8-1a0d44a737d2
-- title:
--   §II–§V model: cyclotomic coordinates, exact unitaries, circuits, and approximation algorithms
-- statement:
--   Let $\omega=e^{i\pi/5}$, $\tau=(\sqrt5-1)/2$, and $\varphi=(\sqrt5+1)/2$. An element of $\mathbb Z[\omega]$ is represented by its four integer coefficients in $a+b\omega+c\omega^2+d\omega^3$. Multiplication reduces powers using $\omega^4=-1+\omega-\omega^2+\omega^3$ and $\omega^5=-1$. The two embeddings used in the paper are complex evaluation and the automorphism $\omega\mapsto\omega^3$. The Gauss complexity is
--
--   $$G(u)=|u|^2+|u^\bullet|^2.$$
--
--   The model defines the paper's exact unitary $U[u,v,k]$, the $F$, $T$, and $\omega I$ gates, circuit evaluation, circuit length, $R_z(\phi)$, and the phase-invariant distance $d(U,V)=\sqrt{1-|\operatorname{tr}(UV^\dagger)|/2}$. It also defines the loops and formulas of Figures 4, 12, 13, and 15, including the Fibonacci-based real approximation, the sampled cyclotomic integer, the dark gray parallelogram $P$ of Figure 14 (imaginary part in $[y_{\min},y_{\max}]$, and projection on the direction $e^{i\theta}$ between $r\varphi^m(1-\varepsilon^2)$ and $r\varphi^m(1-\varepsilon^2/2)$), the norm-equation target $\xi$, and the final circuit. These definitions let the milestone theorems and the goal refer to actual algorithm outputs.
--
--   **Formalization Note** Circuit matrices multiply in list order, and length counts $F$ and $T$ but not the global phase gate. The minimizing exponent in Figure 4 is chosen by the first minimum in $1,\ldots,10$. Figure 12's final unitary uses $U[u,v,5]$, and Figure 13's $x_{\max}$ has the geometrically correct plus sign. The random choice is an explicit index, and the norm solver is represented by any output satisfying its specified equation.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, pp. 3–4, 11–13, eqs. (3)–(7), (21), Figures 4, 11–15

import Mathlib

noncomputable section

namespace FibAnyon.Approx

def w10 : ℂ := Complex.exp (Real.pi * Complex.I / 5)
def tau : ℝ := (Real.sqrt 5 - 1) / 2
def gold : ℝ := (Real.sqrt 5 + 1) / 2

@[ext] structure ZOmega where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

instance : Zero ZOmega := ⟨⟨0, 0, 0, 0⟩⟩
instance : One ZOmega := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add ZOmega := ⟨fun x y => ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩⟩
instance : Neg ZOmega := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub ZOmega := ⟨fun x y => x + -y⟩

/-- Product reduced using ω⁴ = −1 + ω − ω² + ω³ and ω⁵ = −1. -/
instance : Mul ZOmega := ⟨fun x y =>
  let r0 := x.a*y.a
  let r1 := x.a*y.b+x.b*y.a
  let r2 := x.a*y.c+x.b*y.b+x.c*y.a
  let r3 := x.a*y.d+x.b*y.c+x.c*y.b+x.d*y.a
  let r4 := x.b*y.d+x.c*y.c+x.d*y.b
  let r5 := x.c*y.d+x.d*y.c
  let r6 := x.d*y.d
  ⟨r0-r4-r5, r1+r4-r6, r2-r4, r3+r4⟩⟩

def ZOmega.pow (x : ZOmega) : ℕ → ZOmega
  | 0 => 1
  | n+1 => x * x.pow n

def ZOmega.w : ZOmega := ⟨0, 1, 0, 0⟩
def ZOmega.tauZ : ZOmega := ⟨0, 0, 1, -1⟩
def ZOmega.goldZ : ZOmega := ⟨1, 0, 1, -1⟩
def ZOmega.wpow (k : ℤ) : ZOmega := ZOmega.w.pow (k % 10).toNat
def ZOmega.conj (x : ZOmega) : ZOmega := ⟨x.a+x.b, -x.b, x.b-x.d, -x.b-x.c⟩
def ZOmega.bullet (x : ZOmega) : ZOmega := ⟨x.a+x.d, -x.c-x.d, x.d, x.b-x.d⟩
def ZOmega.toC (x : ZOmega) : ℂ :=
  (x.a : ℂ) + (x.b : ℂ)*w10 + (x.c : ℂ)*w10^2 + (x.d : ℂ)*w10^3

def gaussG (x : ZOmega) : ℝ := ‖x.toC‖^2 + ‖x.bullet.toC‖^2
def IsExact (u v : ZOmega) : Prop := ‖u.toC‖^2 + tau * ‖v.toC‖^2 = 1
def exactU (u v : ZOmega) (k : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u.toC, star v.toC * (Real.sqrt tau : ℂ) * w10^k;
     v.toC * (Real.sqrt tau : ℂ), -(star u.toC) * w10^k]

inductive Gate | F | T | W
deriving DecidableEq

def Gate.mat : Gate → Matrix (Fin 2) (Fin 2) ℂ
  | .F => !![(tau : ℂ), (Real.sqrt tau : ℂ); (Real.sqrt tau : ℂ), -(tau : ℂ)]
  | .T => !![1, 0; 0, w10]
  | .W => w10 • (1 : Matrix (Fin 2) (Fin 2) ℂ)

def circuitMat (C : List Gate) : Matrix (Fin 2) (Fin 2) ℂ := (C.map Gate.mat).prod
def circuitLength (C : List Gate) : ℕ := (C.filter (· != Gate.W)).length
def Rz (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(φ * Complex.I) / 2), 0;
     0, Complex.exp (φ * Complex.I / 2)]
def dist (U V : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (1 - ‖Matrix.trace (U * V.conjTranspose)‖ / 2)

def synthNextU (u v : ZOmega) (j : ℕ) : ZOmega :=
  ZOmega.tauZ * (u + ZOmega.wpow j * v)
def synthBestJ (u v : ZOmega) : ℕ :=
  ((List.range 10).map (· + 1)).foldl
    (fun best j => if gaussG (synthNextU u v j) < gaussG (synthNextU u v best)
      then j else best) 1
def terminalCircuit (u : ZOmega) (k : ℤ) : List Gate :=
  match (List.range 10).find? (fun a => u = ZOmega.w.pow a) with
  | some a => List.replicate a Gate.W ++ List.replicate ((k - 2*(a:ℤ) + 5) % 10).toNat Gate.T
  | none => []

/-- Figure 4, with fuel supplied by the initial integer Gauss complexity. -/
def synthLoop : ℕ → ZOmega → ZOmega → ℤ → List Gate → List Gate
  | 0, u, _, k, C => C ++ terminalCircuit u k
  | fuel+1, u, v, k, C =>
      if 2 < gaussG u then
        let j := synthBestJ u v
        let wv := ZOmega.wpow j * v
        synthLoop fuel (ZOmega.tauZ * (u + wv))
          (u - ZOmega.tauZ * wv) (k + j + 5)
          (C ++ List.replicate (10-j) Gate.T ++ [Gate.F])
      else C ++ terminalCircuit u k
def exactSynthesize (u v : ZOmega) (k : ℤ) : List Gate :=
  synthLoop ⌈gaussG u⌉₊ u v k []

/-- Figure 15; the guarantees use n ≥ 2. -/
def approxReal (x : ℝ) (n : ℕ) : ℤ × ℤ := Id.run do
  let p : ℤ := Nat.fib n
  let q : ℤ := Nat.fib (n+1)
  let uF : ℤ := (-1 : ℤ)^(n+1) * Nat.fib n
  let vF : ℤ := (-1 : ℤ)^n * Nat.fib (n-1)
  let c : ℤ := round (x * q)
  let z : ℤ := round ((c * uF : ℤ) / (q : ℝ))
  return (c*vF+p*z, c*uF-q*z)

def sampleM (ε r : ℝ) : ℕ :=
  (⌈Real.logb tau (Real.sqrt (gold / (4*r)) * ε * r)⌉ + 1 : ℤ).toNat
def sampleN (ε r : ℝ) : ℕ := ⌈gold^(sampleM ε r)⌉₊

/-- Figure 13, with the geometric correction to the sign of x_max. -/
def randomSample (θ ε r : ℝ) (j : ℕ) : ZOmega := Id.run do
  let m := sampleM ε r
  let scale := r * gold^m
  let ymin := scale * (Real.sin θ - ε * (Real.sqrt (4-ε^2) * Real.cos θ + ε * Real.sin θ)/2)
  let ymax := scale * (Real.sin θ + ε * (Real.sqrt (4-ε^2) * Real.cos θ - ε * Real.sin θ)/2)
  let xmax := scale * ((1-ε^2/2)*Real.cos θ + ε * Real.sqrt (1-ε^2/4)*Real.sin θ)
  let xc := xmax - r*ε^2*gold^m/(4*Real.cos θ)
  let y := ymin + j*(ymax-ymin)/(sampleN ε r : ℝ)
  let yz := approxReal (y / Real.sqrt (2-tau)) m
  let ay := yz.1
  let byCoeff := yz.2
  let x := xc - (((ay:ℝ)+byCoeff*tau)*Real.sqrt (2-tau)-ymin)*Real.tan θ
  let xz := approxReal x m
  let ax := xz.1
  let bx := xz.2
  let ux : ZOmega := ⟨ax, 0, bx, -bx⟩
  let uy : ZOmega := ⟨ay, 0, byCoeff, -byCoeff⟩
  return ux + (⟨-1, 2, -1, 1⟩ : ZOmega) * uy

/-- The dark gray parallelogram P of Figure 14, p. 12: the points with imaginary part in
[y_min, y_max] lying between the chord through (x_min, y_max), (x_max, y_min) (at depth
rε²ϕ^m/2 below the circle of radius rϕ^m in the direction θ) and the parallel line at depth
rε²ϕ^m. -/
def parallelogramP (θ ε r : ℝ) : Set ℂ :=
  let scale := r * gold^(sampleM ε r)
  let ymin := scale * (Real.sin θ - ε * (Real.sqrt (4-ε^2) * Real.cos θ + ε * Real.sin θ)/2)
  let ymax := scale * (Real.sin θ + ε * (Real.sqrt (4-ε^2) * Real.cos θ - ε * Real.sin θ)/2)
  {z | ymin ≤ z.im ∧ z.im ≤ ymax ∧
    scale * (1 - ε^2) ≤ (z * Complex.exp (-(θ * Complex.I))).re ∧
    (z * Complex.exp (-(θ * Complex.I))).re ≤ scale * (1 - ε^2/2)}

def rzTheta (φ : ℝ) (k : ℤ) : ℝ := -φ/2 - Real.pi*k/5
def rzSample (φ ε : ℝ) (k : ℤ) (j : ℕ) : ZOmega :=
  randomSample (rzTheta φ k) ε 1 j
def rzXi (φ ε : ℝ) (k : ℤ) (j : ℕ) : ZOmega :=
  let m := sampleM ε 1
  let u0 := rzSample φ ε k j
  ZOmega.goldZ * (ZOmega.goldZ.pow (2*m) - u0 * u0.conj)
/-- Figure 12, with U[u,v,5] in the last line. -/
def rzOutput (φ ε : ℝ) (k : ℤ) (j : ℕ) (x : ZOmega) : List Gate :=
  let m := sampleM ε 1
  let u := ZOmega.wpow k * ZOmega.tauZ.pow m * rzSample φ ε k j
  let v := ZOmega.tauZ.pow m * x
  exactSynthesize u v 5

end FibAnyon.Approx


