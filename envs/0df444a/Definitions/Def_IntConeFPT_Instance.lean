-- Prove2me | Definitions.Def_IntConeFPT_Instance
-- name    : IntConeFPT_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:30.443231+00:00
-- url     : https://prove2.me/theorems/46bc6212-3964-4fcc-af59-181af8835d43
-- title:
--   An instance of (♣): rational generator polytopes $P^{(t)}$, dense convex polynomial costs $f^{(t)}$, polyhedra $Q$ and $\mathcal A$; validity and the encoding $|I|$
-- statement:
--   An **instance** of the problem (♣) consists of integers $d,k,\tau\ge 0$ and, written as rational data:
--
--   1. for each type $t\in[\tau]$ a system $A^{(t)}x+B^{(t)}u\le b^{(t)}$ in $(x,u)\in\mathbb R^d\times\mathbb R^k$, whose solution set is the **generator polytope** $P^{(t)}\subseteq\mathbb R^{d+k}$;
--   2. for each type a degree bound $D_t$ and the rational coefficients of all monomials of total degree at most $D_t$ in $d$ variables (**dense encoding by total degree**), defining the cost polynomial $f^{(t)}$;
--   3. a system $B(y,v)\le c$ defining the polyhedron $Q\subseteq\mathbb R^{d+k}$;
--   4. a system on the tuples $((y^{(t)},v^{(t)},N^{(t)}))_{t=1}^{\tau}$ defining the polyhedron $\mathcal A\subseteq\mathbb R^{\tau(d+k+1)}$.
--
--   The projection $P^{(t)}_x=\{x\in\mathbb R^d:\exists u\in\mathbb R^k,\ (x,u)\in P^{(t)}\}$ is the domain of the integer block. The polyhedra $\hat Q$ and $\hat{\mathcal A}$ are given by the same systems with right-hand side replaced by $0$ (proof of Theorem 1, p.18).
--
--   An instance is **valid** when $d\ge1$, $\tau\ge1$, every $P^{(t)}$ is bounded (a rational polytope, possibly empty), and every $f^{(t)}$ is convex on $P^{(t)}_x$. The continuous dimension $k=0$ is allowed, and $Q$, $\mathcal A$ may be empty or unbounded.
--
--   The **encoding** of an instance writes $d,k,\tau$ in binary, then for each type the row count, the local system, the degree bound and the coefficients in a fixed monomial order, then the systems of $Q$ and $\mathcal A$; every number is binary and rationals are in lowest terms. Its length is the paper's $|I|$ up to a constant factor.
--
--   **Formalization Note** Types are indexed by `Fin τ`. The cost coefficients are indexed by the positions of the list `monomials d D`, which enumerates every exponent vector of total degree at most $D$ exactly once. Assumption 3 of the paper (p.6) is not a separate condition: explicitly given convex polynomials with rational coefficients satisfy it (p.7).
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §1, pp.2–4 ((♣), |I|), B.1 p.33 (local systems), p.18 (Q̂, Â)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat

namespace IntConeFPT

open OnlineCRS.Combine
open RobustToDynamics (encMat)

/-- **Exponent vectors of total degree at most `D` in `d` variables, in a fixed order.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §1, p.3: "each f^(t) is an explicitly given
polynomial in these d variables with rational coefficients, in dense encoding by total degree".

`monomials d D` lists every `e : Fin d → ℕ` with `e 0 + ⋯ + e (d−1) ≤ D` exactly once: the first
exponent runs over `0, …, D` and the remaining ones recursively over total degree `D − e 0`.

**Formalization Note.** This fixes the order in which the dense encoding lists the coefficients. -/
def monomials : (d D : ℕ) → List (Fin d → ℕ)
  | 0, _ => [fun i => Fin.elim0 i]
  | d + 1, D => (List.range (D + 1)).flatMap fun e =>
      (monomials d (D - e)).map fun r => (Fin.cons e r : Fin (d + 1) → ℕ)

/-- **An instance of the problem (♣).**
Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), §1, pp.2–4: "Let d ≥ 1 and k ≥ 0 be
integers, and let P^(1), …, P^(τ) ⊆ R^{d+k} be rational polytopes. … Given rational polyhedra
Q ⊆ R^{d+k} and A ⊆ R^{τ(d+k+1)} …"; B.1, p.33: "P = P^(t) = {(x, u) : Ax + Bu ≤ c}".

The data are
1. the dimensions `d` (integer coordinates), `k` (continuous coordinates) and `τ` (types);
2. for each type `t`, a rational system `Aloc t · x + Bloc t · u ≤ bloc t` with `m t` rows
   (the polytope `P^(t)`);
3. for each type `t`, a degree bound `deg t` and the rational coefficients `coeff t` of the cost
   polynomial `f^(t)` on all monomials of total degree `≤ deg t`, listed by `monomials`;
4. a rational system `QY · y + QV · v ≤ cQ` with `mQ` rows (the polyhedron `Q ⊆ R^{d+k}`);
5. a rational system `Σ_t (AY t · y^(t) + AV t · v^(t) + AN_{·,t} N^(t)) ≤ cA` with `mA` rows
   (the polyhedron `A ⊆ R^{τ(d+k+1)}` on the typewise aggregates and counts).

**Formalization Note.** Types are indexed by `Fin τ` (the paper's `t = 1, …, τ` is `t = 0, …, τ−1`).
The cost coefficients are indexed by the positions of `monomials d (deg t)` (dense encoding by
total degree). -/
structure Instance where
  d : ℕ
  k : ℕ
  τ : ℕ
  m : Fin τ → ℕ
  Aloc : (t : Fin τ) → Matrix (Fin (m t)) (Fin d) ℚ
  Bloc : (t : Fin τ) → Matrix (Fin (m t)) (Fin k) ℚ
  bloc : (t : Fin τ) → Fin (m t) → ℚ
  deg : Fin τ → ℕ
  coeff : (t : Fin τ) → Fin (monomials d (deg t)).length → ℚ
  mQ : ℕ
  QY : Matrix (Fin mQ) (Fin d) ℚ
  QV : Matrix (Fin mQ) (Fin k) ℚ
  cQ : Fin mQ → ℚ
  mA : ℕ
  AY : Fin τ → Matrix (Fin mA) (Fin d) ℚ
  AV : Fin τ → Matrix (Fin mA) (Fin k) ℚ
  AN : Matrix (Fin mA) (Fin τ) ℚ
  cA : Fin mA → ℚ

namespace Instance

/-- **The generator polytope `P^(t) ⊆ R^{d+k}`** (§1, p.2; B.1, p.33): the real solutions
`(x, u)` of `Aloc t · x + Bloc t · u ≤ bloc t`. -/
def P (I : Instance) (t : Fin I.τ) : Set ((Fin I.d → ℝ) × (Fin I.k → ℝ)) :=
  {p | ∀ i, (∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j) ≤ (I.bloc t i : ℝ)}

/-- **The domain `P_x^(t)` of the integer-coordinate block** (§1, p.2): `{x ∈ R^d : ∃ u ∈ R^k,
(x, u) ∈ P^(t)}`. -/
def Px (I : Instance) (t : Fin I.τ) : Set (Fin I.d → ℝ) :=
  Prod.fst '' I.P t

/-- **The cost polynomial `f^(t)`** (§1, p.3): `f^(t)(x) = Σ_e coeff_e · ∏_i x_i^{e_i}`, the sum over
all exponent vectors `e` of total degree `≤ deg t`. -/
def f (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℝ) : ℝ :=
  ∑ j : Fin (monomials I.d (I.deg t)).length,
    (I.coeff t j : ℝ) * ∏ i, x i ^ ((monomials I.d (I.deg t)).get j i)

/-- **The aggregate polyhedron `Q ⊆ R^{d+k}`** (§1, p.3; (3.2a), p.12: "B(y, v) ≤ c"). -/
def Q (I : Instance) : Set ((Fin I.d → ℝ) × (Fin I.k → ℝ)) :=
  {p | ∀ i, (∑ j, (I.QY i j : ℝ) * p.1 j) + (∑ j, (I.QV i j : ℝ) * p.2 j) ≤ (I.cQ i : ℝ)}

/-- **The typewise polyhedron `A ⊆ R^{τ(d+k+1)}`** (§1, p.3) on the tuples
`((y^(t), v^(t), N^(t)))_{t=1}^τ`. -/
def A (I : Instance) : Set (Fin I.τ → (Fin I.d → ℝ) × (Fin I.k → ℝ) × ℝ) :=
  {Y | ∀ i, (∑ t, ((∑ j, (I.AY t i j : ℝ) * (Y t).1 j) + (∑ j, (I.AV t i j : ℝ) * (Y t).2.1 j)
      + (I.AN i t : ℝ) * (Y t).2.2)) ≤ (I.cA i : ℝ)}

/-- **`Q̂`: the description of `Q` with right-hand side replaced by zero** (proof of Theorem 1,
p.18: "replace the right-hand sides in the descriptions of Q and A by zero, obtaining polyhedra
Q̂ and Â"). -/
def Qhat (I : Instance) : Set ((Fin I.d → ℝ) × (Fin I.k → ℝ)) :=
  {p | ∀ i, (∑ j, (I.QY i j : ℝ) * p.1 j) + (∑ j, (I.QV i j : ℝ) * p.2 j) ≤ 0}

/-- **`Â`: the description of `A` with right-hand side replaced by zero** (p.18). -/
def Ahat (I : Instance) : Set (Fin I.τ → (Fin I.d → ℝ) × (Fin I.k → ℝ) × ℝ) :=
  {Y | ∀ i, (∑ t, ((∑ j, (I.AY t i j : ℝ) * (Y t).1 j) + (∑ j, (I.AV t i j : ℝ) * (Y t).2.1 j)
      + (I.AN i t : ℝ) * (Y t).2.2)) ≤ 0}

/-- **Valid instances** (§1, pp.2–3; standing assumptions). `d ≥ 1` ("Let d ≥ 1"), `τ ≥ 1`
(types `t ∈ [τ]`), every `P^(t)` bounded (a "rational polytope", possibly empty), and every
`f^(t)` convex on `P_x^(t)` ("convexity is required on P_x^(t)"). `k = 0` is allowed, and `Q`, `A`
are arbitrary rational polyhedra (possibly empty or unbounded).

**Formalization Note.** Assumption 3 (p.6) is not an extra condition: explicitly given convex
polynomials with rational coefficients satisfy it (p.7). -/
structure Valid (I : Instance) : Prop where
  one_le_d : 1 ≤ I.d
  one_le_τ : 1 ≤ I.τ
  bounded : ∀ t, Bornology.IsBounded (I.P t)
  convex : ∀ t, ConvexOn ℝ (I.Px t) (I.f t)

end Instance

/-- `p` lies in the box `[−M, M]^{d+k}` ((2.1), p.6). -/
def InBox {d k : ℕ} (M : ℕ) (p : (Fin d → ℝ) × (Fin k → ℝ)) : Prop :=
  (∀ i, |p.1 i| ≤ (M : ℝ)) ∧ ∀ j, |p.2 j| ≤ (M : ℝ)

/-- **The binary encoding of an instance; `|I|` is its length.**
Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), §1, p.4: "For optimization, |I|
includes the descriptions of all P(t), f(t), Q, and A"; p.3: "dense encoding by total degree".

`encInstance I` writes `d, k, τ` in binary, then for each type `t` the row count, the rows of the
local system and its right-hand side, the degree bound and the coefficients of all monomials of
total degree `≤ deg t` (in the order of `monomials`), then the system of `Q` and the system of `A`.
Every number is binary (`encNat`, `encRat` in lowest terms), every size is written out, and items
are separated by `3`.

**Formalization Note.** This is the paper's |I| up to a constant factor. -/
def encInstance (I : Instance) : List Sym :=
  encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encNat I.τ ++ [3] ++
  (List.finRange I.τ).flatMap (fun t =>
    encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
    encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]) ++
  encNat I.mQ ++ [3] ++ encMat I.QY ++ encMat I.QV ++ encVec I.cQ ++ [3] ++
  encNat I.mA ++ [3] ++
  (List.finRange I.τ).flatMap (fun t => encMat (I.AY t) ++ encMat (I.AV t)) ++
  encMat I.AN ++ encVec I.cA ++ [3]

end IntConeFPT


