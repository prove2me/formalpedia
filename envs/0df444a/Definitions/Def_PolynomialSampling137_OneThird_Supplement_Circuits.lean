-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits
-- name    : PolynomialSampling137_OneThird_Supplement_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:46:17.616203+00:00
-- url     : https://prove2.me/theorems/be298387-af21-4eca-8a78-f5ddb1d74445
-- title:
--   Finite Boolean DAGs, nonlinear ancestors and signed dyadic sums
-- statement:
--   A finite circuit has constants, seed inputs, NOT, XOR, AND and OR gates. Gates are listed in topological order, with arbitrary finite lists of earlier parents. Evaluation uses the original seed. For a chosen output, the nonlinear count is the number of distinct AND/OR nodes reachable backwards from it, including the output itself when nonlinear. Shared nodes count once. The class $\mathcal C_q$ consists of the functions admitting such a circuit with count at most $q$.
--
--   $$F(x)=A(x)+\sum_{i=1}^M v_i1_{B_i}(x),\qquad V(M,u)=\sum_{j=0}^{\min(u,M)}\binom Mj.$$
--
--   Here $A$ is an actual affine map and each $B_i$ is an affine flat. Labels specify all outputs reading one shared term. This representation also admits redundant terms, which can be removed or absorbed into $A$. Signed dyadic sums have at most $m$ terms $\sigma_i2^{j_i}$, signs $\sigma_i\in\{-1,1\}$ and arbitrary integer exponents; repetitions and the empty sum are allowed. The normalized version uses terms in $\{0\}\cup\{2^{-r}:r\ge0\}$. Neither circuit membership nor acceptance is defined by a gap estimate.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §§6.1–6.2, Appendix A.1 and B.1, printed pp. 25–26, 32, 36–38; PDF pp. 27–28, 34, 38–40

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

/-- An ordinary finite Boolean DAG, presented in a topological order.
Fan-in is any finite list; XOR, AND and OR are distinct primitives. -/
inductive Gate where
  | input (i : ℕ)
  | constant (b : ZMod 2)
  | neg (j : ℕ)
  | xor (js : List ℕ)
  | and (js : List ℕ)
  | or (js : List ℕ)

def Gate.parents : Gate → List ℕ
  | .input _ | .constant _ => []
  | .neg j => [j]
  | .xor js | .and js | .or js => js

def Gate.nonlinear : Gate → Bool
  | .and _ | .or _ => true
  | _ => false

def Gate.eval {s : ℕ} (g : Gate) (x : Word s) (v : List (ZMod 2)) : ZMod 2 :=
  match g with
  | .input i => if h : i < s then x ⟨i,h⟩ else 0
  | .constant b => b
  | .neg j => 1 + v.getD j 0
  | .xor js => (js.map (fun j => v.getD j 0)).sum
  | .and js => (js.map (fun j => v.getD j 0)).prod
  | .or js => 1 + (js.map (fun j => 1 + v.getD j 0)).prod

structure Circuit (s : ℕ) where
  gates : List Gate
  out : Fin gates.length
  earlier : ∀ (i : ℕ) (h : i < gates.length), ∀ j ∈ (gates[i]).parents, j < i
  inputs : ∀ g ∈ gates, ∀ i, g = .input i → i < s

def Circuit.eval {s : ℕ} (C : Circuit s) (x : Word s) : ZMod 2 :=
  (C.gates.foldl (fun v g => v ++ [g.eval x v]) []).getD C.out.val 0

/-- Reflexive ancestry includes the output gate itself, and counts a shared node once. -/
def Circuit.ancestor {s : ℕ} (C : Circuit s) (i : ℕ) : Prop :=
  Relation.ReflTransGen
    (fun a b : ℕ => ∃ h : a < C.gates.length, b ∈ (C.gates[a]).parents)
    C.out.val i

def Circuit.nonlinearCount {s : ℕ} (C : Circuit s) : ℕ := by
  classical
  exact ((Finset.range C.gates.length).filter (fun i =>
    C.ancestor i ∧ (C.gates.getD i (.constant 0)).nonlinear = true)).card

def InCircuitClass {s : ℕ} (q : ℕ) (f : Word s → ZMod 2) : Prop :=
  ∃ C : Circuit s, C.nonlinearCount ≤ q ∧ C.eval = f

/-- Signed powers allow repetitions, arbitrary integer exponents and the empty sum. -/
def SignedDyadic (m : ℕ) (z : ℝ) : Prop :=
  ∃ (l : ℕ) (σ : Fin l → ℤ) (j : Fin l → ℤ), l ≤ m ∧
    (∀ i, σ i = 1 ∨ σ i = -1) ∧ z = ∑ i, (σ i : ℝ) * (2 : ℝ) ^ j i

def NormalizedSignedDyadic (m : ℕ) (z : ℝ) : Prop :=
  ∃ (l : ℕ) (σ : Fin l → ℤ) (a : Fin l → ℝ), l ≤ m ∧
    (∀ i, σ i = 1 ∨ σ i = -1) ∧
    (∀ i, a i = 0 ∨ ∃ r : ℕ, a i = (2 : ℝ) ^ (-(r : ℤ))) ∧
    z = ∑ i, (σ i : ℝ) * a i

/-- Equation (36), one shared label for each flat term; no independence assumption.
Allowing redundant, empty and affine terms preserves all normalized source instances. -/
def FlatMap {s n : ℕ} (M : ℕ) (A : Word s →ᵃ[ZMod 2] Word n)
    (v : Fin M → Word n) (B : Fin M → AffineSubspace (ZMod 2) (Word s))
    (x : Word s) : Word n := by
  classical
  exact A x + ∑ i, if x ∈ B i then v i else 0

def HammingVolume (M u : ℕ) : ℕ := MonomialCount M u

end PolynomialSampling137.OneThird.Supplement


