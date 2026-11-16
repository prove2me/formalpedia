-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_RobustPromiseValue
-- name    : PolyEulerFlow_Supplement_RobustPromiseValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:05:36.744202+00:00
-- url     : https://prove2.me/theorems/9430dbaa-daf2-4748-90f8-fab1a10bbb59
-- title:
--   The fixed-field robust prediction promise of Theorem 10 and its stronger form on the hard instances
-- statement:
--   Fix a rational polynomial field $F(h,Z)$ on $\mathbb R^n$, a rational polynomial initialization $c(x,h)$, an integer $r$, a rational box $[lo,hi]$ and an output coordinate $o$. An instance is a triple $(x,s,N)$ of natural numbers, encoded as $x$ in binary, $s$ in **unary** and $N$ in binary, each self-delimiting.
--
--   1. The instance satisfies the **promise with value** $b\in\{0,1\}$ if $s\ge\ell(x)+4$, $N\ge1$, and every unit-step execution
--   $$z_0=c(x,2^{-s}),\qquad z_{k+1}=z_k+F(2^{-s},z_k)+\xi_k,\qquad \|\xi_k\|_\infty\le 2^{-rs},$$
--   stays in $[lo,hi]$ and satisfies $|z_k(o)-b|\le1/4$ at every index $k\ge N$.
--   2. It satisfies the **strong promise with value** $b$ if moreover, with the same bound $2^{-rs}$: every execution on an admissible variable mesh ($0<\eta_k\le1$, $\sum_k\eta_k=\infty$, updates $\eta_kF+\eta_k\xi_k$) has $|z_k(o)-b|\le1/4$ at every index of physical time $\sum_{i<k}\eta_i\ge N$; and for every measurable forcing with $\|\xi(t)\|_\infty\le2^{-rs}$ a.e., a solution of $\dot z=F(2^{-s},z)+\xi(t)$, $z(0)=c(x,2^{-s})$ on $[0,\infty)$ exists and every such solution has $|z(t)(o)-b|\le1/4$ for all $t\ge N$.
--
--   Item 1 is the promise problem of Theorem 10 ("decide that value"); item 2 is the stronger property of its hard instances.
--
--   **Formalization Note** Executions, meshes, disturbances and forced solutions are the published `eulerOrbit`, `IsAdmissibleMesh`, `IsPermittedDisturbance`, `IsForcedSolution` and `IsPermittedForcing`; $F$ and $c$ are evaluated by the published `fieldEval` and `initEval`.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 10, p.8 (PDF 10)

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_encodeNatVec
import Definitions.Def_PolyEulerFlow_fieldEval
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- The encoding of an instance `(x, s, N)` of the robust prediction problem of Theorem 10 (p.8, PDF 10): `x` in binary, `s` in unary,
`N` in binary, each self-delimiting. Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…). -/
def encodePredInstance (I : ℕ × ℕ × ℕ) : List Bool :=
  tagBits (binWord I.1) ++ unaryWord I.2.1 ++ tagBits (binWord I.2.2)

/-- The promise of Theorem 10 with value `b` at the instance `(x, s, N)`: `s ≥ ℓ(x) + 4`, `N ≥ 1`, and every unit-step execution from
`c(x, 2^{-s})` with active disturbances `‖ξ_k‖∞ ≤ 2^{-rs}` stays in the box `[lo, hi]` and has output within `1/4` of `b` at every index
`k ≥ N`. Instances with no such `b` are outside the promise. -/
def RobustPromiseValue {n : ℕ} (F : Fin n → MvPolynomial (Option (Fin n)) ℚ) (c : Fin n → MvPolynomial (Fin 2) ℚ) (r : ℕ)
    (lo hi : Fin n → ℚ) (o : Fin n) (I : ℕ × ℕ × ℕ) (b : Bool) : Prop :=
  inputLength I.1 + 4 ≤ I.2.1 ∧ 1 ≤ I.2.2 ∧
    ∀ ξ : ℕ → Fin n → ℝ, IsPermittedDisturbance (scale I.2.1 ^ r) ξ →
      (∀ k, eulerOrbit (fieldEval F (scale I.2.1)) (initEval c I.1 (scale I.2.1)) (fun _ => 1) ξ k ∈
          Set.Icc (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ))) ∧
        ∀ k : ℕ, I.2.2 ≤ k →
          |eulerOrbit (fieldEval F (scale I.2.1)) (initEval c I.1 (scale I.2.1)) (fun _ => 1) ξ k o - (if b then 1 else 0)| ≤ 1 / 4

/-- The stronger promise met by the hard instances of Theorem 10: the promise with value `b`, and moreover, with the same disturbance bound
`2^{-rs}`, the output is within `1/4` of `b` at every grid index of physical time at least `N` of every admissible variable mesh, and for
every measurable forcing a forced solution exists and every forced solution has output within `1/4` of `b` at every time `t ≥ N`. -/
def StrongPromiseValue {n : ℕ} (F : Fin n → MvPolynomial (Option (Fin n)) ℚ) (c : Fin n → MvPolynomial (Fin 2) ℚ) (r : ℕ)
    (lo hi : Fin n → ℚ) (o : Fin n) (I : ℕ × ℕ × ℕ) (b : Bool) : Prop :=
  RobustPromiseValue F c r lo hi o I b ∧
    (∀ (η : ℕ → ℝ) (ξ : ℕ → Fin n → ℝ), IsAdmissibleMesh η → IsPermittedDisturbance (scale I.2.1 ^ r) ξ →
      ∀ k : ℕ, (I.2.2 : ℝ) ≤ physTime η k →
        |eulerOrbit (fieldEval F (scale I.2.1)) (initEval c I.1 (scale I.2.1)) η ξ k o - (if b then 1 else 0)| ≤ 1 / 4) ∧
    ∀ ξ : ℝ → Fin n → ℝ, IsPermittedForcing (scale I.2.1 ^ r) ξ →
      (∃ z : ℝ → Fin n → ℝ, IsForcedSolution (fieldEval F (scale I.2.1)) (initEval c I.1 (scale I.2.1)) ξ z) ∧
        ∀ z : ℝ → Fin n → ℝ, IsForcedSolution (fieldEval F (scale I.2.1)) (initEval c I.1 (scale I.2.1)) ξ z →
          ∀ t : ℝ, (I.2.2 : ℝ) ≤ t → |z t o - (if b then 1 else 0)| ≤ 1 / 4

end PolyEulerFlow.Supplement


