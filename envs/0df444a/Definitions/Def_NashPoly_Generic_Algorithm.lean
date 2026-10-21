-- Prove2me | Definitions.Def_NashPoly_Generic_Algorithm
-- name    : NashPoly_Generic_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:50.803956+00:00
-- url     : https://prove2.me/theorems/512626e9-ce2e-405c-a599-0d922eb3768f
-- title:
--   Algorithm 3.1, (3.8), pp. 9–10 — runs of the KKT-cut algorithm
-- statement:
--   This file encodes the runs of Algorithm 3.1 of Nie and Tang, which searches for a Nash equilibrium of a NEPP by minimizing $\theta(x)=[x]_1^T\Theta[x]_1$ over the KKT set $G$ and cutting off non-equilibria.
--
--   **Problem (3.8).** At a candidate $u$, player $i$ solves $\omega_i=\min_{x_i\in X_i} f_i(x_i,u_{-i})-f_i(u_i,u_{-i})$. Player $i$ *can improve* at $u$ (that is, $\omega_i<0$) if some $v\in X_i$ has $f_i(v,u_{-i})<f_i(u)$. An *optimizer of (3.8)* is a point $v\in X_i$ minimizing $f_i(\cdot,u_{-i})$ on $X_i$.
--
--   **The algorithm** (pp. 9–10). Step 0 sets $K_i=\emptyset$ and $\ell=0$ and fixes a positive definite $\Theta$. Step 1 solves (3.10) (minimize $\theta$ over $\mathrm{Feas}(K)$); if it is infeasible it reports that there is no NE, otherwise it takes an optimizer $u$. Step 2 solves (3.8) for every $i$; if all $\omega_i\ge0$ it outputs the NE $u$. Step 3, for each $i$ with $\omega_i<0$, takes a set $U_i$ of some optimizers of (3.8), updates $K_i:=K_i\cup U_i$, sets $\ell:=\ell+1$ and returns to Step 1.
--
--   **Runs.** A *run that has completed $L$ loops* consists of cut sets $K^{(0)},\dots,K^{(L)}$ and candidates $u^{(0)},\dots,u^{(L-1)}$ with:
--   1. $K^{(0)}_i=\emptyset$ for all $i$;
--   2. for each $\ell<L$: $u^{(\ell)}$ is a minimizer of $\theta$ on $\mathrm{Feas}(K^{(\ell)})$;
--   3. $u^{(\ell)}$ is not a Nash equilibrium;
--   4. $K^{(\ell+1)}_i=K^{(\ell)}_i\cup U_i$, where $U_i$ is a nonempty set of optimizers of (3.8) at $u^{(\ell)}$ if player $i$ can improve at $u^{(\ell)}$, and $U_i=\emptyset$ otherwise.
--
--   The algorithm makes choices (which optimizer $u$, which sets $U_i$), so statements about it quantify over all runs. `Step38Solvable` says every player test (3.8) attains its minimum at each point of $G$; `IsTerminal` says the final call to Step 1 is infeasible or has a minimizing NE; and `RunExtends` preserves every earlier cut set and candidate.
--
--   **Formalization Note** $L$ counts completed executions of Step 3 (the loop counter $\ell$ of the paper). The optimal value $\omega_i$ is never formed as a real infimum (which would be $0$ on an unbounded-below set); "$\omega_i<0$" is the existence of a strictly improving feasible point. Step 2 does not stop exactly when $u^{(\ell)}$ is not a Nash equilibrium, which is recorded directly.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 9, (3.8), (3.10); pp. 9–10, Algorithm 3.1

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

namespace NashPoly.Generic

open MvPolynomial Matrix

variable {N : ℕ} {n m : Fin N → ℕ}

namespace NEP

variable (P : NEP N n m)

/-- Player `i` can improve at `u`: some `v ∈ X_i` has `f_i(v, u_{-i}) < f_i(u)`. This is
"`ω_i < 0`" for the optimal value `ω_i` of (3.8), p. 9, without taking an infimum. -/
def CanImprove (i : Fin N) (u : Var n → ℝ) : Prop :=
  ∃ v ∈ P.X i, eval (repl u i v) (P.f i) < eval u (P.f i)

/-- `v` is an optimizer of (3.8), p. 9: `v ∈ X_i` minimizes `f_i(·, u_{-i}) − f_i(u)` on `X_i`. -/
def IsOpt38 (i : Fin N) (u : Var n → ℝ) (v : Fin (n i) → ℝ) : Prop :=
  v ∈ P.X i ∧ IsMinOn (fun w => eval (repl u i w) (P.f i)) (P.X i) v

/-- The player tests in (3.8) attain their minima at every candidate of (3.7). This is
the extra condition needed for Steps 2 and 3 to be executable; the paper notes on p. 10
that (3.8) need not attain a minimum on an unbounded strategy set. -/
def Step38Solvable
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i))
      (MvPolynomial (Fin (n i)) ℝ)) : Prop :=
  ∀ u ∈ P.GSet H, ∀ i, ∃ v, P.IsOpt38 i u v

/-- A run of Algorithm 3.1 (pp. 9–10) that has completed `L` loops (`L` executions of Step 3),
with multiplier expressions from `H` and the matrix `Θ` of Step 0.
* `K ℓ i` is the cut set `K_i` at the start of loop `ℓ`; `K 0 i = ∅` (Step 0).
* `u ℓ` is the optimizer of (3.10) found by Step 1 in loop `ℓ`: a minimizer of
  `[x]_1^T Θ [x]_1` on the feasible set of (3.10) for the cut sets `K ℓ`.
* `u ℓ` is not a Nash equilibrium (Step 2 did not stop).
* Step 3: `K_i := K_i ∪ U_i`, where `U_i` is a nonempty set of optimizers of (3.8) at `u ℓ`
  if `ω_i < 0`, and `U_i = ∅` otherwise. -/
def IsRun
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (L : ℕ)
    (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ)) (u : Fin L → Var n → ℝ) : Prop :=
  (∀ i, K 0 i = ∅) ∧
  ∀ ℓ : Fin L,
    u ℓ ∈ P.Feas H (K ℓ.castSucc) ∧ IsMinOn (theta Θ) (P.Feas H (K ℓ.castSucc)) (u ℓ) ∧
    ¬ P.IsNE (u ℓ) ∧
    ∀ i, ∃ U : Set (Fin (n i) → ℝ), K ℓ.succ i = K ℓ.castSucc i ∪ U ∧
      (P.CanImprove i (u ℓ) → U.Nonempty ∧ ∀ v ∈ U, P.IsOpt38 i (u ℓ) v) ∧
      (¬ P.CanImprove i (u ℓ) → U = ∅)

/-- The final call to Step 1 is terminal: (3.10) is infeasible, or a minimizer
passes Step 2 and is a Nash equilibrium. -/
def IsTerminal
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i))
      (MvPolynomial (Fin (n i)) ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ)
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) : Prop :=
  P.Feas H K = ∅ ∨
    ∃ u ∈ P.Feas H K, IsMinOn (theta Θ) (P.Feas H K) u ∧ P.IsNE u

/-- The later run preserves every earlier cut set and candidate. -/
def RunExtends (_P : NEP N n m) {L L' : ℕ} (h : L ≤ L')
    (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
    (u : Fin L → Var n → ℝ)
    (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
    (u' : Fin L' → Var n → ℝ) : Prop :=
  (∀ t : Fin L, u' ⟨t.val, lt_of_lt_of_le t.isLt h⟩ = u t) ∧
  (∀ t : Fin (L + 1),
    K' ⟨t.val, lt_of_lt_of_le t.isLt (Nat.add_le_add_right h 1)⟩ = K t)

end NEP

end NashPoly.Generic


