-- Prove2me | Definitions.Def_FreeSpencer_trialLaw
-- name    : FreeSpencer_trialLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:17.386797+00:00
-- url     : https://prove2.me/theorems/cebaedd0-bf6d-4274-81f1-d494fc62b82b
-- title:
--   The law of a trial of Algorithm 2
-- statement:
--   A state of Algorithm 2 records the point $x$, the covariance $C$, the number of movements (so the clock is $T=\text{moves}\cdot h^2$), the movement sum $y$ (so $Y=\hat A(y)$), the scalars $a,u,v,r_c$, the set $F$ of newly frozen coordinates, and a stop flag. One pass of the loop tests $T+h^2\le\tau$, $|F|<\ell/8$, $d=a+u\le\ell/32$; prepares; stops if the loss now exceeds $\ell/32$; otherwise draws $(j,\pm)$ uniformly from the $2k$ possibilities, moves by $h\xi$ with $\xi=\pm\sqrt{k/2}\,u_j$, sets $C\leftarrow C-h^2Q$ with $Q=\frac12P_W$, and rounds each live coordinate within $a_0$ of a face to its nearest sign, a tie resolved as $+1$. The trial law is the law of the state after $\lfloor\tau/h^2\rfloor+1$ passes, with stopped states absorbing. It has finite support.
--
--   **Formalization Note** All $n$ coordinates are kept in the coefficient space (Remark 7.2), so the identity covariance on the live set $I_0$ is a diagonal projection. The empty basis stops a trial; Lemma 7.5 shows it does not occur.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 2, p.78; Section 7.2, p.50; Section 7.4, p.52; Remark 7.2, p.49

import Mathlib
import Definitions.Def_FreeSpencer_Procs
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- A state of Algorithm 2: the point `x`, the covariance `C`, the number of movements (the clock is
`T = moves · h²`), the movement sum `y` (so the stored matrix is `Y = Â(y)`), the ghost scalars `a`
(cuts), `u` (cleanup), `v` (movement withdrawal), `r_c` (rounding), the set `F` of newly frozen
coordinates, and a stop flag. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 2, p.78; Section 7.4, p.52. -/
structure TrialState (n : ℕ) where
  x : Fin n → ℝ
  C : Matrix (Fin n) (Fin n) ℝ
  moves : ℕ
  y : Fin n → ℝ
  a : ℝ
  u : ℝ
  v : ℝ
  rc : ℝ
  F : Finset (Fin n)
  stopped : Bool

open Classical in
/-- The live coordinates: `|xᵢ| < 1`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18. -/
noncomputable def liveSet {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => |x i| < 1

/-- The nearest sign, a tie resolved as `+1`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Appendix C.1, p.77. -/
noncomputable def nearestSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

open Classical in
/-- The diagonal projection onto the coordinates `I₀`: the identity covariance `I_ℓ` on `ℝ^{I₀}`, with
all `n` coordinates kept in the coefficient space (Remark 7.2, p.49). -/
noncomputable def diagOn {n : ℕ} (I₀ : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if i ∈ I₀ then 1 else 0

/-- The start of a trial from the saved point `x∗`: line 1 of Algorithm 2. -/
noncomputable def trialInit {n : ℕ} (xs : Fin n → ℝ) : TrialState n :=
  { x := xs, C := diagOn (liveSet xs), moves := 0, y := 0, a := 0, u := 0, v := 0, rc := 0, F := ∅,
    stopped := false }

open Classical in
/-- Line 10 of Algorithm 2: round each live `xᵢ` with `1 - |xᵢ| ≤ a₀` to its nearest sign and freeze it. -/
noncomputable def roundState {n : ℕ} (I₀ : Finset (Fin n)) (s : TrialState n) : TrialState n :=
  let R := (I₀ \ s.F).filter fun i => 1 - |s.x i| ≤ marginA n
  { s with
    x := fun i => if i ∈ R then nearestSign (s.x i) else s.x i
    rc := s.rc + ∑ i ∈ R, |nearestSign (s.x i) - s.x i|
    F := s.F ∪ R }

open Classical in
/-- One pass through the loop of Algorithm 2 from the saved point `xs`: the while test, Prepare with
its loss test, then the uniform choice of `(j, ±)` from the `2k` possibilities, the tangent move with
`ξ = ±√(k/2) u_j`, and rounding. A stopped state is absorbing.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 2, p.78; Section 7.2, p.50.

**Formalization Note** The empty basis stops the trial; Lemma 7.5 shows it never occurs. -/
noncomputable def trialStep {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (xs : Fin n → ℝ) (s : TrialState n) : PMF (TrialState n) :=
  let I₀ := liveSet xs
  let ℓ := I₀.card
  let h := stepH n m par
  if s.stopped = true ∨ ¬((s.moves : ℝ) * h ^ 2 + h ^ 2 ≤ par.τ ∧ (s.F.card : ℝ) < (ℓ : ℝ) / 8 ∧
      s.a + s.u ≤ (ℓ : ℝ) / 32) then
    PMF.pure { s with stopped := true }
  else
    let r := P.prep ℓ (s.a + s.u) (center A s.x) s.C
    let s₁ : TrialState n := { s with C := r.1, a := s.a + r.2.1, u := s.u + r.2.2 }
    if (ℓ : ℝ) / 32 < s₁.a + s₁.u then
      PMF.pure { s₁ with stopped := true }
    else
      match P.basis s₁.C s₁.x s₁.F with
      | [] => PMF.pure { s₁ with stopped := true }
      | w :: ws =>
        let l := w :: ws
        let k : ℝ := (l.length : ℝ)
        (PMF.uniformOfFintype (Fin l.length × Bool)).map fun p =>
          let ξ : Fin n → ℝ := ((if p.2 then 1 else -1 : ℝ) * Real.sqrt (k / 2)) • l.get p.1
          roundState I₀
            { s₁ with
              x := s₁.x + h • ξ
              y := s₁.y + h • ξ
              C := s₁.C - h ^ 2 • moveCov l
              moves := s₁.moves + 1
              v := s₁.v + h ^ 2 * (k / 2) }

/-- The law of the state after `k` passes through the loop. -/
noncomputable def trialIter {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (xs : Fin n → ℝ) : ℕ → PMF (TrialState n)
  | 0 => PMF.pure (trialInit xs)
  | k + 1 => (trialIter P A par xs k).bind (trialStep P A par xs)

/-- The law of the terminal state of a trial from `xs`. A trial has at most `⌊τ/h²⌋` movements
(Lemma 7.5), so `⌊τ/h²⌋ + 1` passes reach a stopped state, and the law has finite support.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 2, p.78; Lemma 7.5, p.52. -/
noncomputable def trialLaw {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) (xs : Fin n → ℝ) : PMF (TrialState n) :=
  trialIter P A par xs (⌊par.τ / stepH n m par ^ 2⌋₊ + 1)

end FreeSpencer


