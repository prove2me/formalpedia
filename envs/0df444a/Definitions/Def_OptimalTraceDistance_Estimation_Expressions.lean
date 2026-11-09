-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Expressions
-- name    : OptimalTraceDistance_Estimation_Expressions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:37:24.891905+00:00
-- url     : https://prove2.me/theorems/f138861d-5085-41a5-8f95-953d3206631a
-- title:
--   Ordered trace words and the constructed multiscale expression
-- statement:
--   A matrix word is $(A_1X_{t_1}\cdots A_kX_{t_k})B$, with known matrices, labels $t_i\in\{0,1\}$, and ordered multiplication. Matrix expressions are finite sums of words. Multiplication distributes without commuting factors; scaling and substitution retain every word. A trace expression is a complex scalar constant plus a finite sum of single traces. Its degree is the maximum number of variable occurrences in its chosen words. Realness on Hermitian inputs is a predicate, not a structural accuracy condition.
--
--   The order-$j$ Taylor coefficient is obtained by substituting $X+tE_0,Y+tE_1$ in the retained words and reading the coefficient of the central scalar variable. Bounded ordered representations assert (15) for all complex perturbations with (16). The scale count, scale degrees, directly filtered $Y_\ell$, multiscale sum (13), compression substitution and complete correction (27) are explicit finite expressions. Construction constants are parameters here. The filtered sequence is computed from $Y$ at each scale, without recursive filtering.
--
--   Compression substitutes QXQ and QYQ into each variable occurrence. In a nonempty word its first known factor becomes A₁Q, internal factors become QAᵢQ, and the tail becomes QB; variable-free words remain unchanged. This preserves arbitrary known coefficients, including off-diagonal ones.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), §§2.3–2.4 and Algorithm 2, pp.8–11.

import Definitions.Def_OptimalTraceDistance_Estimation_Scalar

open scoped BigOperators Matrix
noncomputable section

namespace OptimalTraceDistance.Estimation

/-- Ordered word (A₁Xₜ₁⋯AₖXₜₖ)B. The trailing B permits exact multiplication and compression. -/
structure Word (d : ℕ) where
  factors : List (Mat d × Bool)
  tail : Mat d

abbrev MatrixExpression (d : ℕ) := List (Word d)

def wordMul {d : ℕ} (u v : Word d) : Word d :=
  match v.factors with
  | [] => ⟨u.factors, u.tail * v.tail⟩
  | (A,t) :: xs => ⟨u.factors ++ ((u.tail * A,t) :: xs), v.tail⟩
def exprConst {d : ℕ} (A : Mat d) : MatrixExpression d := [⟨[], A⟩]
def exprVar (d : ℕ) (t : Bool) : MatrixExpression d := [⟨[(1,t)],1⟩]
def exprMul {d : ℕ} (u v : MatrixExpression d) : MatrixExpression d :=
  u.flatMap (fun a => v.map (wordMul a))
def exprScale {d : ℕ} (c : ℝ) (u : MatrixExpression d) : MatrixExpression d :=
  u.map (fun w => ⟨w.factors,(c : ℂ) • w.tail⟩)
def exprPow {d : ℕ} (u : MatrixExpression d) : ℕ → MatrixExpression d
  | 0 => exprConst 1
  | k+1 => exprMul (exprPow u k) u

def exprPoly {d : ℕ} (p : Polynomial ℝ) (u : MatrixExpression d) : MatrixExpression d :=
  p.support.toList.flatMap (fun k => exprScale (p.coeff k) (exprPow u k))
def exprCompress {d : ℕ} (Q : Mat d) (u : MatrixExpression d) : MatrixExpression d :=
  exprMul (exprMul (exprConst Q) u) (exprConst Q)
def wordEval {d : ℕ} (w : Word d) (X Y : Mat d) : Mat d :=
  (w.factors.map (fun At => At.1 * (if At.2 then Y else X))).prod * w.tail

def wordLine {d : ℕ} (w : Word d) (X Y E₀ E₁ : Mat d) : Polynomial (Mat d) :=
  (w.factors.map (fun At => Polynomial.C At.1 *
    (Polynomial.C (if At.2 then Y else X) +
      Polynomial.X * Polynomial.C (if At.2 then E₁ else E₀)))).prod * Polynomial.C w.tail

/-- Single traces only. The chosen words and syntactic degree remain available to Algorithm 1. -/
structure TraceExpression (d : ℕ) where
  constant : ℂ
  words : MatrixExpression d

def traceExpr {d : ℕ} (u : MatrixExpression d) : TraceExpression d := ⟨0,u⟩
def expressionDegree {d : ℕ} (f : TraceExpression d) : ℕ :=
  (f.words.map (fun w => w.factors.length)).foldl max 0
def evaluate {d : ℕ} (f : TraceExpression d) (X Y : Mat d) : ℂ :=
  f.constant + (f.words.map (fun w => (wordEval w X Y).trace)).sum
def realOnHermitian {d : ℕ} (f : TraceExpression d) : Prop :=
  ∀ X Y, X.IsHermitian → Y.IsHermitian → (evaluate f X Y).im = 0

def taylor {d : ℕ} (f : TraceExpression d) (X Y : Mat d) (j : ℕ) (E₀ E₁ : Mat d) : ℂ :=
  (if j = 0 then f.constant else 0) +
    (f.words.map (fun w => ((wordLine w X Y E₀ E₁).coeff j).trace)).sum

/-- Ordered representation (15)-(16). The identity quantifies over ALL complex perturbations. -/
def HasOrderedBound {d : ℕ} (j : ℕ) (Φ : Mat d → Mat d → ℂ) (M : ℝ) : Prop :=
  ∃ (L : ℕ) (c : Fin L → ℂ) (A : Fin L → Fin (j+1) → Mat d)
      (t : Fin L → Fin j → Bool),
    (∀ E₀ E₁, Φ E₀ E₁ = ∑ α, c α *
      (((List.ofFn (fun i : Fin j => A α i.castSucc * (if t α i then E₁ else E₀))).prod *
        A α (Fin.last j)).trace)) ∧
    (∑ α, ‖c α‖ * ∏ i, opNorm (A α i)) ≤ M

def scales (d : ℕ) (ε : ℝ) : ℕ := ⌈Real.log (2^9 * d / ε) / Real.log 2⌉₊
def scaleDegree (A : ℝ) (d : ℕ) (ε : ℝ) (l : ℕ) : ℕ :=
  ⌈A / ε * Real.sqrt (min 1 ((d : ℝ) * (2 : ℝ)^(-(l : ℤ))))⌉₊
def filteredY (d l : ℕ) : MatrixExpression d :=
  if l = 0 then exprVar d true else
    let r := exprPoly (filter ((2 : ℝ)^(-(l : ℤ)))) (exprVar d false)
    exprMul (exprMul r (exprVar d true)) r

def multiscale (A : ℝ) (d : ℕ) (ε : ℝ) : TraceExpression d :=
  traceExpr ((List.range (scales d ε)).flatMap (fun i =>
    let l := i+1
    let p := q (scaleDegree A d ε l)
    let s := (2 : ℝ)^((l : ℤ)-9)
    let a := exprPoly p (exprScale s (filteredY d (l-1)))
    let b := exprPoly p (exprScale s (filteredY d l))
    exprScale s⁻¹ (a ++ exprScale (-1) b)))

/-- Substitute QXQ and QYQ without compressing the known coefficients.
For a nonempty word the boundary factors are A₁Q and QB; only internal
coefficients have Q on both sides. A variable-free word is unchanged. -/
def substituteCompression {d : ℕ} (Q : Mat d) (f : TraceExpression d) : TraceExpression d :=
  ⟨f.constant, f.words.map (fun w =>
    match w.factors with
    | [] => w
    | (A,t) :: xs =>
      ⟨(A * Q,t) :: xs.map (fun At => (Q * At.1 * Q, At.2)), Q * w.tail⟩)⟩

/-- (26)-(27), with the equality ε log d=1 in the univariate branch. -/
def estimatorExpression (A C₀ : ℝ) (d : ℕ) (ε : ℝ) (Q : Mat d) : TraceExpression d :=
  let fr := if ε * Real.log d ≤ 1 then
      traceExpr (exprPoly (q ⌈C₀*d/ε⌉₊) (exprVar d true))
    else multiscale A d (ε/8)
  let correction := exprPoly (q ⌈C₀*Real.log d/ε⌉₊) (exprVar d true)
  let r := substituteCompression Q fr
  let c := substituteCompression Q (traceExpr correction)
  ⟨r.constant-c.constant, r.words ++ correction ++ exprScale (-1) c.words⟩

end OptimalTraceDistance.Estimation


