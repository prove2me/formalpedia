-- Prove2me | Definitions.Def_KhachiyanRounding_BCD_Program
-- name    : KhachiyanRounding_BCD_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:43:42.215921+00:00
-- url     : https://prove2.me/theorems/3a9ddb8c-b59b-46b4-86fe-ad3f501f6437
-- title:
--   Deterministic scalar BCD implementation and output construction
-- statement:
--   The program starts with uniform weights, forms the moment matrix by scalar loops, inverts it by guarded Gauss–Jordan elimination, and computes every initial leverage by scalar dot products. It stores weights, the inverse, and all leverage scores. The stored arrays carry no correctness certificates.
--
--   At every call it scans the scores in a fixed order, retaining the first maximum, and charges the stopping comparison. If the test fails and evaluation fuel remains, it applies the BCD weight update and the paper's rank-one inverse correction, updating every score by the corresponding scalar quadratic expression. If the test fails with exhausted fuel, evaluation fails. The stopping test is performed even at fuel zero, so successful initialization can be returned immediately.
--
--   The symmetric program constructs its enclosing shape matrix by scalar loops. The general program also forms both signed lifted copies, computes the tolerance $n\varepsilon/(n+1)$, aggregates the endpoint weights, and forms the center $b$ and shape $((1+\varepsilon)n)(D-bb^\mathsf T)$. All real arithmetic and comparisons use the costed scalar primitives. No square root or logarithm is called by either program.
--
--   Fuel only defines finite evaluation; the theorem must establish that some fuel succeeds. These definitions assume no termination, geometry, inverse correctness or cost bound.
-- source:
--   Leonid G. Khachiyan (1996), Rounding of Polytopes in the Real Number Model of Computation, Mathematics of Operations Research 21(2), 307–320, https://doi.org/10.1287/moor.21.2.307, §2, (2.18), (2.19), BCD, printed p.312 / PDF p.7; rank-one display and implementation discussion, printed p.314 / PDF p.9; §3, (3.2)–(3.7), printed pp.315–316 / PDF pp.10–11.

import Definitions.Def_KhachiyanRounding_BCD_Scalar
import Definitions.Def_KhachiyanRound_BCD_Setting

namespace KhachiyanRounding.BCD

/-- Ordinary stored arrays, with no correctness, termination or cost fields. -/
structure Registers (ι : Type) (d : ℕ) where
  weights : ι → ℝ
  inverse : Matrix (Fin d) (Fin d) ℝ
  scores : ι → ℝ

/-- Finite generic array filling, in the explicitly supplied index order.
The callers below use complete lists with no repeated indices. -/
noncomputable def fill {ι : Type} [DecidableEq ι] (L : List ι)
    (f : ι → Calc ℝ) : Calc (ι → ℝ) :=
  L.foldlM (fun v i => do
    let x ← f i
    pure (Function.update v i x)) (fun _ => 0)

noncomputable def moment {ι : Type} {d : ℕ} (L : List ι)
    (v : ι → Fin d → ℝ) (p : ι → ℝ) : Calc (Matrix (Fin d) (Fin d) ℝ) :=
  matrix (fun i k => sumList L (fun j => do
    let x ← mul (p j) (v j i)
    mul x (v j k)))

noncomputable def initRegisters {ι : Type} [DecidableEq ι] {d : ℕ}
    (L : List ι) (v : ι → Fin d → ℝ) : Calc (Registers ι d) := do
  let q ← divide 1 (L.length : ℝ)
  let p := fun _ => q
  let A ← moment L v p
  let H ← invert A
  let w ← fill L (fun j => do
    let u ← matvec H (v j)
    dot (v j) u)
  pure ⟨p, H, w⟩

/-- First maximizing index in the specified scan order; ties retain the first.
An empty array fails. Every real comparison is charged. -/
noncomputable def maximum {ι : Type} (L : List ι) (w : ι → ℝ) : Calc ι :=
  match L with
  | [] => fun _ => none
  | r :: tail => tail.foldlM (fun best j => do
      let keep ← le (w j) (w best)
      pure (if keep then best else j)) r

/-- One cached-score BCD update. Every arithmetic expression is decomposed into
scalar primitives. Source: (2.18), (2.19), BCD, and the inverse correction on p.314.
The score update is evaluation of that same rank-one correction on each v_j. -/
noncomputable def update {ι : Type} [DecidableEq ι] {d : ℕ}
    (L : List ι) (v : ι → Fin d → ℝ) (s : Registers ι d) (r : ι) :
    Calc (Registers ι d) := do
  let z ← divide (s.scores r) (d : ℝ)
  let η ← sub z 1
  let wr1 ← sub (s.scores r) 1
  let τ ← divide η wr1
  let scale ← sub 1 τ
  let p ← fill L (fun j => do
    let x ← mul scale (s.weights j)
    if j = r then add x τ else pure x)
  let u ← matvec s.inverse (v r)
  let dm1 ← sub (d : ℝ) 1
  let e1 ← add 1 η
  let den ← mul dm1 e1
  let frac ← divide η den
  let α ← add 1 frac
  let den2 ← mul den e1
  let β ← divide η den2
  let H ← matrix (fun i k => do
    let a ← mul α (s.inverse i k)
    let b ← mul (u i) (u k)
    let c ← mul β b
    sub a c)
  let w ← fill L (fun j => do
    let b ← dot (v j) u
    let b2 ← mul b b
    let c ← mul β b2
    let a ← mul α (s.scores j)
    sub a c)
  pure ⟨p, H, w⟩

/-- Fuel is an evaluator parameter, not a promised runtime or a stopping bound.
Even with zero fuel, perform the charged scan and return on success. Otherwise
fail at exhausted fuel; the full theorems assert some fuel actually succeeds. -/
noncomputable def descend {ι : Type} [DecidableEq ι] {d : ℕ}
    (L : List ι) (v : ι → Fin d → ℝ) (threshold : ℝ) :
    ℕ → Registers ι d → Calc (Registers ι d)
  | fuel, s => do
    let r ← maximum L s.scores
    let stop ← le (s.scores r) threshold
    if stop then pure s else
      match fuel with
      | 0 => fun _ => none
      | k + 1 => do
        let s' ← update L v s r
        descend L v threshold k s'

noncomputable def core {ι : Type} [DecidableEq ι] {d : ℕ}
    (L : List ι) (v : ι → Fin d → ℝ) (δ : ℝ) (fuel : ℕ) : Calc (Registers ι d) := do
  let s ← initRegisters L v
  let e1 ← add 1 δ
  let threshold ← mul e1 (d : ℝ)
  descend L v threshold fuel s

/-- Center and inverse-shape convention are those of LinearOptimization.ellipsoid.
Endpoint registers are retained for relating the computation to the paper. -/
structure Output (ι : Type) (d n : ℕ) where
  endpoint : Registers ι d
  center : Fin n → ℝ
  shape : Matrix (Fin n) (Fin n) ℝ

/-- Full symmetric program, including output construction, no square root calls. -/
noncomputable def symmetric {M d : ℕ} (v : Fin M → Fin d → ℝ)
    (δ : ℝ) (fuel : ℕ) : Calc (Output (Fin M) d d) := do
  let L := List.finRange M
  let s ← core L v δ fuel
  let A ← moment L v s.weights
  let e1 ← add 1 δ
  let t ← mul e1 (d : ℝ)
  let Q ← matrix (fun i k => mul t (A i k))
  pure ⟨s, fun _ => 0, Q⟩

/-- Explicit order on the 2m lifted points, positive copy first. -/
def liftOrder (m : ℕ) : List (Fin m ⊕ Fin m) :=
  (List.finRange m).map Sum.inl ++ (List.finRange m).map Sum.inr

/-- Materialize both lifted copies. Every negation is charged as subtraction. -/
noncomputable def formLift {m n : ℕ} (a : Fin m → Fin n → ℝ) :
    Calc (Fin m ⊕ Fin m → Fin (n + 1) → ℝ) := do
  let pos := fun j => Fin.snoc (α := fun _ => ℝ) (a j) 1
  let neg ← (List.finRange m).foldlM (fun v j => do
    let row ← vector (fun k => sub 0 (pos j k))
    pure (Function.update v j row)) (fun _ _ => 0)
  pure (Sum.elim pos neg)

/-- Theorem 2's complete program. Includes lift/tolerance, cached BCD,
aggregation and scalar computation of center b and shape t(D-bbᵀ).
Source: (3.2)–(3.7), pp.315–316. No output geometry is assumed. -/
noncomputable def general {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (ε : ℝ) (fuel : ℕ) : Calc (Output (Fin m ⊕ Fin m) (n + 1) n) := do
  let v ← formLift a
  let ne ← mul (n : ℝ) ε
  let δ ← divide ne (n + 1 : ℕ)
  let s ← core (liftOrder m) v δ fuel
  let p ← vector (fun j => add (s.weights (Sum.inl j)) (s.weights (Sum.inr j)))
  let b ← vector (fun i => sumList (List.finRange m) (fun j => mul (p j) (a j i)))
  let D ← moment (List.finRange m) a p
  let e1 ← add 1 ε
  let t ← mul e1 (n : ℝ)
  let Q ← matrix (fun i k => do
    let x ← mul (b i) (b k)
    let c ← sub (D i k) x
    mul t c)
  pure ⟨s, b, Q⟩

end KhachiyanRounding.BCD


