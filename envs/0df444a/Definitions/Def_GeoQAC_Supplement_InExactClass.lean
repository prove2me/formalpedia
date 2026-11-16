-- Prove2me | Definitions.Def_GeoQAC_Supplement_InExactClass
-- name    : GeoQAC_Supplement_InExactClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:43.004571+00:00
-- url     : https://prove2.me/theorems/1360716a-1f56-4fc6-b8bb-50cae8bf55db
-- title:
--   The class $\mathcal F_{h,w,d}$ and PAC success of a learner
-- statement:
--   Fix a layout: the grid $[w]\times[h]$ and the positions of the $n$ input qubits, the other qubits being ancillas in $|0\rangle$. **$\mathcal F_{h,w,d}$** is the set of Boolean functions computed exactly by some 2D-QAC circuit of depth at most $d$ on this layout, with some output qubit. A **learner** with $m$ examples is any map from $m$ labeled examples $(x_i,f(x_i))$ to a hypothesis $\tilde f:\{0,1\}^n\to\{0,1\}$. It **$(\varepsilon,\delta)$-learns** $f$ if, for $x_1,\dots,x_m$ independent and uniform,
--   $$
--   \Pr_{x_1,\dots,x_m}\Big[\Pr_x[\tilde f(x)\ne f(x)]\le\varepsilon\Big]\ge 1-\delta .
--   $$
--
--   These notions state the sample-complexity bound of Theorem A.4.
--
--   **Formalization Note** No running time is bounded and the hypothesis may lie outside the class. With uniform samples the probabilities are finite counts over the $2^{nm}$ example tuples and the $2^n$ inputs.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Appendix A, p.38

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_ComputesWithProb

namespace GeoQAC.Supplement

open GeoQAC

/-!
# The class `F_{h,w,d}` and PAC success of a learner

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Appendix A, p.38: "fix the parameters
`h, w, d` and the locations of the `n` input qubits and `a = wh − n` ancillas, all known to the
learner. The ancillas begin in a fixed product state, which we take to be `|0^a⟩` by one-qubit gates.
Let `F_{h,w,d}` be the Boolean functions decided exactly by circuits on this layout with depth at
most `d`. The learner receives independent classical examples `(x, f(x))`, with `x` uniform on
`{0,1}^n`, and may return a hypothesis outside `F_{h,w,d}`." Theorem A.4: "With probability at least
`1 − δ`, the returned hypothesis `f̃` satisfies `Pr_x[f̃(x) ≠ f(x)] ≤ ε`."

**Formalization Note.**
* The layout is `Pos w h` with inputs at `inp`; `F_{h,w,d}` is the set of `f` computed exactly
  (published `GeoQAC.ComputesExactly`) from `|0⟩` ancillas by some 2D-QAC circuit of depth
  `D ≤ d` with some output qubit.
* A learner with `m` examples is any function from `m` labeled examples to a hypothesis; no running
  time is bounded (p.38–39).
* The `m` examples are i.i.d. uniform, so probabilities are counts: `xs` ranges over the `2^{nm}`
  tuples and `x` over the `2^n` inputs.
-/

/-- `f ∈ F_{h,w,d}` for the layout `(w, h, inp)` (Appendix A, p.38). -/
def InExactClass {n : ℕ} (w h d : ℕ) (inp : Fin n ↪ Pos w h) (f : (Fin n → Bool) → Bool) :
    Prop :=
  ∃ (D : ℕ) (C : QACCircuit (Pos w h) D) (out : Pos w h),
    D ≤ d ∧ C.Is2D ∧ ComputesExactly C inp (fun _ => ket0) out f

/-- The learner `L` with `m` uniform examples `(ε, δ)`-learns the target `f` (Theorem A.4, p.38):
the fraction of example tuples `xs` for which the hypothesis `L((xs i, f(xs i))_i)` disagrees with
`f` on at most an `ε` fraction of inputs is at least `1 − δ`. -/
def LearnsTarget {n m : ℕ} (L : (Fin m → (Fin n → Bool) × Bool) → (Fin n → Bool) → Bool)
    (f : (Fin n → Bool) → Bool) (ε δ : ℝ) : Prop :=
  (1 - δ) * (2 : ℝ) ^ (n * m) ≤
    ((Finset.univ.filter fun xs : Fin m → (Fin n → Bool) =>
      ((Finset.univ.filter fun x => L (fun i => (xs i, f (xs i))) x ≠ f x).card : ℝ) ≤
        ε * 2 ^ n).card : ℝ)

end GeoQAC.Supplement


