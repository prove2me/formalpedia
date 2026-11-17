-- Prove2me | Definitions.Def_PhaseEncodedQGE_Supplement_ClassValue
-- name    : PhaseEncodedQGE_Supplement_ClassValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:28:56.033215+00:00
-- url     : https://prove2.me/theorems/1c5351f6-9efd-4ee4-a00c-67704f4f8d67
-- title:
--   Degree-prepared members, the two-defect classes, the class value $f(a,k)$ and its increments $\Delta_k$, $\Delta_a$
-- statement:
--   1. The **degree-prepared members** are PE-X1 (the $X$ mixer, one repetition, profile $h^{X,1}$), PE-Y1 (the $Y$ mixer, one repetition, profile $h^Y$) and PE-X2 (the $X$ mixer, two tied repetitions, profile $h^{X,2}$), each with the degree-aware preparation; $h^{X,r}(k)=\sum_{b=1}^r\cos(b\gamma(2k-3))$ and $h^Y(k)=\sin(\gamma(2k-3))$.
--   2. The **seven two-defect classes** are $(a,k)\in\{0,1\}\times\{0,1,2,3\}\setminus\{(1,3)\}$.
--   3. For a profile $h$, a ratio $t$ and $n$ vertices, the **class value** is
--   $$f(a,k)=\frac{(n-8+2a+k)h(0)+(6-2a-2k)h(1)+k\,h(2)}{t}-2t\,h(a),$$
--   with the **increments**
--   $$\Delta_k=\frac{h(0)-2h(1)+h(2)}{t},\qquad \Delta_a=2\big(h(0)-h(1)\big)\Big(t+\frac1t\Big).$$
--   4. A function of the class labels is **injective on the classes** if it takes seven distinct values on the seven classes.
--
--   These are the objects of Theorem A.11 (= Theorem 4.1), which computes the first-order value of every two-defect outcome and decides when the two-defect block resolves all seven classes.
--
--   **Formalization Note** $n$, $a$, $k$ are cast to real numbers before subtracting. Lean's $x/0=0$ applies at $t=0$; every statement using these objects assumes $\cos(\eta/2)\ne0\ne\sin(\eta/2)$, so $t=\tan(\eta/2)\ne0$.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.3, p.16 (PDF p.17), Lemma A.10 and Theorem A.11, eqs. (28)–(30); §3.1, p.6 (PDF p.7), eq. (8)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- The degree-prepared members with their mixer profiles (Miller, Lee, *Structural Accessibility
in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §2, p.4;
§3.1, p.6, eq. (8); App. A.1.1, p.14, eqs. (23)–(24)): PE-X1 is the `X` mixer with one
repetition and profile `h^{X,1}`, PE-Y1 the `Y` mixer with one repetition and profile `h^Y`, and
PE-X2 the `X` mixer with two tied repetitions and profile `h^{X,2}`, all at mixer-phase angle `γ`
under the degree-aware preparation.

**Formalization Note** `IsDegMember γ P r h` says that `(P, r, h)` is the axis, repetition count
and profile of one of the three members; the preparation (`degPrep G η`) is supplied by each
statement. -/
def IsDegMember (γ : ℝ) (P : Axis) (r : ℕ) (h : ℕ → ℝ) : Prop :=
  (P = .X ∧ r = 1 ∧ h = hX 1 γ) ∨ (P = .Y ∧ r = 1 ∧ h = hY γ) ∨ (P = .X ∧ r = 2 ∧ h = hX 2 γ)

/-- The seven two-defect classes realizable on cubic graphs,
`(a, k) ∈ {0, 1} × {0, 1, 2, 3} \ {(1, 3)}` (§2, p.5; Lemma A.10, p.16). -/
def IsPairClass (a k : ℕ) : Prop := (a = 0 ∧ k ≤ 3) ∨ (a = 1 ∧ k ≤ 2)

/-- The two-defect class value
`f(a, k) = [(n − 8 + 2a + k) h(0) + (6 − 2a − 2k) h(1) + k h(2)]/t − 2t h(a)`
(Theorem A.11, p.16, eq. (28) = Theorem 4.1, p.8, eq. (12)) for a mixer profile `h`, the
preparation ratio `t`, the number of vertices `n` and the class labels `(a, k)`.

**Formalization Note** `n`, `a`, `k` are cast to `ℝ` before any subtraction. Lean's `x / 0 = 0`
applies at `t = 0`; every statement using `f` assumes `cos(η/2) ≠ 0 ≠ sin(η/2)`, so `t ≠ 0`. -/
noncomputable def classValue (h : ℕ → ℝ) (t : ℝ) (n a k : ℕ) : ℝ :=
  (((n : ℝ) - 8 + 2 * (a : ℝ) + (k : ℝ)) * h 0 + (6 - 2 * (a : ℝ) - 2 * (k : ℝ)) * h 1 +
      (k : ℝ) * h 2) / t - 2 * t * h a

/-- The codegree increment `∆_k = [h(0) − 2h(1) + h(2)]/t` (Theorem A.11, p.16, eq. (29)). -/
noncomputable def incrK (h : ℕ → ℝ) (t : ℝ) : ℝ := (h 0 - 2 * h 1 + h 2) / t

/-- The adjacency increment `∆_a = 2(h(0) − h(1))(t + 1/t)` (Theorem A.11, p.16, eq. (30)). -/
noncomputable def incrA (h : ℕ → ℝ) (t : ℝ) : ℝ := 2 * (h 0 - h 1) * (t + 1 / t)

/-- A class-value function takes seven distinct values on the seven classes: it is injective on
`{(a, k) : IsPairClass a k}` (Theorem A.11, p.16, "takes seven distinct values on the seven
classes"; "injective", p.16, last sentence of the statement). -/
def ClassInjective (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ a k a' k' : ℕ, IsPairClass a k → IsPairClass a' k' → f a k = f a' k' → a = a' ∧ k = k'

end PhaseEncodedQGE.Supplement


