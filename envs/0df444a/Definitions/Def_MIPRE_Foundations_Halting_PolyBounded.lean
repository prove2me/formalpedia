-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
-- name    : MIPRE_Foundations_Halting_PolyBounded
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:47:37.422285+00:00
-- url     : https://prove2.me/theorems/2aa30def-46e1-4874-9431-dcfc098f8afe
-- title:
--   Polynomially bounded functions and polynomially bounded program costs
-- statement:
--   Let `Polynomial ℕ` be the polynomials over $\mathbb{N}$, `Data` the binary trees of the ambient model with `d.size`, `Prog` its programs with `p.Runs x r t`, and `Nat.size` the number of binary digits. Names are in `MIPRE.Cost`.
--
--   `PolyBounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n`. `PolyBounded.poly (hf : PolyBounded f) : Polynomial ℕ` is a polynomial chosen from the witness, with `le_poly_eval : f n ≤ hf.poly.eval n`. `PolyCost (f : ℕ → Data → ℕ) : Prop := ∃ (C : ℕ → ℕ) (k : ℕ), PolyBounded C ∧ ∀ n d, f n d ≤ C n * (d.size + 1) ^ k`, a cost function of an index and an input bounded by $C(n)\,(|d|+1)^k$ with $C$ polynomially bounded and $k$ constant. `Prog.HasPolyCost (p : Prog) : Prop := ∃ (C : ℕ → ℕ) (k : ℕ), PolyBounded C ∧ ∀ n d, ∃ r t, t ≤ C n * (d.size + 1) ^ k ∧ p.Runs (.cons (encode n) d) r t`: `p` halts on every input `(n, d)` within such a bound.
--
--   The closure lemmas for `PolyBounded` are `const`, `id`, `mono` (domination by a polynomially bounded function), `add`, `mul`, `pow`, `const_mul`, `add_const`, `eval` (a fixed polynomial at a polynomially bounded argument), `comp` (a polynomially bounded function of a polynomially bounded argument), `size` (`Nat.size`) and `two_mul_add_one`; for `PolyCost` they are `const`, `ofIndex`, `size`, `add` (exponent $\max(k_1, k_2)$), `mul` (exponent $k_1 + k_2$) and `poly` (a fixed polynomial of a polynomially bounded cost, the universal machine's overhead). The two threshold lemmas are `exists_le_two_pow` ($\exists n_0, \forall n \ge n_0, f(n) \le 2^n$) and
--
--   $$\mathrm{PolyBounded}\, f \implies \exists\, \lambda,\ \forall n \ge 2,\ f(n) \le n^{\lambda}$$
--
--   (`exists_le_pow`), a single exponent for every index. The time accounting of the instantiation composes a dozen explicit cost bounds; what the argument needs is only that the total is bounded by some polynomial in the level, and these lemmas let the bounds be composed without writing the polynomial down.
--
--   **Formalization Note**. `PolyCost` is exactly the shape of `Decider.TimeBoundAt` ($T \cdot (|d|+1)^k$) and `exists_le_pow` the shape `Verifier.IsBounded` asks for ($n^\lambda$ for all $n \ge 2$); `HasPolyCost` is the hypothesis the deciders of the instantiation carry, and its equivalence with boundedness (a module lemma) is not in this bundle. Polynomials over `ℕ` are monotone, so `comp` needs no monotonicity of the outer function. `poly` uses `Exists.choose` and is noncomputable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/PolyBounded.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/PolyBounded.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Theorems.Thm_MIPRE_Cost_mul_pow_le_two_pow

/-!
# Polynomially bounded functions

The time accounting of the instantiation (`Halting/Wrapper.lean`, `Halting/Compressor.lean`)
composes a dozen explicit cost bounds, each a polynomial in the values it depends on. What the
argument eventually needs is only that the total is bounded by *some* polynomial in the level,
so that it falls under `2 ^ n` above a threshold. `PolyBounded f` records exactly that —
`f n ≤ P.eval n` for some `P : Polynomial ℕ` — with the closure properties that let the
bounds be composed without ever writing the polynomial down:

* constants, the identity, sums, products, powers, `Nat.size`;
* `PolyBounded.comp`: a polynomially bounded function of a polynomially bounded function;
* `PolyBounded.eval`: a fixed polynomial evaluated at a polynomially bounded argument;
* `PolyBounded.mono`: domination by a polynomially bounded function;
* `PolyBounded.exists_le_two_pow`: the threshold, `f n ≤ 2 ^ n` for all `n` above some `n₀`;
  `PolyBounded.exists_le_pow`: a single `λ` with `f n ≤ n ^ λ` for *every* `n ≥ 2`, which is the
  shape `Verifier.IsBounded` asks for.

`PolyCost` and `HasPolyCost` are the same notion for the cost of a program at index `n` on an
input `d`: bounded by `C n · (|d| + 1) ^ k` with `C` polynomially bounded and `k` constant —
exactly what `Decider.TimeBoundAt` asks for, and what the stages of a decider's run compose
into (`PolyCost.add`, `mul`, `poly`, the last being the universal machine's overhead).

The polynomial of a `PolyBounded` function can be extracted (`PolyBounded.choose`) where an
explicit `Polynomial ℕ` is required, as in the `timeBound` field of `PolyTimeFun`.
-/

namespace MIPRE.Cost

open Polynomial

/-- `f` is bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

namespace PolyBounded

theorem const (c : ℕ) : PolyBounded fun _ => c := ⟨C c, fun _ => by simp⟩

theorem id : PolyBounded fun n => n := ⟨X, fun _ => by simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) : PolyBounded f :=
  let ⟨P, hP⟩ := hg
  ⟨P, fun n => (h n).trans (hP n)⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n + g n :=
  let ⟨P, hP⟩ := hf
  let ⟨Q, hQ⟩ := hg
  ⟨P + Q, fun n => by simp only [eval_add]; exact Nat.add_le_add (hP n) (hQ n)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n * g n :=
  let ⟨P, hP⟩ := hf
  let ⟨Q, hQ⟩ := hg
  ⟨P * Q, fun n => by simp only [eval_mul]; exact Nat.mul_le_mul (hP n) (hQ n)⟩

theorem pow {f : ℕ → ℕ} (hf : PolyBounded f) (k : ℕ) : PolyBounded fun n => f n ^ k := by
  induction k with
  | zero => exact (const 1).mono fun n => by simp
  | succ k ih => exact (ih.mul hf).mono fun n => by rw [pow_succ]

theorem const_mul {f : ℕ → ℕ} (c : ℕ) (hf : PolyBounded f) : PolyBounded fun n => c * f n :=
  (const c).mul hf

theorem add_const {f : ℕ → ℕ} (hf : PolyBounded f) (c : ℕ) : PolyBounded fun n => f n + c :=
  hf.add (const c)

/-- A fixed polynomial at a polynomially bounded argument. -/
theorem eval (P : Polynomial ℕ) {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded fun n => P.eval (f n) :=
  let ⟨Q, hQ⟩ := hf
  ⟨P.comp Q, fun n => by rw [eval_comp]; exact polynomial_eval_mono P (hQ n)⟩

/-- A polynomially bounded function of a polynomially bounded argument. Polynomials over `ℕ`
are monotone, so no monotonicity of `g` is needed. -/
theorem comp {g f : ℕ → ℕ} (hg : PolyBounded g) (hf : PolyBounded f) :
    PolyBounded fun n => g (f n) :=
  let ⟨Q, hQ⟩ := hg
  (eval Q hf).mono fun n => hQ (f n)

theorem size : PolyBounded Nat.size :=
  id.mono fun _ => Nat.size_le.2 Nat.lt_two_pow_self

theorem two_mul_add_one : PolyBounded fun n => 2 * n + 1 := (id.const_mul 2).add_const 1

/-- The polynomial of a polynomially bounded function. -/
noncomputable def poly {f : ℕ → ℕ} (hf : PolyBounded f) : Polynomial ℕ := Exists.choose hf

theorem le_poly_eval {f : ℕ → ℕ} (hf : PolyBounded f) (n : ℕ) : f n ≤ hf.poly.eval n :=
  Exists.choose_spec hf n

/-- **The threshold.** A polynomially bounded function is below `2 ^ n` from some `n₀` on. -/
theorem exists_le_two_pow {f : ℕ → ℕ} (hf : PolyBounded f) : ∃ n₀, ∀ n, n₀ ≤ n → f n ≤ 2 ^ n := by
  obtain ⟨P, hP⟩ := hf
  set A := ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i with hA
  set D := P.natDegree with hD
  refine ⟨A * (D + 1) ^ (D + 1) + 1, fun n hn => ?_⟩
  have h1 : P.eval n ≤ A * n ^ D := polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h2 : A * n ^ D ≤ 2 ^ n := mul_pow_le_two_pow A D n (by omega)
  exact (hP n).trans (h1.trans h2)

/-- **A single exponent for every index.** A polynomially bounded function is below `n ^ λ` for
one `λ` and *all* `n ≥ 2` — the form `Verifier.IsBounded` asks for. -/
theorem exists_le_pow {f : ℕ → ℕ} (hf : PolyBounded f) : ∃ lam, ∀ n, 2 ≤ n → f n ≤ n ^ lam := by
  obtain ⟨P, hP⟩ := hf
  set A := ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i with hA
  set D := P.natDegree with hD
  refine ⟨D + A, fun n hn => ?_⟩
  have h1 : P.eval n ≤ A * n ^ D := polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h2 : A ≤ 2 ^ A := Nat.le_of_lt Nat.lt_two_pow_self
  have h3 : (2 : ℕ) ^ A ≤ n ^ A := Nat.pow_le_pow_left hn A
  calc f n ≤ A * n ^ D := (hP n).trans h1
    _ ≤ n ^ A * n ^ D := Nat.mul_le_mul_right _ (h2.trans h3)
    _ = n ^ (D + A) := by rw [← pow_add, Nat.add_comm]

end PolyBounded

/-! ## Costs, polynomially bounded in the index and in the input -/

/-- A cost function of an index and an input, bounded by `C n · (|d| + 1) ^ k` with `C`
polynomially bounded and `k` constant. -/
def PolyCost (f : ℕ → Data → ℕ) : Prop :=
  ∃ (C : ℕ → ℕ) (k : ℕ), PolyBounded C ∧ ∀ n d, f n d ≤ C n * (d.size + 1) ^ k

namespace PolyCost

theorem const (c : ℕ) : PolyCost fun _ _ => c :=
  ⟨fun _ => c, 0, PolyBounded.const c, fun _ d => by simp⟩

theorem ofIndex {g : ℕ → ℕ} (hg : PolyBounded g) : PolyCost fun n _ => g n :=
  ⟨g, 0, hg, fun _ d => by simp⟩

theorem size : PolyCost fun _ d => d.size :=
  ⟨fun _ => 1, 1, PolyBounded.const 1, fun _ d => by simp⟩

theorem add {f g : ℕ → Data → ℕ} (hf : PolyCost f) (hg : PolyCost g) :
    PolyCost fun n d => f n d + g n d := by
  obtain ⟨C₁, k₁, hC₁, hb₁⟩ := hf
  obtain ⟨C₂, k₂, hC₂, hb₂⟩ := hg
  refine ⟨fun n => C₁ n + C₂ n, max k₁ k₂, hC₁.add hC₂, fun n d => ?_⟩
  show f n d + g n d ≤ (C₁ n + C₂ n) * (d.size + 1) ^ max k₁ k₂
  have e₁ : (d.size + 1) ^ k₁ ≤ (d.size + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (d.size + 1) ^ k₂ ≤ (d.size + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have b₁ := hb₁ n d
  have b₂ := hb₂ n d
  have m₁ : C₁ n * (d.size + 1) ^ k₁ ≤ C₁ n * (d.size + 1) ^ max k₁ k₂ :=
    Nat.mul_le_mul_left _ e₁
  have m₂ : C₂ n * (d.size + 1) ^ k₂ ≤ C₂ n * (d.size + 1) ^ max k₁ k₂ :=
    Nat.mul_le_mul_left _ e₂
  have hsum : (C₁ n + C₂ n) * (d.size + 1) ^ max k₁ k₂ =
      C₁ n * (d.size + 1) ^ max k₁ k₂ + C₂ n * (d.size + 1) ^ max k₁ k₂ := by ring
  omega

theorem mul {f g : ℕ → Data → ℕ} (hf : PolyCost f) (hg : PolyCost g) :
    PolyCost fun n d => f n d * g n d := by
  obtain ⟨C₁, k₁, hC₁, hb₁⟩ := hf
  obtain ⟨C₂, k₂, hC₂, hb₂⟩ := hg
  refine ⟨fun n => C₁ n * C₂ n, k₁ + k₂, hC₁.mul hC₂, fun n d => ?_⟩
  show f n d * g n d ≤ C₁ n * C₂ n * (d.size + 1) ^ (k₁ + k₂)
  calc f n d * g n d ≤ (C₁ n * (d.size + 1) ^ k₁) * (C₂ n * (d.size + 1) ^ k₂) :=
        Nat.mul_le_mul (hb₁ n d) (hb₂ n d)
    _ = C₁ n * C₂ n * (d.size + 1) ^ (k₁ + k₂) := by rw [pow_add]; ring

/-- A fixed polynomial at a polynomially bounded cost: the universal machine's overhead. -/
theorem poly (P : Polynomial ℕ) {f : ℕ → Data → ℕ} (hf : PolyCost f) :
    PolyCost fun n d => P.eval (f n d) := by
  obtain ⟨C, k, hC, hb⟩ := hf
  set A := ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i with hA
  set D := P.natDegree with hD
  refine ⟨fun n => A * (C n + 1) ^ D, k * D, ((hC.add_const 1).pow D).const_mul A, fun n d => ?_⟩
  show P.eval (f n d) ≤ A * (C n + 1) ^ D * (d.size + 1) ^ (k * D)
  have h1 : P.eval (f n d) ≤ P.eval (C n * (d.size + 1) ^ k) := polynomial_eval_mono P (hb n d)
  have h2 : P.eval (C n * (d.size + 1) ^ k + 1) ≤ A * (C n * (d.size + 1) ^ k + 1) ^ D :=
    polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h3 : P.eval (C n * (d.size + 1) ^ k) ≤ P.eval (C n * (d.size + 1) ^ k + 1) :=
    polynomial_eval_mono P (by omega)
  have h4 : C n * (d.size + 1) ^ k + 1 ≤ (C n + 1) * (d.size + 1) ^ k := by
    have : 1 ≤ (d.size + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h5 : ((C n + 1) * (d.size + 1) ^ k) ^ D = (C n + 1) ^ D * (d.size + 1) ^ (k * D) := by
    rw [mul_pow, ← pow_mul]
  calc P.eval (f n d) ≤ A * (C n * (d.size + 1) ^ k + 1) ^ D := h1.trans (h3.trans h2)
    _ ≤ A * ((C n + 1) * (d.size + 1) ^ k) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 D)
    _ = A * (C n + 1) ^ D * (d.size + 1) ^ (k * D) := by rw [h5]; ring

end PolyCost

/-- A program whose cost at index `n` on input `d` is polynomially bounded: the hypothesis the
deciders of the instantiation carry, and (through `hasPolyCost_iff_exists_isBounded`) what
`λ`-boundedness comes from. -/
def Prog.HasPolyCost (p : Prog) : Prop :=
  ∃ (C : ℕ → ℕ) (k : ℕ), PolyBounded C ∧
    ∀ (n : ℕ) (d : Data), ∃ r t, t ≤ C n * (d.size + 1) ^ k ∧ p.Runs (.cons (encode n) d) r t

end MIPRE.Cost


