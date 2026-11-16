-- Prove2me | Definitions.Def_FourierSparseTesting1656_Uniform_Supplement_DistFree
-- name    : FourierSparseTesting1656_Uniform_Supplement_DistFree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:12:50.918766+00:00
-- url     : https://prove2.me/theorems/c70b9754-2e13-4bd4-b25c-ba79b0cd59f8
-- title:
--   Distribution-free distance $\mathrm{dist}_D$ and testers with sample access to $D$ and query access to $f$
-- statement:
--   Let $V=\mathbb F_2^n$ and let $D$ be a probability distribution on $V$. For Boolean functions $f,g:V\to\{-1,+1\}$ and a set $S$ of Boolean functions,
--   $$\operatorname{dist}_D(f,g)=\Pr_{x\sim D}[f(x)\ne g(x)]=\sum_{x\in V}D(x)\,\mathbf 1[f(x)\ne g(x)],\qquad \operatorname{dist}_D(f,S)=\min_{g\in S}\operatorname{dist}_D(f,g).$$
--
--   A **distribution-free tester** on $V$ consists of
--
--   1. a finite set of internal random seeds $\sigma$ with a probability law;
--   2. a number $m$ of samples;
--   3. a query map, giving for each seed $\sigma$ and each sample vector $x=(x_1,\dots,x_m)\in V^m$ an ordered list of query points;
--   4. an output map, giving a real number (with $1$ meaning accept and $0$ meaning reject) from $\sigma$, $x$ and the ordered list of answers of $f$ at the query points.
--
--   On input $f$ under $D$, a run draws $\sigma$ from its law and $x_1,\dots,x_m$ independently from $D$, independently of $\sigma$, queries $f$ at the listed points and outputs the value of the output map. The probability of output $b$ is
--   $$\Pr[\text{output }b]=\sum_{\sigma}\sum_{x\in V^m}\Pr[\sigma]\prod_{i=1}^m D(x_i)\,\mathbf 1[\text{output}(\sigma,x,f)=b].$$
--   The tester never receives $D$: it sees $D$ only through the samples. The number of samples is $m$ and the number of queries of a run is the length of its query list.
--
--   This is the distribution-free model of property testing of §5 in which Theorem 5.1 is stated.
--
--   **Formalization Note** $\operatorname{dist}_D(f,S)$ is the infimum of the finitely many values $\operatorname{dist}_D(f,g)$, $g\in S$; the file proves $F_s\ne\emptyset$ for $s\ge1$ (it contains the constant $+1$), so on $F_s$ it is the attained minimum. Query points may depend on the seed and the samples but on no oracle answer, the form the paper proves for its tester on p. 23.
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 20, §5 (distribution-free model, dist_D(f,g), dist_D(f,F_s)); p. 22, Algorithm 4 (DistFreeTest); p. 23, §5.2.3 (samples drawn up front, query locations depend on samples but not on answers); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Basic

set_option autoImplicit false

namespace FourierSparseTesting1656.Uniform.Supplement

open FourierDimTesting102.Quantum FourierSparseTesting1656.Uniform

open Classical in
/-- §5, p.20: `dist_D(f, g) = Pr_{x∼D}[f(x) ≠ g(x)] = ∑_x D(x)·[f(x) ≠ g(x)]` for a probability
distribution `D` on `F₂ⁿ`. -/
noncomputable def distD {n : ℕ} (D : PMF (V n)) (f g : BoolFn n) : ℝ :=
  ∑ x : V n, (D x).toReal * (if f x ≠ g x then 1 else 0)

/-- §5, p.20: `dist_D(f, S) = min_{g ∈ S} dist_D(f, g)`, written as the infimum of the finitely many
values `dist_D(f, g)`, `g ∈ S`. For `S = F_s` with `s ≥ 1` the set is nonempty (`Fs_nonempty`),
so this is the attained minimum; on the empty set the value would be `0`. -/
noncomputable def distDToSet {n : ℕ} (D : PMF (V n)) (f : BoolFn n) (S : Set (BoolFn n)) : ℝ :=
  sInf (distD D f '' S)

/-- The constant function `+1` (bit `false`) lies in `F_s` for every `s ≥ 1`, so `F_s ≠ ∅`. -/
theorem Fs_nonempty (n : ℕ) {s : ℕ} (hs : 1 ≤ s) : (Fs n s).Nonempty := by
  refine ⟨fun _ => false, ?_⟩
  have h : toSign (fun _ : V n => false) = fun _ => (1 : ℝ) := by
    funext x; simp [toSign, signOf]
  show realSparsity (toSign (fun _ : V n => false)) ≤ s
  rw [h]
  exact (realSparsity_const_one n).trans hs

/-- §5, pp.20 and 23: a **distribution-free tester** on `F₂ⁿ` with query access to `f` and sample
access to an unknown distribution `D`. It has a finite seed type with a probability law `law`
(its internal randomness), a fixed number `m` of samples, a query map `queries σ x` giving the
ordered list of query points from the seed `σ` and the samples `x = (x₁, …, x_m)` (indexed by `Fin m`), and an
output map `output σ x ans` computed from the seed, the samples and the ordered answers. The
query points may depend on the seed and the samples but on no answer (the form p.23 proves for
Algorithm 4), and the tester never receives `D` itself: `D` enters only through the samples. -/
structure DistFreeTester (n : ℕ) where
  /-- The internal random seed. -/
  Seed : Type
  /-- The seed space is finite. -/
  seedFintype : Fintype Seed
  /-- The law of the seed. -/
  law : PMF Seed
  /-- The number of samples drawn from `D`. -/
  m : ℕ
  /-- The ordered query points, from the seed and the samples. -/
  queries : Seed → (Fin m → V n) → List (V n)
  /-- The output (`1` = accept, `0` = reject), from the seed, the samples and the answers. -/
  output : Seed → (Fin m → V n) → List Bool → ℝ

namespace DistFreeTester

variable {n : ℕ}

/-- One run on input `f` with seed `σ` and samples `x`: the oracle answers the whole query list, and
the output is computed from `σ`, `x` and the answers. -/
def run (T : DistFreeTester n) (f : BoolFn n) (σ : T.Seed) (x : Fin T.m → V n) : ℝ :=
  T.output σ x ((T.queries σ x).map f)

open Classical in
/-- The probability that the tester outputs `b` on `f` when `σ ∼ law` and the `m` samples are
independent samples from `D`, independent of `σ`:
`∑_σ ∑_x law(σ) ∏_i D(x_i) · [run f σ x = b]`. -/
noncomputable def outProb (T : DistFreeTester n) (D : PMF (V n)) (f : BoolFn n) (b : ℝ) : ℝ :=
  letI := T.seedFintype
  ∑ σ : T.Seed, ∑ x : Fin T.m → V n,
    (T.law σ).toReal * (∏ i, (D (x i)).toReal) * (if T.run f σ x = b then 1 else 0)

/-- `Pr[the tester accepts f]` under `D`: the probability of output `1`. -/
noncomputable def acceptProb (T : DistFreeTester n) (D : PMF (V n)) (f : BoolFn n) : ℝ :=
  T.outProb D f 1

/-- `Pr[the tester rejects f]` under `D`: the probability of output `0`. -/
noncomputable def rejectProb (T : DistFreeTester n) (D : PMF (V n)) (f : BoolFn n) : ℝ :=
  T.outProb D f 0

end DistFreeTester

end FourierSparseTesting1656.Uniform.Supplement


