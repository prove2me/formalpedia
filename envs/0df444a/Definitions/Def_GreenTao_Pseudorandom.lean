-- Prove2me | Definitions.Def_GreenTao_Pseudorandom
-- name    : GreenTao_Pseudorandom
-- status  : Definition
-- author  : @davidnet
-- created : 2026-09-06T01:23:54.172716+00:00
-- url     : https://prove2.me/theorems/b4b72aeb-5812-4fcc-9552-93d3f82a7e1e
-- title:
--   Green–Tao pseudorandom measures on cyclic groups
-- statement:
--   Let $M_n$ be positive integers and write $G_n=\mathbb Z/M_n\mathbb Z$. For a real function on a finite set, write $\mathbb E$ for its uniform average. This interface defines
--
--   $$T_k(f)=\mathbb E_{x,r\in G_n}\prod_{j=0}^{k-1}f(x+jr),\qquad D_k(f)=\frac1{M_n}\mathbb E_{x\in G_n}f(x)^k.$$
--
--   The linear forms condition with parameters $(m_0,t_0,L_0)$ requires the average of a product of weights along at most $m_0$ nonzero, pairwise nonproportional rational affine forms in at most $t_0$ variables to tend to one. Numerators and denominators of the coefficients are bounded by $L_0$. Convergence is uniform over the translations: the limit must hold for every sequence of translations. Rational coefficients are interpreted modulo $M_n$ by inverting denominators; applications use growing prime moduli, so these inverses exist eventually.
--
--   The $m_0$-correlation condition requires a nonnegative weight $\tau_m$ for each $2\le m\le m_0$, with bounded moments of every real order $q\ge1$, such that eventually, uniformly over all shifts,
--
--   $$\mathbb E_x\prod_{i=1}^m\nu_n(x+h_i)\le\sum_{i<j}\tau_{m,n}(h_i-h_j).$$
--
--   A family is $k$-pseudorandom when it is nonnegative, its mean tends to one, and it satisfies the linear forms condition with parameters $(k2^{k-1},3k-4,k)$ and the $2^{k-1}$-correlation condition. These are the interfaces needed to state relative Szemerédi and the analytic majorant construction independently.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §2 equation (2.4), §3 Definitions 3.1–3.3 and equations (3.1), (3.5), (3.6), (3.9); diagonal contribution as in §9, proof of Theorem 1.1 assuming Proposition 9.1.

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Tendsto

open scoped BigOperators Topology
open Filter

namespace GreenTao

/-- Uniform expectation on a finite type. -/
noncomputable def avg {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

/-- A family of functions on cyclic groups of positive, varying orders. -/
abbrev Family (M : ℕ → ℕ+) := ∀ n, ZMod (M n : ℕ) → ℝ

/-- The normalized count of ordered progressions, including zero difference. -/
noncomputable def apAvg (k : ℕ) {m : ℕ+} (f : ZMod (m : ℕ) → ℝ) : ℝ :=
  avg fun x => avg fun r => ∏ j : Fin k, f (x + (j.val : ZMod (m : ℕ)) * r)

/-- The zero-difference contribution to the normalized progression count. -/
noncomputable def diagonalAvg (k : ℕ) {m : ℕ+} (f : ZMod (m : ℕ) → ℝ) : ℝ :=
  avg (fun x => f x ^ k) / (m : ℝ)

/-- Interpret a rational coefficient in a cyclic group by inverting its denominator.
The denominators are invertible eventually for the prime moduli used below. -/
noncomputable def ratCoeff (m : ℕ+) (q : ℚ) : ZMod (m : ℕ) :=
  (q.num : ZMod (m : ℕ)) * (q.den : ZMod (m : ℕ))⁻¹

/-- Definition 3.1 of Green--Tao. Quantification over every sequence of translations
expresses the required uniformity in the constant terms of the linear forms. -/
def LinearFormsCondition (M : ℕ → ℕ+) (ν : Family M) (m₀ t₀ L₀ : ℕ) : Prop :=
  ∀ m t : ℕ, m ≤ m₀ → t ≤ t₀ →
  ∀ L : Fin m → Fin t → ℚ,
    (∀ i j, (L i j).num.natAbs ≤ L₀ ∧ (L i j).den ≤ L₀) →
    (∀ i, ∃ j, L i j ≠ 0) →
    (∀ i i', i ≠ i' → ¬ ∃ c : ℚ, ∀ j, L i j = c * L i' j) →
    ∀ b : ∀ n, Fin m → ZMod (M n : ℕ),
      Tendsto (fun n => avg fun x : Fin t → ZMod (M n : ℕ) =>
        ∏ i : Fin m, ν n ((∑ j : Fin t, ratCoeff (M n) (L i j) * x j) + b n i))
        atTop (𝓝 1)

/-- Definition 3.2 of Green--Tao, with all real moments and bounds uniform in shifts. -/
def CorrelationCondition (M : ℕ → ℕ+) (ν : Family M) (m₀ : ℕ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → m ≤ m₀ →
    ∃ τ : Family M,
      (∀ n x, 0 ≤ τ n x) ∧
      (∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ᶠ n in atTop,
        avg (fun x => (τ n x) ^ q) ≤ C) ∧
      (∀ᶠ n in atTop, ∀ h : Fin m → ZMod (M n : ℕ),
        avg (fun x => ∏ i : Fin m, ν n (x + h i)) ≤
          ∑ i : Fin m, ∑ j : Fin m, if i < j then τ n (h i - h j) else 0)

/-- Asymptotically normalized, nonnegative k-pseudorandom measures (Definition 3.3). -/
def Pseudorandom (k : ℕ) (M : ℕ → ℕ+) (ν : Family M) : Prop :=
  (∀ n x, 0 ≤ ν n x) ∧
  Tendsto (fun n => avg (ν n)) atTop (𝓝 1) ∧
  LinearFormsCondition M ν (k * 2 ^ (k - 1)) (3 * k - 4) k ∧
  CorrelationCondition M ν (2 ^ (k - 1))

end GreenTao


