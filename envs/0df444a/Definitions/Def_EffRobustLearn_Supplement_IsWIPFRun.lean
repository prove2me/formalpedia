-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_IsWIPFRun
-- name    : EffRobustLearn_Supplement_IsWIPFRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:17:13.376515+00:00
-- url     : https://prove2.me/theorems/f5fa5e77-8bc3-47c9-b307-d73618acd3be
-- title:
--   Algorithm 2: weighted iterative polynomial filtering (WIPF), as a run relation with a work count
-- statement:
--   Algorithm 2, WIPF$(\bar S_{\mathrm{inp},t},S_{\mathrm{ref}},m,\varepsilon,|\bar S_{\mathrm{inp}}|)$ with degree $\ell$ and constant $A$. Let $n=|\bar S_{\mathrm{inp}}|$ be the normalization, $\bar S_{\mathrm{inp},t}\subseteq\bar S_{\mathrm{inp}}$ the current sub-sample and $m:\mathbb R^d\to\mathbb R$ a function. Set
--   $$
--   R=2,\quad \beta=2(2A)^{4\ell},\quad \gamma=\frac{\varepsilon}{64},\quad B=16(d+1)^\ell\sqrt{\beta/\varepsilon},\quad \Delta=\frac{\varepsilon}{32B},
--   $$
--   $$
--   \mathcal P=\Big\{p:\deg p\le2\ell,\ \tfrac1{|S_{\mathrm{ref}}|}\textstyle\sum_{x\in S_{\mathrm{ref}}}|p(x)|\le\gamma,\ \tfrac1{|S_{\mathrm{ref}}|}\sum_{x\in S_{\mathrm{ref}}}p(x)^2\le\beta\Big\},
--   \qquad v(x,y)=\frac{2+|m(x)|-y\,m(x)}{8(1+|m(x)|)} .
--   $$
--   The run first keeps the examples $(x,y)\in\bar S_{\mathrm{inp},t}$ with $|p(x)|\le B$ for every $p\in\mathcal P$. Then, for $i=0,\dots,|\bar S_{\mathrm{inp},t}|$, it picks any maximizer $p^\star$ of $\sum_{(x,y)\in\bar S_{\mathrm{filt}}}v(x,y)p(x)$ over $\mathcal P$ and sets $\lambda^\star=\frac1n\sum v\,p^\star$. If $\lambda^\star\le\varepsilon/64$ it returns $\bar S_{\mathrm{filt}}$. Otherwise it takes the smallest $\tau^\star\ge0$ with
--   $$
--   \frac{|\{x\in S_{\mathrm{filt}}:|p^\star(x)|>\tau^\star\}|}{n}\ \ge\ R\,\frac{|\{x\in S_{\mathrm{ref}}:|p^\star(x)|>\tau^\star\}|}{|S_{\mathrm{ref}}|}+\Delta
--   $$
--   and deletes $\{|p^\star|>\tau^\star\}$ from $\bar S_{\mathrm{filt}}$.
--
--   A run records the returned sub-sample and the number $k\le|\bar S_{\mathrm{inp},t}|$ of deletions. Its work is $(s+k+1)(N'+s+m+1)^4$ for an input of $s$ examples, $m$ reference points and $N'$ monomials of degree at most $2\ell$.
--
--   **Formalization Note** Samples are indexed families and sub-samples are sets of indices into $\bar S_{\mathrm{inp}}$. The run is a relation: any maximizer may be chosen at every iteration, and every theorem holds for every such choice. The cost model charges each test $\sup_{p\in\mathcal P}|p(x)|\le B$ and each loop iteration (linear maximization over $\mathcal P$, threshold search, deletion) the fixed polynomial $(N'+s+m+1)^4$ of its instance size. The source reduces these steps to convex programs of polynomial size; another fixed polynomial would change only the constants of the runtime bounds.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 2, p.20 (PDF p.21); runtime in the proof of Theorem D.1, p.45 (PDF p.46)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_Supplement_psi

namespace EffRobustLearn

namespace Supplement

/-! Algorithm 2 (weighted iterative polynomial filtering, WIPF) of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.20 (PDF p.21).
Samples are indexed families: `Sinp : Fin n → ℝ^d × Bool` is the corrupted sample `S̄inp` (labels read as `±1`
by `pm`), its sub-samples are sets of indices `Finset (Fin n)`, and `Sref : Fin m → ℝ^d`. The normalization
`|S̄inp|` is `n`. -/

/-- `β := 2(2A)^{4ℓ}` (Algorithm 2, line 4). -/
noncomputable def wipfBeta (A : ℝ) (ℓ : ℕ) : ℝ := 2 * (2 * A) ^ (4 * ℓ)

/-- `B := 16(d + 1)^ℓ √(β/ε)` (line 4). -/
noncomputable def wipfB (d ℓ : ℕ) (A ε : ℝ) : ℝ :=
  16 * ((d : ℝ) + 1) ^ ℓ * Real.sqrt (wipfBeta A ℓ / ε)

/-- `Δ := ε/(32B)` (line 4). `R := 2` and `γ := ε/64` are written out where they are used. -/
noncomputable def wipfDelta (d ℓ : ℕ) (A ε : ℝ) : ℝ := ε / (32 * wipfB d ℓ A ε)

/-- The filtering family `P := {p : deg p ≤ 2ℓ, (1/|Sref|)∑_{Sref}|p| ≤ γ, (1/|Sref|)∑_{Sref} p² ≤ β}`, line 5,
with `γ = ε/64`. -/
noncomputable def filterFamily {d m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sref : Fin m → Fin d → ℝ) :
    Set (MvPolynomial (Fin d) ℝ) :=
  {p | p.totalDegree ≤ 2 * ℓ ∧
    (1 / (m : ℝ)) * ∑ j, |MvPolynomial.eval (Sref j) p| ≤ ε / 64 ∧
    (1 / (m : ℝ)) * ∑ j, (MvPolynomial.eval (Sref j) p) ^ 2 ≤ wipfBeta A ℓ}

/-- The weight `v(x, y) = (2 + |m(x)| − y m(x)) / (8(1 + |m(x)|))` of line 8 (also Theorem D.1). -/
noncomputable def vWeight {d : ℕ} (mf : (Fin d → ℝ) → ℝ) (z : (Fin d → ℝ) × Bool) : ℝ :=
  (2 + |mf z.1| - pm z.2 * mf z.1) / (8 * (1 + |mf z.1|))

/-- The objective `∑_{(x,y)∈S̄filt} v(x, y) p(x)` of line 8. -/
noncomputable def filtObj {d n : ℕ} (Sinp : Fin n → (Fin d → ℝ) × Bool) (mf : (Fin d → ℝ) → ℝ)
    (F : Finset (Fin n)) (p : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ i ∈ F, vWeight mf (Sinp i) * MvPolynomial.eval (Sinp i).1 p

open Classical in
/-- Line 6: `S̄filt := {(x, y) ∈ S̄inp,t : |p(x)| ≤ B for every p ∈ P}`. -/
noncomputable def initFilt {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun i => ∀ p ∈ filterFamily ℓ A ε Sref, |MvPolynomial.eval (Sinp i).1 p| ≤ wipfB d ℓ A ε

open Classical in
/-- The deletion condition of line 10 at threshold `τ`:
`|{x ∈ Sfilt : |p(x)| > τ}| / |S̄inp| ≥ R |{x ∈ Sref : |p(x)| > τ}| / |Sref| + Δ`, with `R = 2`. -/
def tailCond {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (F : Finset (Fin n)) (p : MvPolynomial (Fin d) ℝ) (τ : ℝ) : Prop :=
  2 * (((Finset.univ.filter fun j => τ < |MvPolynomial.eval (Sref j) p|).card : ℕ) : ℝ) / (m : ℝ) +
      wipfDelta d ℓ A ε ≤
    (((F.filter fun i => τ < |MvPolynomial.eval (Sinp i).1 p|).card : ℕ) : ℝ) / (n : ℝ)

/-- `p⋆` is a maximizer of line 8: `p⋆ ∈ P` and `∑ v p ≤ ∑ v p⋆` for every `p ∈ P` (any maximizer may be used). -/
def IsFiltMaximizer {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (mf : (Fin d → ℝ) → ℝ) (F : Finset (Fin n))
    (p : MvPolynomial (Fin d) ℝ) : Prop :=
  p ∈ filterFamily ℓ A ε Sref ∧ ∀ p' ∈ filterFamily ℓ A ε Sref, filtObj Sinp mf F p' ≤ filtObj Sinp mf F p

open Classical in
/-- One rejected iteration of the loop (lines 8, 10, 11): for a maximizer `p⋆` with
`λ⋆ = (1/|S̄inp|) ∑ v p⋆ > ε/64`, `τ⋆` is the smallest `τ ≥ 0` satisfying the deletion condition, and the
new sample is `F' = F \ {|p⋆| > τ⋆}`. -/
def IsRejectStep {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (mf : (Fin d → ℝ) → ℝ) (F F' : Finset (Fin n)) : Prop :=
  ∃ p, IsFiltMaximizer ℓ A ε Sinp Sref mf F p ∧ ε / 64 < filtObj Sinp mf F p / (n : ℝ) ∧
    ∃ τ, IsLeast {τ : ℝ | 0 ≤ τ ∧ tailCond ℓ A ε Sinp Sref F p τ} τ ∧
      F' = F.filter fun i => ¬ τ < |MvPolynomial.eval (Sinp i).1 p|

/-- The returning iteration (lines 8, 9): for a maximizer `p⋆`, `λ⋆ ≤ ε/64`. -/
def IsReturnStep {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (mf : (Fin d → ℝ) → ℝ) (F : Finset (Fin n)) : Prop :=
  ∃ p, IsFiltMaximizer ℓ A ε Sinp Sref mf F p ∧ filtObj Sinp mf F p / (n : ℝ) ≤ ε / 64

/-- A run of Algorithm 2, WIPF(`S̄inp,t`, `Sref`, `m`, `ε`, `|S̄inp|`), with degree `ℓ` and constant `A`, on the
input sub-sample `S` (the indices of `S̄inp,t` in `S̄inp`): it returns `out` after `k` rejected iterations.

**Formalization Note.**
* The run is a relation, not a function: any maximizer `p⋆` of line 8 may be chosen at each iteration, and every
  theorem about runs holds for every such choice. Line 6 is applied on every call.
* The loop `i = 0, …, |S̄inp,t|` has `|S| + 1` iterations, so a run that returns has `k ≤ |S|` rejections and
  returns at iteration `k`. A run that would leave the loop without returning is not a run.
* `d`, `A` and `ℓ` are inputs as in lines 2 and 4. -/
def IsWIPFRun {d n m : ℕ} (ℓ : ℕ) (A ε : ℝ) (Sinp : Fin n → (Fin d → ℝ) × Bool)
    (Sref : Fin m → Fin d → ℝ) (mf : (Fin d → ℝ) → ℝ) (S out : Finset (Fin n)) (k : ℕ) : Prop :=
  k ≤ S.card ∧ ∃ F : ℕ → Finset (Fin n), F 0 = initFilt ℓ A ε Sinp Sref S ∧
    (∀ i < k, IsRejectStep ℓ A ε Sinp Sref mf (F i) (F (i + 1))) ∧
    IsReturnStep ℓ A ε Sinp Sref mf (F k) ∧ out = F k

/-- The work charged to a run of Algorithm 2 on an input of `s` examples with `k` rejections, reference size
`m`, and `N' = Nf` monomials of degree `≤ 2ℓ` (the coefficient dimension of `P`).

**Formalization Note (cost model).** The paper reduces lines 6 and 8 to "convex optimization problems of
polynomial size" (proof of Theorem D.1, p.45). Each primitive step, namely one test `sup_{p∈P}|p(x)| ≤ B` of line 6, or one
loop iteration (the linear maximization over `P`, `λ⋆`, the threshold search over sorted values, the deletion),
is charged the fixed polynomial `(N' + s + m + 1)^4` of its instance size. Real arithmetic and comparisons have
unit cost. Line 6 makes `s` tests and the loop makes `k + 1` iterations. The exponent `4` is fixed here, not by
any theorem; another fixed polynomial changes only the constants of the runtime bounds. -/
def wipfWork (Nf s m k : ℕ) : ℕ := (s + k + 1) * (Nf + s + m + 1) ^ 4

end Supplement

end EffRobustLearn


