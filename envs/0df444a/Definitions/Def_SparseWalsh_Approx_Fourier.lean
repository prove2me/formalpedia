-- Prove2me | Definitions.Def_SparseWalsh_Approx_Fourier
-- name    : SparseWalsh_Approx_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:01:45.600408+00:00
-- url     : https://prove2.me/theorems/77d5dbbc-3491-442a-8af4-d3cee182d362
-- title:
--   The Boolean cube, Walsh characters, Fourier coefficients, sparsity, degree, the best s-term error, bucket tables, the median estimator and top-j selection
-- statement:
--   Let $d\ge 0$ and write $\mathbb F_2^d$ for the Boolean cube; binary sums, inner products and matrix products are taken modulo $2$. For $a,x\in\mathbb F_2^d$ the **Walsh character** is $\chi_a(x)=(-1)^{\langle a,x\rangle}$ with $\langle a,x\rangle=\sum_i a_ix_i\in\mathbb F_2$. Every $f:\mathbb F_2^d\to\mathbb R$ has the **Fourier coefficients**
--   $$\hat f(a)=\mathbb E_X[f(X)\chi_a(X)]=2^{-d}\sum_{x\in\mathbb F_2^d}f(x)\chi_a(x),$$
--   with $X$ uniform, and $\|f\|_2^2=\mathbb E_X[f(X)^2]$. For a real coefficient vector $c=(c(a))_a$, $\|c\|_2^2=\sum_a c(a)^2$.
--
--   - **Sparsity and degree** (Definition 2.1): $\operatorname{supp}(\hat f)=\{a:\hat f(a)\ne0\}$; $f$ is $s$-Fourier-sparse if $|\operatorname{supp}(\hat f)|\le s$. The Hamming weight is $|a|=\#\{i:a_i=1\}$, and $f$ has Fourier degree at most $k$ if $|a|\le k$ whenever $\hat f(a)\ne0$.
--   - **Best $s$-term error** (Eq. (2)): $\mathrm{OPT}_s(f)=\min_{|\operatorname{supp}(\hat g)|\le s}\|f-g\|_2^2$ over all real $g$. A best $s$-term approximation is a $g$ attaining it; $T$ is the support of an optimal $s$-term approximation if $T=\operatorname{supp}(\hat g)$ for such a $g$, and then $\tau^2=\sum_{a\notin T}\hat f(a)^2$. The **degree promise** with bound $k$ says that some best $s$-term approximation has degree at most $k$.
--   - A **Fourier polynomial** is listed by (frequency, coefficient) pairs $(a_i,\lambda_i)$ and equals $\sum_i\lambda_i\chi_{a_i}$.
--   - **Bucket tables** (Eq. (3)): for $B\in\mathbb F_2^{m\times d}$, $y\in\mathbb F_2^d$, $v\in\mathbb F_2^m$,
--   $$H^f_{B,y}(v)=2^{-m}\sum_{z\in\mathbb F_2^m}f(y+B^\top z)(-1)^{\langle v,z\rangle},\qquad H^c_{B,y}(v)=\sum_{a:Ba=v}c(a)\chi_a(y).$$
--   - **Median and estimator** (p. 21): the median of $q$ reals is the middle value for odd $q$ and the average of the two middle values for even $q$. For a list $E$ of hash–shift pairs $(C,y)$, $\mathrm{Est}_E(c,a)=\operatorname{median}_{(C,y)\in E}\chi_a(y)H^c_{C,y}(Ca)$.
--   - **Selection** (Lemma D.4): $A_j$ contains the $j$ elements of a candidate set $W$ with the largest estimated magnitudes $|\tilde f(a)|$, ties broken by a fixed order, or all of $W$ if $|W|<j$.
--
--   **Formalization Note.** $\mathbb F_2^d$ is `Fin d → ZMod 2` and binary matrices are `Matrix (Fin m) (Fin d) (ZMod 2)`. $\mathrm{OPT}_s(f)$ is written as the infimum of the attained values; the set is nonempty ($g=0$) and bounded below by $0$, and the minimum is attained (p. 11). The median of an empty list is $0$; it is never used. A fixed tie-breaking order is an injective key into $\mathbb N$, where the smaller key wins. Algorithm 3 uses the binary number $\sum_ia_i2^i$ as its key.
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), pp. 1-2 (characters, Fourier expansion); p. 11 (inner product, Definition 2.1, weight, degree, best s-term truncation); p. 12 (Definition 2.3, Eq. (2)); p. 13 (Eq. (3)); p. 19 (H^c, T, τ); p. 21 (Est_E, median); p. 43 (Lemma D.4's A_j)

import Mathlib

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-!
# The Boolean cube, Walsh characters, Fourier coefficients, sparsity, degree, the best s-term
error, bucket tables, the even-count median, the estimator `Est_E`, and top-`j` selection

Attias, Bshouty, Medvedev, Srebro, *Efficient Non-Adaptive Sparse Fourier Learning on the Boolean
Cube and Finite Abelian Groups*, STOC 2027 submission (manuscript sha256 4cbf9075…), pp. 1–2
(characters, Fourier expansion), p. 11 (inner product, Definition 2.1, Hamming weight, degree,
best s-term truncation), p. 12 (Definition 2.3, Eq. (2), output format), p. 13 (Eq. (3)),
p. 19 (`H^c_{B,y}`, `T`, `τ`), p. 21 (`Est_E`, median convention), p. 43 (Lemma D.4's selection).

* `Cube d = Fin d → ZMod 2` is `F_2^d`; a binary `m × d` matrix is `Matrix (Fin m) (Fin d) (ZMod 2)`,
  `B a` is `B *ᵥ a`, `Bᵀ z` is `Bᵀ *ᵥ z`; all binary arithmetic is in `ZMod 2`.
* `chi a x = (−1)^{⟨a,x⟩}` with `⟨a,x⟩ = Σ_i a_i x_i ∈ F_2`; it is defined for every length, so it
  also gives `(−1)^{⟨v,z⟩}` on `F_2^m`.
* `hat f a = 2^{−d} Σ_x f(x) χ_a(x)` (the uniform expectation `E_X[f(X)χ_a(X)]`); functions and
  coefficients are real.
* `normSq f = 2^{−d} Σ_x f(x)²` is `‖f‖₂² = E_X[f(X)²]`; `coefNormSq c = Σ_a c(a)²` is the
  Euclidean norm squared of a coefficient vector (equal to `normSq` of `Σ_a c(a)χ_a` by Parseval).
* `bestErr s f` is `min_{|supp ĝ| ≤ s} ‖f − g‖₂²` over **all** real `g`, written as the infimum
  of the (nonempty, bounded below by `0`) set of attained values; the minimum is attained (p. 11).
* `bucket f B y v` is Eq. (3); `coefBucket c B y v = Σ_{a : Ba = v} c(a)χ_a(y)` is `H^c_{B,y}(v)`.
* `median` of `q ≥ 1` reals: the middle value for odd `q`, the average of the two middle values
  for even `q` (p. 21); `0` for `q = 0` (never used: every estimation list is nonempty).
* `selectTop key j W ft` is Lemma D.4's `A_j`: the `j` elements of `W` of largest `|ft|`, ties
  broken by the fixed order given by an injective `key` (smaller key wins), or all of `W` if
  `|W| < j`.
-/

/-- The Boolean cube `F_2^d`. -/
abbrev Cube (d : ℕ) : Type := Fin d → ZMod 2

/-- The `F_2` inner product `⟨a, x⟩ = Σ_i a_i x_i`. -/
def dot {d : ℕ} (a x : Cube d) : ZMod 2 := ∑ i, a i * x i

/-- The Walsh character `χ_a(x) = (−1)^{⟨a,x⟩}`. -/
def chi {d : ℕ} (a x : Cube d) : ℝ := if dot a x = 0 then 1 else -1

/-- The Fourier coefficient `f̂(a) = E_X[f(X)χ_a(X)] = 2^{−d} Σ_x f(x)χ_a(x)`. -/
noncomputable def hat {d : ℕ} (f : Cube d → ℝ) (a : Cube d) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ x, f x * chi a x

/-- `‖f‖₂² = E_X[f(X)²]`, `X` uniform on `F_2^d`. -/
noncomputable def normSq {d : ℕ} (f : Cube d → ℝ) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹ * ∑ x, f x ^ 2

/-- The Euclidean norm squared `‖c‖₂² = Σ_a c(a)²` of a coefficient vector. -/
noncomputable def coefNormSq {d : ℕ} (c : Cube d → ℝ) : ℝ := ∑ a, c a ^ 2

/-- The Fourier support `supp(f̂) = {a : f̂(a) ≠ 0}` (Definition 2.1). -/
noncomputable def fourierSupport {d : ℕ} (f : Cube d → ℝ) : Finset (Cube d) := by
  classical exact Finset.univ.filter fun a => hat f a ≠ 0

/-- The Hamming weight `|a| = #{i : a_i = 1}`. -/
def weight {d : ℕ} (a : Cube d) : ℕ := (Finset.univ.filter fun i => a i = 1).card

/-- `f` has Fourier degree at most `k`: `|a| ≤ k` whenever `f̂(a) ≠ 0` (p. 11). -/
def HasDegreeAtMost {d : ℕ} (f : Cube d → ℝ) (k : ℕ) : Prop :=
  ∀ a, hat f a ≠ 0 → weight a ≤ k

/-- The best `s`-term error `min_{|supp(ĝ)| ≤ s} ‖f − g‖₂²` over all real `g : F_2^d → ℝ`
(Eq. (2)); the set is nonempty (`g = 0`) and bounded below by `0`. -/
noncomputable def bestErr {d : ℕ} (s : ℕ) (f : Cube d → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ g : Cube d → ℝ, (fourierSupport g).card ≤ s ∧ e = normSq (f - g)}

/-- `g` is a best `s`-term approximation of `f`: `|supp ĝ| ≤ s` and `‖f − g‖₂² = bestErr s f`. -/
def IsBestApprox {d : ℕ} (s : ℕ) (f g : Cube d → ℝ) : Prop :=
  (fourierSupport g).card ≤ s ∧ normSq (f - g) = bestErr s f

/-- The degree promise for approximation (p. 12): some best (unrestricted) `s`-term approximation
of `f` has Fourier degree at most `k`. -/
def DegreePromise {d : ℕ} (s k : ℕ) (f : Cube d → ℝ) : Prop :=
  ∃ g, IsBestApprox s f g ∧ HasDegreeAtMost g k

/-- `T` is the support of an optimal `s`-term Fourier approximation of `f` (p. 19). -/
def IsOptimalSupport {d : ℕ} (s : ℕ) (f : Cube d → ℝ) (T : Finset (Cube d)) : Prop :=
  ∃ g, IsBestApprox s f g ∧ fourierSupport g = T

/-- `τ² = Σ_{a ∉ T} f̂(a)²` (p. 19). -/
noncomputable def tailSq {d : ℕ} (f : Cube d → ℝ) (T : Finset (Cube d)) : ℝ :=
  ∑ a ∈ Tᶜ, hat f a ^ 2

/-- The Fourier polynomial `x ↦ Σ_{(a, λ) ∈ l} λ χ_a(x)` listed by (frequency, coefficient)
pairs. -/
noncomputable def poly {d : ℕ} (l : List (Cube d × ℝ)) : Cube d → ℝ :=
  fun x => (l.map fun p => p.2 * chi p.1 x).sum

/-- The Fourier polynomial `Σ_{a ∈ A} c(a) χ_a` of a coefficient vector on a finite set. -/
noncomputable def polyOn {d : ℕ} (A : Finset (Cube d)) (c : Cube d → ℝ) : Cube d → ℝ :=
  fun x => ∑ a ∈ A, c a * chi a x

/-- The bucket table of Eq. (3):
`H^f_{B,y}(v) = 2^{−m} Σ_{z ∈ F_2^m} f(y + Bᵀz)(−1)^{⟨v,z⟩}`. -/
noncomputable def bucket {d m : ℕ} (f : Cube d → ℝ) (B : Matrix (Fin m) (Fin d) (ZMod 2))
    (y : Cube d) (v : Cube m) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∑ z : Cube m, f (y + Bᵀ *ᵥ z) * chi v z

/-- The coefficient bucket `H^c_{B,y}(v) = Σ_{a : Ba = v} c(a)χ_a(y)` (p. 19). -/
noncomputable def coefBucket {d m : ℕ} (c : Cube d → ℝ) (B : Matrix (Fin m) (Fin d) (ZMod 2))
    (y : Cube d) (v : Cube m) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : Cube d => B *ᵥ a = v), c a * chi a y

/-- The median of `q` reals: the middle value for odd `q`, the average of the two middle values
for even `q ≥ 2` (p. 21); `0` when `q = 0`. -/
noncomputable def median {q : ℕ} (x : Fin q → ℝ) : ℝ :=
  let l := (List.ofFn x).insertionSort (· ≤ ·)
  if q % 2 = 1 then l.getD (q / 2) 0 else (l.getD (q / 2 - 1) 0 + l.getD (q / 2) 0) / 2

/-- `Est_E(c, a) = median_{(C,y) ∈ E} χ_a(y) H^c_{C,y}(Ca)` (p. 21), for a list `E` of `q`
hash–shift pairs with `p`-row hashes (tables with `2^p` buckets). -/
noncomputable def est {d p q : ℕ} (E : Fin q → Matrix (Fin p) (Fin d) (ZMod 2) × Cube d)
    (c : Cube d → ℝ) (a : Cube d) : ℝ :=
  median fun i => chi a (E i).2 * coefBucket c (E i).1 (E i).2 ((E i).1 *ᵥ a)

/-- Lemma D.4's `A_j`: the elements of `W` beaten (larger `|ft|`, or equal `|ft|` and smaller
key) by fewer than `j` elements of `W`. For an injective `key` this is the `j` largest estimated
magnitudes with fixed tie-breaking, or all of `W` when `|W| < j`. -/
noncomputable def selectTop {d : ℕ} (key : Cube d → ℕ) (j : ℕ) (W : Finset (Cube d))
    (ft : Cube d → ℝ) : Finset (Cube d) := by
  classical exact W.filter fun a =>
    (W.filter fun b => |ft a| < |ft b| ∨ (|ft b| = |ft a| ∧ key b < key a)).card < j

/-- The fixed frequency order used by Algorithm 3: the binary number `Σ_i a_i 2^i`. -/
def freqKey {d : ℕ} (a : Cube d) : ℕ := ∑ i : Fin d, (a i).val * 2 ^ (i : ℕ)

end SparseWalsh.Approx


