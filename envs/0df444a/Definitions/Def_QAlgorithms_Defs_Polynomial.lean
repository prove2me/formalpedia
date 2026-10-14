-- Prove2me | Definitions.Def_QAlgorithms_Defs_Polynomial
-- name    : QAlgorithms_Defs_Polynomial
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:31:35.705226+00:00
-- url     : https://prove2.me/theorems/966b51a1-3323-476c-8443-21c55e3839b3
-- title:
--   The polynomial method (shared definition layer)
-- statement:
--   The polynomial method (shared definition layer)
--
--   ### QAlgorithms.IsMultilinear
--
--   **Definition.** Let $\sigma$ be any type of variables and $p$ a multivariate polynomial over $\mathbb{R}$ in the variables indexed by $\sigma$. Then $p$ is *multilinear* exactly when, for every variable $i \in \sigma$, the degree of $p$ in $X_i$ is at most $1$.
--
--   Equivalently, no monomial of $p$ contains any variable squared or to a higher power. The zero polynomial qualifies.
--
--   ### QAlgorithms.boolPoint
--
--   **Definition.** For any index type $\sigma$ and Boolean vector $x : \sigma \to \{\text{true},\text{false}\}$, the point $\mathrm{bool}(x) \in \mathbb{R}^\sigma$ is given coordinatewise by
--   $$\mathrm{bool}(x)_i = \begin{cases}1 & \text{if } x_i \text{ is true},\\ 0 & \text{otherwise.}\end{cases}$$
--
--   ### QAlgorithms.weightAverage
--
--   **Definition.** For $n \in \mathbb{N}$, a real polynomial $p$ in variables $X_0, \dots, X_{n-1}$, and $k \in \mathbb{N}$,
--   $$\mathrm{avg}_k(p) = \binom{n}{k}^{-1} \sum_{\substack{x \in \{0,1\}^n \\ |x| = k}} p\big(\mathrm{bool}(x)\big).$$
--
--   Here:
--
--   - $|x|$ is the Hamming weight of $x$, the number of true coordinates;
--   - $\mathrm{bool}(x)$ is the 0/1 real point from `boolPoint`.
--
--   So this is the average of $p$ over the $\binom nk$ Boolean points of weight $k$.
--
--   **Edge case $k > n$.** The sum is empty and $\binom nk = 0$; its inverse is evaluated as $0$. The value is $0$.
--
--   ### QAlgorithms.ValidKutinTriple
--
--   **Definition.** For natural numbers $n, m, a, b$, the property holds exactly when all of the following hold:
--
--   - $m \le n$;
--   - $a \ge 1$;
--   - $b \ge 1$;
--   - $a$ divides $m$;
--   - $b$ divides $n - m$.
--
--   **Edge cases.** The difference $n - m$ is the ordinary difference, because $m \le n$ is required. When $m = 0$ the condition $a \mid m$ holds automatically, and when $m = n$ the condition $b \mid n - m$ holds automatically.
--
--   ### QAlgorithms.kutinInput
--
--   **Definition.** For natural numbers $n, m, a, b$ (no validity hypothesis is assumed), this is a map $g : \{0,\dots,n-1\} \to \{0,\dots,n-1\}$.
--
--   For $p \in \{0,\dots,n-1\}$, set $q = p+1$. Then
--   $$g(p) = \min\big(c(p) \mathbin{\dot-} 1,\; n-1\big),$$
--   where $\dot-$ is truncated subtraction ($r \mathbin{\dot-} s = \max(r-s, 0)$) and
--   $$c(p) = \begin{cases} \big\lfloor (q + a \mathbin{\dot-} 1)/a \big\rfloor & \text{if } q \le m, \\[2pt] n \mathbin{\dot-} \big\lfloor (n - q)/b \big\rfloor & \text{if } q > m. \end{cases}$$
--
--   Division by $0$ is evaluated as $0$.
--
--   **Simplified reading.**
--
--   - For $a \ge 1$, the first branch equals $\lceil q/a \rceil$.
--   - For $a = 0$, the first branch is $\lfloor p/0 \rfloor = 0$, so $g(p) = 0$.
--   - For $b = 0$, the second branch is $n$, so $g(p) = n-1$.
--
--   Thinking of $g(p) + 1$ as a 1-indexed value, a position $q \le m$ is sent to $\lceil q/a \rceil$, and a position $q > m$ is sent to $n - \lfloor (n-q)/b \rfloor$; the result is then shifted down by one and capped at $n-1$.
--
--   ### QAlgorithms.kutinDelta
--
--   **Definition.** For natural numbers $n, m, a, b$ and permutations $\sigma, \tau$ of $\{0,\dots,n-1\}$, this is the real-valued function on pairs $(i,j) \in \{0,\dots,n-1\}^2$ given by
--   $$\Delta_{\sigma,\tau}(i,j) = \begin{cases} 1 & \text{if } \tau\big(g(\sigma(i))\big) = j, \\ 0 & \text{otherwise,}\end{cases}$$
--   where $g$ is the map from `kutinInput` with parameters $n, m, a, b$.
--
--   That is, $\Delta_{\sigma,\tau}$ is the 0/1 indicator array of the graph of the function $i \mapsto \tau(g(\sigma(i)))$: each row $i$ has exactly one $1$. No validity hypothesis on $(n, m, a, b)$ is assumed.
--
--   ### QAlgorithms.kutinAverage
--
--   This definition takes:
--
--   - an implicit natural number $n$;
--   - a real multivariate polynomial $p$ whose variables $x_{ij}$ are indexed by pairs $(i,j) \in \{0,\dots,n-1\}^2$;
--   - three natural numbers $m, a, b$.
--
--   It returns the real number
--
--   $$
--   \mathrm{kutinAverage}(p; m,a,b) \;=\; \frac{1}{(n!)^2}\sum_{\sigma \in S_n}\sum_{\tau \in S_n} p\big(\Delta^{\sigma,\tau}\big),
--   $$
--
--   where $\sigma, \tau$ range over all permutations of $\{0,\dots,n-1\}$. The point $\Delta^{\sigma,\tau} \in \mathbb{R}^{n\times n}$ is the $0/1$ matrix
--
--   $$
--   \Delta^{\sigma,\tau}_{ij} = \begin{cases}1 & \text{if } \tau(g(\sigma(i))) = j,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Here $g = g_{n,m,a,b} : \{0,\dots,n-1\} \to \{0,\dots,n-1\}$ is defined using natural-number arithmetic. Subtraction is truncated at $0$, and division is floor division with $q/0 = 0$. With these conventions,
--
--   $$
--   g(\ell) = \min\!\Big(\,h(\ell) - 1,\; n-1\Big),\qquad
--   h(\ell)=\begin{cases}\big\lfloor (\ell+1+a-1)/a \big\rfloor & \text{if } \ell+1 \le m,\\[2pt] n - \big\lfloor (n-(\ell+1))/b \big\rfloor & \text{otherwise.}\end{cases}
--   $$
--
--   When $a \ge 1$, the first branch is $\lceil (\ell+1)/a\rceil$. The point $\Delta^{\sigma,\tau}$ is therefore the incidence matrix of the function $\tau\circ g\circ\sigma$.
--
--   No hypotheses are imposed on $m, a, b$:
--
--   - If $a = 0$, the first branch gives $h = 0$ and hence $g(\ell) = 0$.
--   - If $b = 0$, the second branch gives $h = n$ and hence $g(\ell) = n-1$.
--   - $m$ may exceed $n$.
--   - For $n = 0$, there is exactly one permutation and $0! = 1$, so the value is $p$ evaluated at the empty point, i.e. its constant term.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Polynomial.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Adversary
/-!
# The polynomial method (shared definition layer)

Polynomials are Mathlib's `MvPolynomial σ ℝ`; a Boolean input `x : σ → Bool` is evaluated as the
0/1 point `boolPoint x`.
-/

namespace QAlgorithms

open scoped Nat

/-- Childs p.106–107 (§21.3–21.4): a multilinear polynomial (degree at most `1` in each variable). -/
def IsMultilinear {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

/-- Childs p.107 (§21.3): a bit string as a 0/1 point, at which polynomials are evaluated
(`MvPolynomial.eval (boolPoint x) p` is the source's `p(x)`). -/
def boolPoint {σ : Type*} (x : σ → Bool) : σ → ℝ :=
  fun i => if x i then 1 else 0

/-- Childs p.107 (Lemma 21.2): `P(k) = E_{|x| = k}[p(x)]`, the uniform average of `p` over the
`n`-bit strings of Hamming weight `k` (there are `C(n, k)` of them, a positive number for
`k ≤ n`; statements quantify `k ≤ n`). -/
noncomputable def weightAverage {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  ((Nat.choose n k : ℝ))⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => hammingWeight x = k),
      MvPolynomial.eval (boolPoint x) p

/-- Childs p.113 (§22.5): the triple `(m, a, b)` is valid: `m ∈ {0, …, n}`, `a ∣ m`, `b ∣ n − m`
(with `a, b ≥ 1`, which the formula `⌈i/a⌉`, `⌊(n − i)/b⌋` presupposes). -/
def ValidKutinTriple (n m a b : ℕ) : Prop :=
  m ≤ n ∧ 1 ≤ a ∧ 1 ≤ b ∧ a ∣ m ∧ b ∣ n - m

/-- Childs p.113 ((22.6)): Kutin's input `x^{m,a,b}`, `x_i = ⌈i/a⌉` for `1 ≤ i ≤ m` and
`x_i = n − ⌊(n − i)/b⌋` for `m < i ≤ n` (positions and values in `{1, …, n}`), stored 0-based:
position `p : Fin n` is `i = p + 1` and value `v` is stored as `v − 1`. The formula is evaluated
in 1-based natural-number arithmetic (`⌈i/a⌉ = (i + a − 1)/a`); for a valid triple the values
lie in `{1, …, n}`, and otherwise they are clamped into range. -/
def kutinInput (n m a b : ℕ) : Fin n → Fin n :=
  fun p =>
    ⟨min ((if (p : ℕ) + 1 ≤ m then ((p : ℕ) + 1 + a - 1) / a else n - (n - ((p : ℕ) + 1)) / b) - 1)
      (n - 1), by have := p.isLt; omega⟩

/-- Childs p.113 ((22.3) and §22.5): the variables `δ^{στ}_{ij} = [x^{στ}_i = j]` of the input
`x^{στ}_i = τ(x^{m,a,b}_{σ(i)})`, for permutations `σ, τ` of `{1, …, n}`. -/
def kutinDelta (n m a b : ℕ) (σ τ : Equiv.Perm (Fin n)) : Fin n × Fin n → ℝ :=
  fun ij => if τ (kutinInput n m a b (σ ij.1)) = ij.2 then 1 else 0

/-- Childs p.113 ((22.7)): `P(m, a, b) = E_{σ,τ}[p({δ^{στ}_{ij}})]`, the average over uniformly
random permutations `σ, τ` of `{1, …, n}`. -/
noncomputable def kutinAverage {n : ℕ} (p : MvPolynomial (Fin n × Fin n) ℝ) (m a b : ℕ) : ℝ :=
  (((n ! : ℕ) : ℝ) ^ 2)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), MvPolynomial.eval (kutinDelta n m a b σ τ) p

/-! ### Sanity tests -/

example : IsMultilinear (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) := by
  intro i
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_X]
  fin_cases i <;> simp

/-- The average of the constant polynomial `1` over a nonempty weight class is `1`. -/
example : weightAverage (1 : MvPolynomial (Fin 2) ℝ) 1 = 1 := by
  simp only [weightAverage, map_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [show (Finset.univ.filter fun x : Fin 2 → Bool => hammingWeight x = 1).card = 2 by decide]
  norm_num

/-- `x^{m,1,1}` is the identity (one-to-one) input, `x^{n,2,b}` pairs up consecutive positions
(two-to-one): at `n = 4`, `x^{4,2,1} = (1, 1, 2, 2)` (stored 0-based). -/
example : kutinInput 4 0 1 1 = id ∧ (List.ofFn (kutinInput 4 4 2 1)).map Fin.val = [0, 0, 1, 1] := by
  refine ⟨funext fun p => ?_, by decide⟩
  fin_cases p <;> decide

end QAlgorithms


