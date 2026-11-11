-- Prove2me | Definitions.Def_TensorBeyond_Main_Model
-- name    : TensorBeyond_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:13:35.829558+00:00
-- url     : https://prove2.me/theorems/ab301312-c75d-44b2-931e-4a49c73597f6
-- title:
--   Random Rademacher tensors $T=\sum_i v_i^{\otimes k}$, both inner products, the input/output encoding on the randomized real RAM, and the success event
-- statement:
--   A **sample** is a list of $m$ sign vectors $v_1,\dots,v_m\in\{\pm1\}^n$ (indices are $0$-based in Lean). The model of the paper draws them independently and uniformly, i.e. the sample is uniform on the finite set $(\{\pm1\}^n)^m$; $\mathrm{probV}(E)$ is the probability of an event $E$ of the sample under this law.
--
--   The **normalized inner product** of $x,y\in\mathbb R^n$ is $\langle x,y\rangle=\frac1n\,x^\top y$ (p. 2), so $\langle v,v\rangle=1$ for $v\in\{\pm1\}^n$; the **dot product** $x^\top y=\sum_u x_uy_u$ is the unnormalized convention that Section 7 and Appendix A use silently.
--
--   The order-$k$ tensor $T=\sum_{i=1}^m v_i^{\otimes k}$ has entries $T_{u}=\sum_i\prod_{a=1}^k v_i[u_a]$ for $u\in[n]^k$, and
--   $$\langle T,x^{\otimes k}\rangle=\frac1{n^k}\sum_{u\in[n]^k}T_u\,x_{u_1}\cdots x_{u_k}=\sum_{i=1}^m\langle v_i,x\rangle^k .$$
--   The slack of (6.1) is $\xi=m\cdot n(3n-2)/n^4-\delta$, with $\delta$ standing for the $\tilde o(1)$ term.
--
--   **Algorithms** are programs of the published randomized real RAM `KXorTPCA_Reduction_Machine` (real arithmetic, indirect addressing, a uniform and a Gaussian random tape, $\exp,\log,\sqrt{\cdot}$). The **input** of an instance is the memory image with $n$, $m$, $\ell$ in cells $0,1,2$ and the $n^k$ entries of $T$ in lexicographic order of $[n]^k$ from cell $3$; all other cells are $0$. The $j$-th **output vector** $\hat v_j\in\mathbb R^n$ is read from the final memory cells $3+n^k+jn+u$, $u<n$.
--
--   The **success event** with accuracy $\delta$ is: every output satisfies $\langle\hat v_j,\hat v_j\rangle=1$, and there is a permutation $\pi$ of $[m]$ with $\langle\hat v_{\pi(i)},v_i\rangle\ge1-\delta$ for all $i$ ($|\langle\hat v_{\pi(i)},v_i\rangle|\ge1-\delta$ when $k$ is even). The **failure probability** of an event $F(v,\omega)$ of the sample and the tapes is $|\{\pm1\}^{nm}|^{-1}\sum_v\Pr_\omega[F(v,\omega)]$, with the tape law of the machine (outer measure, so no measurability is needed).
--
--   **Formalization Note.** Signs are `ℤˣ`; `Fin n`, `Fin m` index coordinates and components. `ip` is $\langle\cdot,\cdot\rangle$, `dot` is $x^\top y$, `pairing k v x` is $\langle T,x^{\otimes k}\rangle$, `encode`, `outVecs`, `Recovers`, `failProb` are the encoding, the output, the success event and the failure probability.
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 2 (PDF 4), Theorem 1.1 and footnote 1; p. 25 (PDF 27), §4.1; p. 29 (PDF 31), §5.1; p. 31 (PDF 33), Eq. (6.1)

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Machine

set_option autoImplicit false

open MeasureTheory

/-!
# The random Rademacher tensor model, its encoding on the randomized real RAM, and success

Jha, Mazzali, Xu, *Tensor Decomposition Beyond the Spectral Threshold*, STOC 2027 submission
(held manuscript, sha256 988d801c…): §1 (p. 2, Theorem 1.1 and footnote 1, the normalized inner
product), §4.1 (p. 25, uniform sampling, coordinate products), §5.1 (p. 29, the model and the
algorithm's input), (6.1) (p. 31).

Conventions.
* A sample `v : Sample n m` is `m` sign vectors `v_i ∈ {±1}^n`, as `Fin m → Fin n → ℤˣ`
  (index base 0). `vec v i : Fin n → ℝ` is `v_i` as a real vector. `probV n m E` is the
  probability of the event `E` when the `v_i` are i.i.d. uniform on `{±1}^n`, i.e. the sample is
  uniform on the finite set `Sample n m`.
* `ip x y = (1/n) ∑_u x_u y_u` is the paper's normalized inner product `⟨x, y⟩` (p. 2), so
  `⟨v, v⟩ = 1` for `v ∈ {±1}^n`; `dot x y = ∑_u x_u y_u` is the unnormalized dot product that §7
  and Appendix A use silently.
* `tensorEntry k v u = ∑_i ∏_a v_i[u_a]` is the entry `T_u` of `T = ∑_i v_i^{⊗k}` (integer,
  unnormalized), and `pairing k v x = n^{-k} ∑_{u ∈ [n]^k} T_u x_{u_1} ⋯ x_{u_k} = ∑_i ⟨v_i, x⟩^k`
  is `⟨T, x^{⊗k}⟩` with the normalized inner product.
* Input encoding (one layout for every instance): memory cell `0` holds `n`, cell `1` holds `m`,
  cell `2` holds `ℓ`, cell `3 + c` holds the `c`-th entry of `T` in lexicographic order of
  `[n]^k` (`c < n^k`), every other cell `0`. Output: the `j`-th output vector is read from final
  memory cells `3 + n^k + j·n + u`, `u < n` (`j < m`), of the published machine's `outMem`.
* `Recovers k vhat v δ`: every output has `⟨v̂_j, v̂_j⟩ = 1`, and some permutation `π` of `[m]`
  has `⟨v̂_{π(i)}, v_i⟩ ≥ 1 − δ` for all `i` (`|⟨v̂_{π(i)}, v_i⟩| ≥ 1 − δ` when `k` is even).
* `failProb n m F` is the probability, under the uniform law of `v` and the published tape law,
  of the failure event `F v ω`: the average over `v` of the (outer) tape measure of
  `{ω | F v ω}`; it needs no measurability of `F`.
-/

namespace TensorBeyond.Main

open KXorTPCA.Reduction

/-- A sample `v_1, …, v_m ∈ {±1}^n` (index base 0). -/
abbrev Sample (n m : ℕ) := Fin m → Fin n → ℤˣ

/-- The component `v_i` as a real vector. -/
def vec {n m : ℕ} (v : Sample n m) (i : Fin m) : Fin n → ℝ :=
  fun u => ((v i u : ℤ) : ℝ)

/-- The normalized inner product `⟨x, y⟩ = (1/n) xᵀy` (p. 2). -/
noncomputable def ip {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ u, x u * y u

/-- The unnormalized dot product `xᵀy` (the convention of §7 and Appendix A). -/
def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ u, x u * y u

open Classical in
/-- The probability of an event when `v_1, …, v_m` are i.i.d. uniform on `{±1}^n`. -/
noncomputable def probV (n m : ℕ) (E : Sample n m → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Sample n m) : ℝ)

/-- The entry `T_u = ∑_i ∏_a v_i[u_a]` of `T = ∑_i v_i^{⊗k}` at the index tuple `u ∈ [n]^k`. -/
def tensorEntry (k : ℕ) {n m : ℕ} (v : Sample n m) (u : Fin k → Fin n) : ℝ :=
  ∑ i, ∏ a, vec v i (u a)

/-- `⟨T, x^{⊗k}⟩ = n^{-k} ∑_{u ∈ [n]^k} T_u ∏_a x_{u_a}` (normalized inner product). -/
noncomputable def pairing (k : ℕ) {n m : ℕ} (v : Sample n m) (x : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ) ^ k) * ∑ u : Fin k → Fin n, tensorEntry k v u * ∏ a, x (u a)

/-- The slack `ξ = m · n(3n − 2)/n⁴ − δ` of (6.1), with `δ` the `õ(1)` term. -/
noncomputable def xi4 (n m : ℕ) (δ : ℝ) : ℝ :=
  (m : ℝ) * ((n : ℝ) * (3 * (n : ℝ) - 2)) / (n : ℝ) ^ 4 - δ

/-- The position of `u ∈ [n]^k` in lexicographic order: `∑_a u_a n^{k-1-a}`. -/
def lexIndex {n k : ℕ} (u : Fin k → Fin n) : ℕ :=
  ∑ a : Fin k, (u a : ℕ) * n ^ (k - 1 - (a : ℕ))

/-- The input memory image: `n`, `m`, `ℓ` in cells `0, 1, 2`, then the entries of
`T = ∑_i v_i^{⊗k}` in lexicographic order from cell `3`; every other cell `0`. -/
noncomputable def encode (k n m ℓ : ℕ) (v : Sample n m) : ℤ → ℝ :=
  fun z =>
    if z = 0 then (n : ℝ) else if z = 1 then (m : ℝ) else if z = 2 then (ℓ : ℝ) else
      ∑ u : Fin k → Fin n, if z = 3 + (lexIndex u : ℤ) then tensorEntry k v u else 0

/-- The output vectors `v̂_0, …, v̂_{m-1} ∈ ℝ^n`: `v̂_j[u]` is final memory cell
`3 + n^k + j·n + u`. -/
noncomputable def outVecs (P : Program) (k n m : ℕ) (y : ℤ → ℝ) (ω : Tapes) :
    Fin m → Fin n → ℝ :=
  fun j u => outMem P y ω (3 + (n : ℤ) ^ k + (j : ℤ) * n + (u : ℤ))

/-- Success of Theorem 1.1 with footnote 1: unit outputs, and a permutation `π` with
`⟨v̂_{π(i)}, v_i⟩ ≥ 1 − δ` for all `i` (absolute value when `k` is even). -/
def Recovers (k : ℕ) {n m : ℕ} (vhat : Fin m → Fin n → ℝ) (v : Sample n m) (δ : ℝ) : Prop :=
  (∀ j, ip (vhat j) (vhat j) = 1) ∧
    ∃ π : Equiv.Perm (Fin m), ∀ i : Fin m,
      1 - δ ≤ (if Even k then |ip (vhat (π i)) (vec v i)| else ip (vhat (π i)) (vec v i))

/-- The probability of a failure event `F v ω` jointly over the uniform sample `v` and the tapes
`ω ∼ tapeLaw`: `|Sample|⁻¹ ∑_v tapeLaw {ω | F v ω}` (outer measure). -/
noncomputable def failProb (n m : ℕ) (F : Sample n m → Tapes → Prop) : ℝ :=
  (1 / (Fintype.card (Sample n m) : ℝ)) * ∑ v : Sample n m, (tapeLaw {ω | F v ω}).toReal

end TensorBeyond.Main


