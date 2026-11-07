-- Prove2me | Definitions.Def_NonadaptiveSFT_Fourier
-- name    : NonadaptiveSFT_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:57.13372+00:00
-- url     : https://prove2.me/theorems/144f82cf-475b-47b2-b746-ecd4f09688fd
-- title:
--   The group $G=(\mathbb Z/2^a\mathbb Z)^d$, characters $\chi_f$, the normalized transform $\widehat X$, $H_k$ and $\sigma_k(\widehat X)_2$
-- statement:
--   Let $a,d\ge1$ be integers, $G=(\mathbb Z/2^a\mathbb Z)^d$ and $N=|G|=2^{ad}$. For $f,t\in G$ the pairing is $\langle f,t\rangle=\sum_{i=1}^d f_it_i\in\mathbb Z/2^a\mathbb Z$ and the character is
--
--   $$\chi_f(t)=\exp\big(2\pi i\langle f,t\rangle/2^a\big).$$
--
--   The Fourier transform of a signal $X:G\to\mathbb C$ is
--
--   $$\widehat X(f)=\frac1N\sum_{t\in G}X(t)\,\overline{\chi_f(t)},\qquad\text{so that}\qquad X(t)=\sum_{f\in G}\widehat X(f)\chi_f(t).$$
--
--   For a complex vector $v$ on a finite index set, $\|v\|_2=(\sum_i|v_i|^2)^{1/2}$, $\|v\|_\infty=\max_i|v_i|$, and $|\mathrm{supp}(v)|$ is the number of nonzero entries.
--
--   Fix an order on the index set. $H_k(Y)$ keeps the $k$ coordinates of largest magnitude, ties broken by the order, and sets the others to zero; it selects exactly $k$ coordinates even when $Y$ has fewer than $k$ nonzero entries. The best $k$-term approximation error is $\sigma_k(Y)_2=\|Y-H_k(Y)\|_2$. The coordinatewise median of $r$ complex numbers takes the median of the real parts and of the imaginary parts separately.
--
--   These are the objects in which every statement of the paper is written.
--
--   **Formalization Note** The order is given by an injective key into $\mathbb N$ (smaller key wins a tie); on $G$ the paper's fixed order is taken to be the lexicographic order of the coordinate representatives in $\{0,\dots,2^a-1\}$. The character uses the representative of $\langle f,t\rangle$ in $\{0,\dots,2^a-1\}$, which gives the same value as any other representative. The median of $r$ reals is the $((r+1)/2)$-th smallest.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), §1, eq. (1), p.1 (PDF p.3); §2.1 Notation, p.17 (PDF p.19)

import Mathlib

open scoped BigOperators

namespace NonadaptiveSFT

/-!
# The group `(ℤ/2^aℤ)^d`, its characters, the normalized Fourier transform, `H_k` and `σ_k`

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…), §1, p.1 (eq. (1)), and §2.1, p.17 (PDF pp.3, 19).

"Throughout, a, d ≥ 1 are integers, G = (Z/2^aZ)^d, N = |G| = 2^{ad}. … For f, t ∈ G, write
⟨f, t⟩ = Σ_{i=1}^d f_i t_i ∈ Z/2^aZ, so that the character χ_f(t) = exp(2πi⟨f, t⟩/2^a) is well
defined." The Fourier coefficient is X̂(f) := (1/N) Σ_{t∈G} X(t)·conj(χ_f(t)).

**Formalization Note.**
* `G a d := Fin d → ZMod (2^a)`; the paper's coordinate `i + 1` is the index `i : Fin d`.
* `chi a d f t = exp(2πi · ⟨f,t⟩.val / 2^a)`, where `⟨f,t⟩.val ∈ {0, …, 2^a − 1}` is the
  representative of the pairing; this is the paper's `χ_f(t)`, well defined modulo `2^a`.
* `hat` is the transform with the normalization `1/N` and the complex conjugate on `χ_f`, so that
  `X(t) = Σ_f X̂(f) χ_f(t)` (the paper's (1)).
* `l2` is the Euclidean norm `(Σ |v_i|²)^{1/2}` and `linf` the maximum modulus (`0` on an empty
  index type) of a vector on a finite index type.
* `Hk key k Y`: "keeping k coordinates of largest magnitude, with ties broken by this order"
  (p.17). The fixed order is given by an injective key `key : ι → ℕ` (smaller key wins a tie);
  every linear order on a finite type is of this form. Coordinate `g` beats `f` when
  `|Y g| > |Y f|`, or `|Y g| = |Y f|` and `key g < key f`; `f` is selected when fewer than `k`
  coordinates beat it. For an injective key exactly `min k |ι|` coordinates are selected, also
  when `Y` has fewer than `k` nonzero entries, as the page requires.
* `sigma key k Y := ‖Y − H_k(Y)‖₂`, the paper's `σ_k(Y)₂`; it does not depend on the key.
* `lexKey a d f := Σ_i (f i).val · 2^{a(d−1−i)}` is the lexicographic order on
  `((f 0).val, …, (f (d−1)).val)`: the fixed order on `G` used by the main theorem.
* `median x` of `r` reals is the `((r+1)/2)`-th smallest entry (the middle one for odd `r`), and
  `cmedian` is the coordinatewise median of complex numbers (real and imaginary parts separately).
-/

/-- The group `G = (ℤ/2^aℤ)^d`. -/
abbrev G (a d : ℕ) : Type := Fin d → ZMod (2 ^ a)

/-- The pairing `⟨f, t⟩ = Σ_i f_i t_i ∈ ℤ/2^aℤ`. -/
def pair {a d : ℕ} (f t : G a d) : ZMod (2 ^ a) := ∑ i, f i * t i

/-- The character `χ_f(t) = exp(2πi⟨f, t⟩/2^a)`. -/
noncomputable def chi {a d : ℕ} (f t : G a d) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((pair f t).val : ℂ) / (2 : ℂ) ^ a)

/-- The normalized Fourier transform `X̂(f) = (1/N) Σ_t X(t)·conj(χ_f(t))`, `N = 2^{ad}`. -/
noncomputable def hat {a d : ℕ} (X : G a d → ℂ) : G a d → ℂ :=
  fun f => (1 / (2 : ℂ) ^ (a * d)) * ∑ t, X t * (starRingEnd ℂ) (chi f t)

/-- The Euclidean norm of a complex vector on a finite index type. -/
noncomputable def l2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The maximum modulus `‖v‖_∞ = max_i |v_i|` (`0` on an empty index type). -/
noncomputable def linf {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ((Finset.univ.sup fun i => ‖v i‖₊ : NNReal) : ℝ)

/-- The number of nonzero coordinates `|supp(v)|`. -/
noncomputable def suppCard {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℕ := by
  classical exact (Finset.univ.filter fun i => v i ≠ 0).card

/-- The selected coordinate set of `H_k(Y)`: the coordinates beaten by fewer than `k` others. -/
noncomputable def selected {ι : Type*} [Fintype ι] (key : ι → ℕ) (k : ℕ) (Y : ι → ℂ) :
    Finset ι := by
  classical exact Finset.univ.filter fun f =>
    (Finset.univ.filter fun g => ‖Y f‖ < ‖Y g‖ ∨ (‖Y g‖ = ‖Y f‖ ∧ key g < key f)).card < k

/-- `H_k(Y)`: keep the selected coordinates and set the others to zero. -/
noncomputable def Hk {ι : Type*} [Fintype ι] (key : ι → ℕ) (k : ℕ) (Y : ι → ℂ) : ι → ℂ := by
  classical exact fun f => if f ∈ selected key k Y then Y f else 0

/-- The best `k`-term approximation error `σ_k(Y)₂ = ‖Y − H_k(Y)‖₂`. -/
noncomputable def sigma {ι : Type*} [Fintype ι] (key : ι → ℕ) (k : ℕ) (Y : ι → ℂ) : ℝ :=
  l2 (Y - Hk key k Y)

/-- The lexicographic key on `G`: coordinate `0` is the most significant digit in base `2^a`. -/
def lexKey (a d : ℕ) (f : G a d) : ℕ :=
  ∑ i : Fin d, (f i).val * (2 ^ a) ^ (d - 1 - (i : ℕ))

/-- The median of `r` reals: the `((r+1)/2)`-th smallest entry. -/
noncomputable def median {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ((List.ofFn x).insertionSort (· ≤ ·)).getD ((r - 1) / 2) 0

/-- The coordinatewise median of `r` complex numbers. -/
noncomputable def cmedian {r : ℕ} (z : Fin r → ℂ) : ℂ :=
  ⟨median fun i => (z i).re, median fun i => (z i).im⟩

end NonadaptiveSFT


