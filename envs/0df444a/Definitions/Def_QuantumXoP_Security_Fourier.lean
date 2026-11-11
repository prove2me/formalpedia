-- Prove2me | Definitions.Def_QuantumXoP_Security_Fourier
-- name    : QuantumXoP_Security_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:40.262352+00:00
-- url     : https://prove2.me/theorems/44340f73-c1fa-41a4-83b8-87f57791b24c
-- title:
--   Functionals on $F_n$, characters, Fourier coefficients and the laws $D_F$, $D_{XoP[r]}$
-- statement:
--   Fix $n\ge 0$ and write $N=2^n$. Bit strings $x\in\{0,1\}^n$ are added by bitwise XOR, and $\langle a,x\rangle=\sum_i a_ix_i \bmod 2$. The set
--   $$F_n=\{f:\{0,1\}^n\to\{0,1\}^n\}$$
--   is a group under pointwise XOR; its dual $\widehat F$ is the same group, whose elements are written $\gamma$. A **functional** is a map $H:F_n\to\mathbb C$.
--
--   1. **Characters.** $\chi_a(x)=(-1)^{\langle a,x\rangle}$ on strings and $\chi_\gamma(f)=\prod_{x}\chi_{\gamma(x)}(f(x))$ on $F_n$. The support of $\gamma$ is $\mathrm{supp}(\gamma)=\{x:\gamma(x)\ne0^n\}$ and its degree is $|\gamma|=|\mathrm{supp}(\gamma)|$.
--   2. **Inner product and norm.** $\langle H,G\rangle=\mathbb E_{f\leftarrow F}[\overline{H(f)}\,G(f)]$ (conjugate on the first argument) and $\|H\|_2=|\langle H,H\rangle|^{1/2}$.
--   3. **Fourier coefficients and components.** $\widehat H(\gamma)=\langle\chi_\gamma,H\rangle$; the degree-$d$ component $H^{=d}=\sum_{|\gamma|=d}\widehat H(\gamma)\chi_\gamma$; the low-degree part $H^{\le d}=\sum_{i\le d}H^{=i}$; $H$ has Fourier degree at most $d$ when $H=H^{\le d}$; the maximal magnitude $M^{=d}[H]=\max_{|\gamma|=d}|\widehat H(\gamma)|$.
--   4. **Convolution and densities.** $(G*H)(f)=\mathbb E_{g\leftarrow F}[G(f+g)H(g)]$; the density of a law $D$ on $F_n$ is $\mu_D(f)=\Pr[f\leftarrow D]/(1/|F|)$.
--   5. **Laws.** $D_F$ is uniform on $F_n$; $\mu_P$ is the density of a uniformly random permutation of $\{0,1\}^n$; $D_{XoP[r]}$ is the law of $P_1+\dots+P_r$ for independent uniformly random permutations $P_1,\dots,P_r$; the law of $f+g$ for independent $f\leftarrow D$, $g\leftarrow E$.
--   6. **The index $\gamma^{(i\leftarrow d)}$** (p. 22): for $\mathrm{supp}(\gamma)=\{x_1,\dots,x_d\}$ with $y_j=\gamma(x_j)$, it equals $y_i+y_d$ at $x_i$, $0^n$ at $x_d$, and $\gamma$ elsewhere.
--
--   These are the objects of the Fourier analysis of §3 and of the bounds on $\mu_{XoP[r]}$ in §5–§7.
--
--   **Formalization Note** Strings are `Qubits n = Fin n → Bool` from the published `QAlgorithms_Defs_Basic`, whose addition is XOR. $M^{=d}[H]$ is the supremum over the finite set of degree-$d$ indices, $0$ when that set is empty (for $d>N$, or for $n=0$ and $d>0$). Densities are real numbers cast to $\mathbb C$.
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), §2 p. 8 (PDF p. 10), §3.1 pp. 9–11 (PDF pp. 11–13), Eqs. (5), (8); §4 p. 14 (PDF p. 16); p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

noncomputable section

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-!
# Fourier analysis of functionals on `F_n` (Choi–Hhan–Jang, §2 p. 8, §3.1 pp. 9–11, §4 p. 14)

Strings are `Qubits n = Fin n → Bool`; their addition (Boolean-ring addition, pointwise) is the
bitwise XOR `x + y` of p. 8, and `dotBits a x` is `⟨a, x⟩ = Σ_i a_i x_i mod 2`.
`F_n = {f : {0,1}^n → {0,1}^n}` is the group `Qubits n → Qubits n` under pointwise XOR;
its dual `F^` is the same group (p. 8, footnote 3). A functional is a map `F_n → ℂ` (p. 9).
-/

/-- p. 8: `F_n`, all functions from `n`-bit strings to `n`-bit strings, with pointwise XOR. -/
abbrev Fn (n : ℕ) := Qubits n → Qubits n

/-- p. 8: `N := 2^n`, as a real number. -/
abbrev bigN (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- p. 9, before Eq. (4): the character `χ_a(x) = (−1)^{⟨a,x⟩}` on `{0,1}^n`, as a complex number. -/
def chiStr {n : ℕ} (a x : Qubits n) : ℂ :=
  if dotBits a x then -1 else 1

/-- p. 9, Eq. (5): the character `χ_γ(f) = ∏_x χ_{γ(x)}(f(x))` on `F_n`, for `γ ∈ F^ = F_n`. -/
def chi {n : ℕ} (γ f : Fn n) : ℂ :=
  ∏ x : Qubits n, chiStr (γ x) (f x)

/-- p. 9: `supp(γ) = {x : γ(x) ≠ 0^n}`. -/
def supp {n : ℕ} (γ : Fn n) : Finset (Qubits n) :=
  Finset.univ.filter fun x => γ x ≠ 0

/-- p. 9: the degree `|γ| = |supp(γ)|` of a character index `γ`. -/
def charDeg {n : ℕ} (γ : Fn n) : ℕ :=
  (supp γ).card

/-- p. 9: the inner product `⟨H, G⟩ = E_{f←F}[conj(H(f)) G(f)]` of functionals (conjugate on the
first argument, as in the proof of Lemma 3.2, p. 11). -/
def innerF {n : ℕ} (H G : Fn n → ℂ) : ℂ :=
  ((Fintype.card (Fn n) : ℂ))⁻¹ * ∑ f : Fn n, conj (H f) * G f

/-- p. 9: the norm `‖H‖₂ = |⟨H, H⟩|^{1/2}`. -/
def l2norm {n : ℕ} (H : Fn n → ℂ) : ℝ :=
  Real.sqrt ‖innerF H H‖

/-- p. 9, Theorem 3.1: the Fourier coefficient `Ĥ(γ) = ⟨χ_γ, H⟩`. -/
def fourierCoeff {n : ℕ} (H : Fn n → ℂ) (γ : Fn n) : ℂ :=
  innerF (chi γ) H

/-- p. 10: the degree-`d` component `H^{=d} = Σ_{|γ| = d} Ĥ(γ) χ_γ`. -/
def degComp {n : ℕ} (H : Fn n → ℂ) (d : ℕ) : Fn n → ℂ :=
  fun f => ∑ γ ∈ Finset.univ.filter (fun γ : Fn n => charDeg γ = d), fourierCoeff H γ * chi γ f

/-- p. 10: the low-degree part `H^{≤d} = Σ_{i ≤ d} H^{=i} = Σ_{|γ| ≤ d} Ĥ(γ) χ_γ`. -/
def lowDeg {n : ℕ} (H : Fn n → ℂ) (d : ℕ) : Fn n → ℂ :=
  fun f => ∑ i ∈ Finset.range (d + 1), degComp H i f

/-- p. 10: `H` has Fourier degree at most `d`, i.e. `H = H^{≤d}` (`deg(H) ≤ d`). -/
def FourierDegLE {n : ℕ} (H : Fn n → ℂ) (d : ℕ) : Prop :=
  H = lowDeg H d

/-- p. 10, Eq. (8): the degree-`d` maximal magnitude `M^{=d}[H] = max_{|γ| = d} |Ĥ(γ)|`
(the value `0` when no `γ` has degree `d`: `d > 2^n`, or `n = 0` and `d > 0`). -/
def maxMag {n : ℕ} (H : Fn n → ℂ) (d : ℕ) : ℝ :=
  (((Finset.univ.filter (fun γ : Fn n => charDeg γ = d)).sup fun γ => ‖fourierCoeff H γ‖₊ : NNReal) : ℝ)

/-- p. 11: the convolution `(G ∗ H)(f) = E_{g←F}[G(f + g) H(g)]`. -/
def conv {n : ℕ} (G H : Fn n → ℂ) : Fn n → ℂ :=
  fun f => ((Fintype.card (Fn n) : ℂ))⁻¹ * ∑ g : Fn n, G (f + g) * H g

/-- p. 8 and p. 11: the density `μ_D(f) = Pr[f ← D] / (1/|F|)` of a distribution `D` on `F_n`,
as a (real-valued) functional. -/
def density {n : ℕ} (D : PMF (Fn n)) : Fn n → ℂ :=
  fun f => (((Fintype.card (Fn n) : ℝ) * (D f).toReal : ℝ) : ℂ)

/-- p. 8, p. 14: `D_F`, the uniform distribution on `F_n` (`S_∞` of Definition 6.3). -/
def uniformF (n : ℕ) : PMF (Fn n) :=
  PMF.uniformOfFintype (Fn n)

/-- p. 13: the uniform distribution on `P_n = {p ∈ F_n : p injective}`, the law of a uniformly
random permutation of `{0,1}^n` viewed as a function. -/
def permLaw (n : ℕ) : PMF (Fn n) :=
  (PMF.uniformOfFintype (Equiv.Perm (Qubits n))).map fun p => (p : Qubits n → Qubits n)

/-- p. 14: `D_{XoP[r]}`, the law of `XoP[r] = P_1 + ⋯ + P_r` for independent uniformly random
permutations `P_1, …, P_r` of `{0,1}^n`. -/
def xopLaw (n r : ℕ) : PMF (Fn n) :=
  (PMF.uniformOfFintype (Fin r → Equiv.Perm (Qubits n))).map fun ps x => ∑ i : Fin r, ps i x

/-- p. 11 (Lemma 3.3): the law of `f + g` for independent `f ← D`, `g ← E`. -/
def xorLaw {n : ℕ} (D E : PMF (Fn n)) : PMF (Fn n) :=
  D.bind fun f => E.map fun g => f + g

/-- p. 22 (before Lemma 5.7): for `supp(γ) = {x_1, …, x_d}` with `y_j = γ(x_j)`, the character
index `γ^{(i←d)}` with `x_i = xi` and `x_d = xd`: it takes the value `y_i + y_d` at `x_i`, `0^n` at
`x_d`, and agrees with `γ` elsewhere (so `y_j` at `x_j` for `j ∈ [d−1] ∖ {i}` and `0^n` off the
support). -/
def shiftChar {n : ℕ} (γ : Fn n) (xi xd : Qubits n) : Fn n :=
  fun x => if x = xi then γ xi + γ xd else if x = xd then 0 else γ x

/-! ### Sanity checks -/

example : chiStr (0 : Qubits 2) ![true, false] = 1 := by
  have : dotBits (0 : Qubits 2) ![true, false] = false := by decide
  simp [chiStr, this]

example : chiStr (![true, false] : Qubits 2) ![true, true] = -1 := by
  have : dotBits (![true, false] : Qubits 2) ![true, true] = true := by decide
  simp [chiStr, this]

example {n : ℕ} : charDeg (0 : Fn n) = 0 := by
  simp [charDeg, supp]

example : (1 + 1 : Qubits 1) = 0 := by decide

end QuantumXoP.Security


