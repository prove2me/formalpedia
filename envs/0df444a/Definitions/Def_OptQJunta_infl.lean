-- Prove2me | Definitions.Def_OptQJunta_infl
-- name    : OptQJunta_infl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:30.479202+00:00
-- url     : https://prove2.me/theorems/b4483d5e-b39c-4919-830c-5ddbc1a91c32
-- title:
--   Fourier coefficients of $(-1)^f$, the influence $\mathrm{Inf}_T[f]$ and the support $\mathrm{supp}(f)$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be a Boolean function and write $(-1)^f$ for its sign function $x\mapsto(-1)^{f(x)}$. For $S\subseteq[n]$ the **parity character** is $\chi_S(x)=(-1)^{\sum_{i\in S}x_i}$, and the **Fourier coefficient** of $(-1)^f$ at $S$ is
--
--   $$
--   \widehat{(-1)^f}(S)=\mathbb E_X\bigl[(-1)^{f(X)}\chi_S(X)\bigr],
--   $$
--
--   with $X$ uniform on $\{0,1\}^n$. For $T\subseteq[n]$, the **influence** of $T$ on $f$ (Definition 2.19) is
--
--   $$
--   \mathrm{Inf}_T[f]=\sum_{S:\,S\cap T\neq\varnothing}\bigl|\widehat{(-1)^f}(S)\bigr|^2,\qquad \mathrm{Inf}_i[f]=\mathrm{Inf}_{\{i\}}[f].
--   $$
--
--   A coordinate $i$ is **relevant** to $f$ if $f(x)\neq f(x\oplus e_i)$ for some $x$, and the **support** $\mathrm{supp}(f)$ is the set of relevant coordinates.
--
--   By Parseval's identity the squared coefficients form a probability distribution on subsets (the law of a Fourier sample), and $\mathrm{Inf}_T[f]$ is the probability that a Fourier sample meets $T$. These quantities link junta distance to Fourier sampling throughout the paper.
--
--   **Formalization Note** Bits are `Bool` and $\{0,1\}^n$ is `QAlgorithms.Qubits n`; coordinates are `Fin n` from $0$. All quantities are real-valued, so $|\cdot|^2$ is a square. $S\cap T\ne\varnothing$ is `¬ Disjoint S T`; the complement $\overline T$ is `Tᶜ`. `flipAt x i` is $x\oplus e_i$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.2.1, p.13; Definition 2.19, p.18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta

open QAlgorithms

/-- The bit flip `x ⊕ e_i` of coordinate `i` of `x ∈ {0,1}^n` (Bao, Gao, Yao, *Optimal Quantum Junta
Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, §2.2.1, p.13: "write `e_i` for the
`i`th coordinate vector").

**Formalization Note** Bits are `Bool` and `{0,1}^n` is `QAlgorithms.Qubits n = Fin n → Bool`;
coordinate `i : Fin n` is the paper's coordinate `i + 1` (0-based indices change no instance). -/
def flipAt {n : ℕ} (x : Qubits n) (i : Fin n) : Qubits n :=
  Function.update x i (!x i)

/-- The sign function `(−1)^f : x ↦ (−1)^{f(x)}` of a Boolean function `f : {0,1}^n → {0,1}`
(Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, §2.2.1, p.13). -/
noncomputable def signFn {n : ℕ} (f : Qubits n → Bool) (x : Qubits n) : ℝ :=
  if f x then -1 else 1

/-- The parity character `χ_S(x) = (−1)^{Σ_{i∈S} x_i}` for `S ⊆ [n]` (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, §2.2.1, p.13). The exponent is the number of `i ∈ S` with
`x_i = 1`. -/
noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (x : Qubits n) : ℝ :=
  (-1 : ℝ) ^ (S.filter fun i => x i = true).card

/-- The Fourier coefficient `\widehat{(−1)^f}(S) = E_X[(−1)^{f(X)} χ_S(X)]` of the sign function of a
Boolean function, `X` uniform on `{0,1}^n` (Bao–Gao–Yao preprint, version of November 3, 2026,
sha256 a97d09a4…, §2.2.1, p.13; uniform inner product `⟨f, g⟩ = E_X[\overline{f(X)} g(X)]`).

**Formalization Note** The function and the characters are real-valued, so the coefficient is real
and `|\widehat{(−1)^f}(S)|²` is its square. -/
noncomputable def fourierSign {n : ℕ} (f : Qubits n → Bool) (S : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Qubits n, signFn f x * chi S x

/-- **Definition 2.19** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.18):
the influence of a coordinate set `T ⊆ [n]` on `f : {0,1}^n → {0,1}`,
`Inf_T[f] = Σ_{S : S ∩ T ≠ ∅} |\widehat{(−1)^f}(S)|²`; `Inf_i[f] = Inf_{{i}}[f]` is `infl f {i}`.

**Formalization Note** `S ∩ T ≠ ∅` is `¬ Disjoint S T`. The complement `T̄ = [n] ∖ T` used by the
paper is `Tᶜ`. -/
noncomputable def infl {n : ℕ} (f : Qubits n → Bool) (T : Finset (Fin n)) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ Disjoint S T), fourierSign f S ^ 2

/-- The support `supp(f)` of a Boolean function: the set of relevant coordinates, those `i` with
`f(x) ≠ f(x ⊕ e_i)` for some `x` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, §2.2.1, p.13). -/
def supp {n : ℕ} (f : Qubits n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x : Qubits n, f x ≠ f (flipAt x i)

end OptQJunta


