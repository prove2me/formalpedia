-- Prove2me | Definitions.Def_QuarticGap_Supplement_fourierZ
-- name    : QuarticGap_Supplement_fourierZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:50:47.166475+00:00
-- url     : https://prove2.me/theorems/e46897c6-293a-475b-84b2-dfcb5c6290ca
-- title:
--   Definition 3.7 — the vector $z_f$, $D_f$ and the task $\mathrm{Samp}_S(\varepsilon)$
-- statement:
--   Let $S \subseteq \{0,1\}^m$ be a nonempty set of characters, put $K = |S|$, and let $\bot$ be a symbol that is not in $\{0,1\}^m$. For a Boolean function $f:\{0,1\}^m \to \{-1,1\}$ with normalized Fourier coefficients $Z_s(f)$, the vector $z_f$ is indexed by $S \cup \{\bot\}$ by
--   $$
--   z_f(s) = \frac{Z_s(f)}{\sqrt K}\quad (s \in S), \qquad z_f(\bot) = 1,
--   $$
--   and $D_f = \|z_f\|^2 = 1 + K^{-1}\sum_{s\in S} Z_s(f)^2$. The task $\mathrm{Samp}_S(\varepsilon)$ asks, given query access to $f$, for a random element of $S\cup\{\bot\}$ whose law is within total variation distance $\varepsilon$ of $p_{z_f}$, for every Boolean function $f$. The item also fixes the query budget
--   $$
--   q_0 = \Bigl\lfloor \frac{M}{32\log(512K)} \Bigr\rfloor, \qquad M = 2^m,
--   $$
--   of Theorem 3.9, with the natural logarithm.
--
--   Fourier sampling on a set of characters is the simplest application of the transfer theorem, and the output vectors of all matrix families of the paper are close to an affine function of these coefficients.
--
--   **Formalization Note** $S \cup \{\bot\}$ is `Option S`, with `none` the symbol $\bot$. $q_0$ here is not the published `QuarticGap.q0` (the budget $q_0(\xi,\delta)$ of (11)).
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Definition 3.7, pp.26–27; Theorem 3.9, p.27

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap.Supplement

/-- The vector `z_f` of Definition 3.7 (Chakrabarti, Herman, Kim, Ozgul, *The Quartic Gap Between
Quantum and Dequantized Algorithms for Linear Algebra Is Tight*, arXiv:2610.42069 (file sha256
9f68aaf9…), Definition 3.7, p.26). For a nonempty set `S ⊆ {0,1}^m` of characters with `K = |S|` and a
Boolean function `f`, `z_f` is indexed by `S ∪ {⊥}`, with `z_f(s) = Z_s(f)/√K` for `s ∈ S` and
`z_f(⊥) = 1`.

**Formalization Note** The index set `S ∪ {⊥}` is `Option S`, with `none` the symbol `⊥`, which is
therefore not an element of `{0,1}^m`. `Z_s(f)` is the published `QuarticGap.Zs`. -/
noncomputable def zf {m : ℕ} (S : Finset (Qubits m)) (f : Qubits m → ℤˣ) : Option S → ℝ
  | none => 1
  | some s => Zs f s / Real.sqrt S.card

/-- `D_f = ∥z_f∥² = 1 + K⁻¹ ∑_{s∈S} Z_s(f)²` (arXiv:2610.42069, Definition 3.7, p.26). -/
noncomputable def Df {m : ℕ} (S : Finset (Qubits m)) (f : Qubits m → ℤˣ) : ℝ :=
  ∑ j, zf S f j ^ 2

/-- The target distribution `p_{z_f}` of the task `Samp_S(ε)` (arXiv:2610.42069, Definition 3.7,
pp.26–27): output an element of `S ∪ {⊥}` whose law is within total variation distance `ε` of
`p_{z_f}`, for every Boolean function `f`. Since `z_f(⊥) = 1`, `z_f ≠ 0` for every `f`. -/
noncomputable def fourierTarget {m : ℕ} (S : Finset (Qubits m)) (f : Qubits m → ℤˣ) :
    Option S → ℝ :=
  lenSqDist (zf S f)

/-- The query budget `q₀ = ⌊M/(32 log(512K))⌋` of Theorem 3.9 (arXiv:2610.42069, p.27), with
`M = 2^m`, `K = |S|` and the natural logarithm (§2.1, p.15).

**Formalization Note** This is not the published `QuarticGap.q0`, which is the budget `q₀(ξ, δ)` of
(11); the two agree at `ξ = 1/4`, `δ = 1/256` only through the proof of Theorem 3.9. -/
noncomputable def q0S {m : ℕ} (S : Finset (Qubits m)) : ℕ :=
  ⌊bigM m / (32 * Real.log (512 * S.card))⌋₊

end QuarticGap.Supplement


