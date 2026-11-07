-- Prove2me | Definitions.Def_QuarticGap_Phi
-- name    : QuarticGap_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:05.130833+00:00
-- url     : https://prove2.me/theorems/f10fdc1b-6627-47de-b6ed-aebd72482061
-- title:
--   Fourier coefficients, the sine and cosine tests, $\Phi$, the bias $\Lambda_F$, $q_0$, and instances of the transfer theorem
-- statement:
--   Fix $m \ge 2$, $M = 2^m$, and a Boolean function $f : \{0,1\}^m \to \{-1,1\}$. With $\chi_s(\sigma) = (-1)^{s\cdot\sigma}$, the **normalized Fourier coefficient** is
--   $$
--   Z_s(f) = \frac{1}{\sqrt M} \sum_{\sigma} \chi_s(\sigma) f(\sigma) .
--   $$
--   For a set $S$ of $K$ characters inside a finite outcome set $Y$, the **sine test** and **cosine test** are
--   $$
--   F_{\sin}(f,s) = \sin Z_s(f), \qquad F_{\cos}(f,s) = \cos Z_s(f) - c_M, \qquad c_M = \cos(M^{-1/2})^M,
--   $$
--   for $s \in S$, and both vanish on $Y \setminus S$. For $\gamma \in \mathbb C^S$, $\beta \in \mathbb C$, $d > 0$,
--   $$
--   \Phi(f) = \frac{1}{dK} \sum_{s\in S} |\gamma_s + \beta Z_s(f)|^2 F(f,s),
--   $$
--   and the **bias** is $\Lambda_F = \mathbb E\,\Phi(f)$ for uniformly random $f$. The item also defines $b_M$, $a_M$ of (8), $\Phi_{\max} = 4(\|\gamma\|^2 + |\beta|^2 M)/(dK)$, the threshold $q_0(\xi,\delta) = \lfloor \xi^2 M/(2\log(2K/\delta)) \rfloor$ of (11), $\tau_F$ of (12), $F_\infty$, the left side of (13), and a bundled instance of Theorem 3.4 for a sequence as in Corollary 3.6.
--
--   This is the vocabulary of the classical lower bound.
--
--   **Formalization Note** "$Y \supseteq S$" is an embedding of $S$ into $Y$, which is how the source identifies $(j,0^k)$ with coordinate $j$ of the third block. The natural-number subtractions in the exponents of $a_M$, $b_M$ are exact since $m \ge 2$.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), §3.1–3.2, pp.21–22; (11), (12), p.24; (13), p.25; Lemma 3.2, p.23; Lemma 3.5, Corollary 3.6, p.26

import Mathlib
import Definitions.Def_QuarticGap_sqRespond

open QAlgorithms
open scoped ComplexConjugate

namespace QuarticGap

/-- `M = 2^m` as a real number (arXiv:2610.42069, §3.1, p.21). -/
noncomputable def bigM (m : ℕ) : ℝ := 2 ^ m

/-- The character `χ_s(σ) = (−1)^{s·σ}` (arXiv:2610.42069, §3.1, p.21). -/
def chi {m : ℕ} (s σ : Qubits m) : ℝ := if dotBits s σ then -1 else 1

/-- The normalized Fourier coefficient `Z_s(f) = M^{−1/2} ∑_σ χ_s(σ) f(σ)`
(arXiv:2610.42069, (4), p.21). -/
noncomputable def Zs {m : ℕ} (f : Qubits m → ℤˣ) (s : Qubits m) : ℝ :=
  (Real.sqrt (bigM m))⁻¹ * ∑ σ, chi s σ * sgn (f σ)

/-- `c_M = cos(M^{−1/2})^M` (arXiv:2610.42069, (6), p.22). -/
noncomputable def cM (m : ℕ) : ℝ := Real.cos (Real.sqrt (bigM m))⁻¹ ^ (2 ^ m)

/-- `b_M = √M sin(M^{−1/2}) cos(M^{−1/2})^{M−1}` (arXiv:2610.42069, (8), p.22). The natural-number
subtraction is exact since `M ≥ 1`. -/
noncomputable def bM (m : ℕ) : ℝ :=
  Real.sqrt (bigM m) * Real.sin (Real.sqrt (bigM m))⁻¹ * Real.cos (Real.sqrt (bigM m))⁻¹ ^ (2 ^ m - 1)

/-- `a_M = cos(M^{−1/2})^{M−2} (1 − M sin²(M^{−1/2}))` (arXiv:2610.42069, (8), p.22). The
natural-number subtraction is exact for `m ≥ 1`, and the section fixes `m ≥ 2`. -/
noncomputable def aM (m : ℕ) : ℝ :=
  Real.cos (Real.sqrt (bigM m))⁻¹ ^ (2 ^ m - 2) * (1 - bigM m * Real.sin (Real.sqrt (bigM m))⁻¹ ^ 2)

/-- Which test function: the sine test or the cosine test (arXiv:2610.42069, (6), p.22). -/
inductive TestKind where
  | sin
  | cos

/-- The value of a test at a character with coefficient `z`: `sin z`, or `cos z − c_M`
(arXiv:2610.42069, (6), p.22). -/
noncomputable def testVal (k : TestKind) (m : ℕ) (z : ℝ) : ℝ :=
  match k with
  | .sin => Real.sin z
  | .cos => Real.cos z - cM m

/-- The test function `F(f, j)` on an outcome set `Y ⊇ S` (arXiv:2610.42069, (6), p.22): for `j = e s`
with `s ∈ S` it is `testVal` at `Z_s(f)`, and it is `0` on `Y ∖ S`.

**Formalization Note** "`Y ⊇ S`" is the embedding `e`, which is how the source identifies the
character `(j, 0^k)` with coordinate `j` of the third block. -/
noncomputable def testF {m : ℕ} {S : Finset (Qubits m)} {Y : Type*} (k : TestKind) (e : S ↪ Y)
    (f : Qubits m → ℤˣ) (j : Y) : ℝ :=
  Function.extend e (fun s : S => testVal k m (Zs f s)) 0 j

/-- `Φ(f) = (dK)⁻¹ ∑_{s∈S} |γ_s + βZ_s(f)|² F(f, s)` (arXiv:2610.42069, (7), p.22), with `K = |S|`. -/
noncomputable def Phi {m : ℕ} (k : TestKind) (S : Finset (Qubits m)) (γ : S → ℂ) (β : ℂ) (d : ℝ)
    (f : Qubits m → ℤˣ) : ℝ :=
  (d * S.card)⁻¹ * ∑ s : S, ‖γ s + β * (Zs f s : ℂ)‖ ^ 2 * testVal k m (Zs f s)

/-- The bias `Λ_F = 𝔼Φ(f)` over uniformly random `f` (arXiv:2610.42069, p.22). -/
noncomputable def Lambda {m : ℕ} (k : TestKind) (S : Finset (Qubits m)) (γ : S → ℂ) (β : ℂ)
    (d : ℝ) : ℝ :=
  uAvg (Phi k S γ β d)

/-- `Φ_max = 4(∥γ∥² + |β|²M)/(dK)` (arXiv:2610.42069, Lemma 3.2, p.23). -/
noncomputable def PhiMax {m : ℕ} (S : Finset (Qubits m)) (γ : S → ℂ) (β : ℂ) (d : ℝ) : ℝ :=
  4 * (∑ s, ‖γ s‖ ^ 2 + ‖β‖ ^ 2 * bigM m) / (d * S.card)

/-- `𝔼F(f, J_A)` for uniformly random `f` and the output `J_A` of an algorithm that queries `f`
directly (arXiv:2610.42069, Lemma 3.3, p.24). -/
noncomputable def expF {m : ℕ} {S : Finset (Qubits m)} {Y : Type*} [Fintype Y] (k : TestKind)
    (e : S ↪ Y) (A : QueryAlg (Qubits m) ℤˣ Y) : ℝ :=
  uAvg fun f : Qubits m → ℤˣ =>
    ∑ j, A.outProb (directRespond f) j * testF k e f j

/-- The query threshold `q₀(ξ, δ) = ⌊ξ²M/(2 log(2K/δ))⌋` (arXiv:2610.42069, (11), p.24). -/
noncomputable def q0 (m K : ℕ) (ξ δ : ℝ) : ℕ :=
  ⌊ξ ^ 2 * bigM m / (2 * Real.log (2 * K / δ))⌋₊

/-- `τ_sin(ξ, δ) = ξ + δ`, `τ_cos(ξ, δ) = ξ² + 2δ` (arXiv:2610.42069, (12), p.24). -/
noncomputable def tauF (k : TestKind) (ξ δ : ℝ) : ℝ :=
  match k with
  | .sin => ξ + δ
  | .cos => ξ ^ 2 + 2 * δ

/-- `F∞ = 1` for the sine test and `F∞ = 2` for the cosine test (arXiv:2610.42069, Lemma 3.5, p.26). -/
def Finf (k : TestKind) : ℝ :=
  match k with
  | .sin => 1
  | .cos => 2

/-- The Euclidean norm of a finite vector. -/
noncomputable def l2 {ι E : Type*} [Fintype ι] [Norm E] (x : ι → E) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The left side of (13) (arXiv:2610.42069, p.25): `𝔼[1[f ∈ G] |∑_{j∈Y} p_{x(f)}(j)F(f, j) − Φ(f)|]`
for uniformly random `f`. -/
noncomputable def transferGap {m : ℕ} {S : Finset (Qubits m)} {Y : Type*} [Fintype Y] (k : TestKind)
    (e : S ↪ Y) (G : Set (Qubits m → ℤˣ)) (x : (Qubits m → ℤˣ) → Y → ℂ) (γ : S → ℂ) (β : ℂ)
    (d : ℝ) : ℝ :=
  uAvg fun f =>
    G.indicator
      (fun f => |∑ j, lenSqDist (x f) j * testF k e f j - Phi k S γ β d f|) f

/-- One instance of Theorem 3.4 for the test `k` (arXiv:2610.42069, Theorem 3.4, p.25, as used by
Corollary 3.6, p.26): `S`, `Y ⊇ S` with `Y ∖ S ≠ ∅`, `G`, targets `x(f)` nonzero on `G`, and `γ`, `β`,
`d > 0`, `η ≥ 0` satisfying (13). The numbers `q`, `τ`, `ε` of the theorem are not part of an instance.

**Formalization Note** "`Y ∖ S ≠ ∅`" is that `e` is not surjective. Only `m ≥ 2` is carried for the
section's "Fix m ≥ 2". -/
structure TransferInstance (k : TestKind) where
  /-- `m`, with `M = 2^m`. -/
  m : ℕ
  /-- The section's standing assumption. -/
  hm : 2 ≤ m
  /-- The set of characters. -/
  S : Finset (Qubits m)
  /-- `K = |S| ≥ 1`. -/
  hS : S.Nonempty
  /-- The outcome set. -/
  Y : Type
  /-- The outcome set is finite. -/
  instY : Fintype Y
  /-- `Y ⊇ S`. -/
  e : S ↪ Y
  /-- `Y ∖ S ≠ ∅`. -/
  hY : ¬ Function.Surjective e
  /-- The set of Boolean functions. -/
  G : Set (Qubits m → ℤˣ)
  /-- The target vectors. -/
  x : (Qubits m → ℤˣ) → Y → ℂ
  /-- Targets are nonzero on `G`. -/
  hx : ∀ f ∈ G, x f ≠ 0
  /-- `γ`. -/
  γ : S → ℂ
  /-- `β`. -/
  β : ℂ
  /-- `d`. -/
  d : ℝ
  /-- `d > 0`. -/
  hd : 0 < d
  /-- `η`. -/
  η : ℝ
  /-- `η ≥ 0`. -/
  hη : 0 ≤ η
  /-- The hypothesis (13). -/
  h13 : transferGap k e G x γ β d ≤ η

end QuarticGap


