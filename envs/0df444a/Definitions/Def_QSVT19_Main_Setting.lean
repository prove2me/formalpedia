-- Prove2me | Definitions.Def_QSVT19_Main_Setting
-- name    : QSVT19_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:44.879225+00:00
-- url     : https://prove2.me/theorems/5fde7a3b-f247-407d-907f-a4fd272fd972
-- title:
--   Projected unitaries, the alternating phase modulation sequence, and singular value transformation
-- statement:
--   This module fixes the objects of quantum signal processing (QSP) and of quantum singular value transformation, following §2–§3.2 of Gilyén, Su, Low and Wiebe.
--
--   **Polynomials.** For $P(x)=\sum_j a_jx^j\in\mathbb C[x]$, $P^*(x)=\sum_j a_j^*x^j$ and $\Re[P](x)=\sum_j \Re[a_j]x^j$. A pair $P,Q\in\mathbb C[x]$ is a *QSP pair of degree $k$* if
--   1. $\deg P\le k$ and $\deg Q\le k-1$ (so $Q=0$ when $k=0$);
--   2. $P$ has parity $k \bmod 2$ and $Q$ has parity $k-1 \bmod 2$;
--   3. $|P(x)|^2+(1-x^2)|Q(x)|^2=1$ for all $x\in[-1,1]$.
--
--   A degree-$d$ polynomial $P$ meets the *requirements of Corollary 8* if it has parity $d \bmod 2$, $|P(x)|\le 1$ on $[-1,1]$, $|P(x)|\ge 1$ for $|x|\ge 1$, and, when $d$ is even, $P(ix)P^*(ix)$ is real and at least $1$ for every real $x$.
--
--   **Reflections.** For $x\in[-1,1]$,
--   $$R(x)=\begin{pmatrix}x&\sqrt{1-x^2}\\ \sqrt{1-x^2}&-x\end{pmatrix},\qquad \prod_{j=1}^{d}\bigl(e^{i\varphi_j\sigma_z}R(x)\bigr),$$
--   the product taken with $j=1$ on the left.
--
--   **Projected unitaries.** On a finite-dimensional Hilbert space $\mathcal H_U$, let $U$ be unitary and $\Pi,\widetilde\Pi$ orthogonal projectors. The phase operator is $e^{i\varphi(2\Pi-I)}=e^{i\varphi}\Pi+e^{-i\varphi}(I-\Pi)$. For $\Phi\in\mathbb R^n$ the *alternating phase modulation sequence* $U_\Phi$ is the product, from $j=1$ on the left to $j=n$ on the right, of $e^{i\varphi_j(2\widetilde\Pi-I)}U$ when $n-j$ is even and $e^{i\varphi_j(2\Pi-I)}U^\dagger$ when $n-j$ is odd; this is (31).
--
--   A *singular value decomposition* of $A=\widetilde\Pi U\Pi$ consists of orthonormal bases $(\psi_i)_{i\in[d]}$ of $\mathrm{img}\,\Pi$ and $(\tilde\psi_i)_{i\in[\tilde d]}$ of $\mathrm{img}\,\widetilde\Pi$ and numbers $\varsigma_1\ge\varsigma_2\ge\dots\ge\varsigma_{d_{\min}}\ge0$, $d_{\min}=\min(d,\tilde d)$, with
--   $$A=\sum_{i=1}^{d_{\min}}\varsigma_i\,|\tilde\psi_i\rangle\langle\psi_i|.$$
--   For $f:\mathbb R\to\mathbb C$ the singular value transformation is
--   $$f^{(SV)}(A)=\sum_{i=1}^{d_{\min}}f(\varsigma_i)|\tilde\psi_i\rangle\langle\psi_i|\ \ (f\text{ odd}),\qquad f^{(SV)}(A)=\sum_{i=1}^{d}f(\varsigma_i)|\psi_i\rangle\langle\psi_i|\ \ (f\text{ even}),$$
--   with $\varsigma_i:=0$ for $d_{\min}<i\le d$. The module also defines the vectors $\psi_i^\perp=(I-\Pi)U^\dagger\tilde\psi_i/\sqrt{1-\varsigma_i^2}$, $\tilde\psi_i^\perp=(I-\widetilde\Pi)U\psi_i/\sqrt{1-\varsigma_i^2}$ of Definition 12, the spanning families of its invariant subspaces, and the one-qubit maps $\langle+|\otimes M$, $|+\rangle\otimes M$ and $|0\rangle\langle0|\otimes V+|1\rangle\langle1|\otimes W$ of (33).
--
--   These are the common definitions for every statement of the mission.
--
--   **Formalization Note** $\mathcal H_U$ is $\mathbb C^\iota$ for a finite type $\iota$, operators are complex $\iota\times\iota$ matrices, and $\Pi,\widetilde\Pi$ are named `Proj`, `Projt`. Indices are 0-based. $e^{i\varphi\sigma_z}$ and the parity predicate come from the published definition `QAlgorithms_Defs_Hamiltonian`. "Orthonormal basis of $\mathrm{img}\,\Pi$" is encoded as orthonormality plus $\Pi=\sum_i|\psi_i\rangle\langle\psi_i|$. The bound $\varsigma_i\le1$ is a consequence, not a field. The ancilla qubit is the first tensor factor.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, §2 (p. 6–7), Theorem 3 (i)–(iii) (p. 8), Definition 7 (13) (p. 12), Corollary 8 (p. 12–13), Definition 11 (17) (p. 15), Definition 12 (p. 15), Definition 15 (31) (p. 17), Definition 16 (p. 18), Corollary 18 (33) (p. 19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Hamiltonian

set_option autoImplicit false

open scoped ComplexOrder

/-!
# Quantum singular value transformation (Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, §2–§3.2)

Shared definition layer of the mission. The Hilbert space `H_U` is `ι → ℂ` for a finite type `ι`
(every finite-dimensional complex Hilbert space is isometric to some `ℂ^ι`), with inner product
`⟨v|w⟩ = star v ⬝ᵥ w`; operators are `Matrix ι ι ℂ`; the ket-bra `|v⟩⟨w|` is
`Matrix.vecMulVec v (star w)`. The projectors `Π, Π̃` of the paper are named `Proj, Projt`,
because `Π` is Lean binder notation. The paper's 1-based indices `[d] = {1, …, d}` are 0-based
`Fin d`. `e^{iφσ_z}` and the parity predicate come from the published definition
`QAlgorithms_Defs_Hamiltonian` (`QAlgorithms.qspZ`, `QAlgorithms.HasParity`).
-/

namespace QSVT19.Main

open Matrix Polynomial

noncomputable section

/-! ### Polynomials (§2, §3.1) -/

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, §2, p. 6–7: "let ℜ[P](x) := ∑_{j=0}^k ℜ[a_j]x^j
denote the real polynomial we get by taking the real part of the coefficients."
`RePartEq P PR` says `ℜ[P] = P_ℜ`: every coefficient of the real polynomial `PR` is the real
part of the corresponding coefficient of `P`. -/
def RePartEq (P : ℂ[X]) (PR : ℝ[X]) : Prop :=
  ∀ j : ℕ, (P.coeff j).re = PR.coeff j

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 3 (i)–(iii), p. 8:
(i) `deg(P) ≤ k` and `deg(Q) ≤ k − 1`; (ii) `P` has parity-(k mod 2) and `Q` has
parity-(k − 1 mod 2); (iii) `∀ x ∈ [−1, 1]: |P(x)|² + (1 − x²)|Q(x)|² = 1`.

**Formalization Note.** "deg(Q) ≤ k − 1" is `Q.degree < k` (so `k = 0` forces `Q = 0`; no
natural-number subtraction), and "parity-(k − 1 mod 2)" is `HasParity Q (k + 1)` (same parity
as `k − 1`). These are the conventions of the platform statement
`QAlgorithms.Childs.qsp_characterization` of Theorem 3. -/
def IsQSPPair (k : ℕ) (P Q : ℂ[X]) : Prop :=
  (P.degree ≤ k ∧ Q.degree < k) ∧
    (QAlgorithms.HasParity P k ∧ QAlgorithms.HasParity Q (k + 1)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 8, p. 12: the requirements on
`P ∈ ℂ[x]`: `P` is a degree-`d` polynomial such that
* `P` has parity-(d mod 2),
* `∀ x ∈ [−1, 1]: |P(x)| ≤ 1`,
* `∀ x ∈ (−∞, −1] ∪ [1, ∞): |P(x)| ≥ 1`,
* if `d` is even, then `∀ x ∈ ℝ: P(ix)P^*(ix) ≥ 1`.

**Formalization Note.** "degree-d" is `P.natDegree = d`. `P^*` (conjugated coefficients, §2,
p. 6) is `P.map (starRingEnd ℂ)`. The last bullet compares complex numbers; it uses Mathlib's
`ComplexOrder`, under which `1 ≤ z` means that `z` is real and at least `1`. -/
def Cor8Requirements (d : ℕ) (P : ℂ[X]) : Prop :=
  P.natDegree = d ∧ QAlgorithms.HasParity P d ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) ∧
    (∀ x : ℝ, 1 ≤ |x| → 1 ≤ ‖P.eval (x : ℂ)‖) ∧
    (Even d → ∀ x : ℝ,
      (1 : ℂ) ≤ P.eval (Complex.I * x) * (P.map (starRingEnd ℂ)).eval (Complex.I * x))

/-! ### Quantum signal processing with reflections (§3.1) -/

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 7, (13), p. 12: "We define a
parametrized family of single qubit reflection operators for all x ∈ [−1, 1] such that
R(x) := [x √(1 − x^2); √(1 − x^2) −x]."

**Formalization Note.** The paper defines `R(x)` only for `x ∈ [−1, 1]`; outside that interval
`Real.sqrt` returns `0` and the matrix is not a reflection. Every statement of the mission
restricts `x` to `[−1, 1]`. -/
def reflR (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ); (Real.sqrt (1 - x ^ 2) : ℂ), -(x : ℂ)]

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 8, (14), p. 13: the product
`∏_{j=1}^d (e^{iφ_jσ_z} R(x))`, with the factor `j = 1` leftmost.

**Formalization Note.** `Φ : Fin d → ℝ` is `(φ_1, …, φ_d)` with 0-based indices; the product is
`List.prod` of the factors in index order. `e^{iφσ_z}` is `QAlgorithms.qspZ φ`. For `d = 0` it is
the identity. -/
def qspRefl {d : ℕ} (Φ : Fin d → ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.ofFn fun j : Fin d => QAlgorithms.qspZ (Φ j) * reflR x).prod

/-! ### Projected unitaries and the alternating phase modulation sequence (§3.2) -/

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 15, p. 17: the phase operator
`e^{iφ(2Π−I)}` of an orthogonal projector `Π`.

**Formalization Note.** It is written `e^{iφ}Π + e^{−iφ}(I − Π)`, which equals the matrix
exponential `exp(iφ(2Π − I))` whenever `Π` is idempotent, because then `(2Π − I)² = I`. -/
def phaseRefl {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ℝ) (M : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Complex.exp (φ * Complex.I) • M + Complex.exp (-(φ * Complex.I)) • (1 - M)

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 15, (31), p. 17: "Let H_U be a
finite-dimensional Hilbert space and let U, Π, Π̃ ∈ End(H_U) be linear operators on H_U such that
U is a unitary, and Π, Π̃ are orthogonal projectors. Let Φ ∈ R^n, then we define the phased
alternating sequence U_Φ as follows
U_Φ := e^{iφ_1(2Π̃−I)}U ∏_{j=1}^{(n−1)/2} (e^{iφ_{2j}(2Π−I)}U^† e^{iφ_{2j+1}(2Π̃−I)}U) if n is
odd, and ∏_{j=1}^{n/2} (e^{iφ_{2j−1}(2Π−I)}U^† e^{iφ_{2j}(2Π̃−I)}U) if n is even."

**Formalization Note.** Both cases of (31) are the product, left to right over `j = 1, …, n`,
of the factor `e^{iφ_j(2Π̃−I)}U` when `n − j` is even and `e^{iφ_j(2Π−I)}U^†` when `n − j` is
odd. With 0-based `j : Fin n` the test is `(n − 1 − j) % 2 = 0` (no truncation occurs since
`j ≤ n − 1`). The arguments are `U`, `Proj = Π`, `Projt = Π̃`; `U^†` is `Uᴴ`. The definition
itself does not assume unitarity or projectivity; the statements do. -/
def altPhaseSeq {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) {n : ℕ}
    (Φ : Fin n → ℝ) : Matrix ι ι ℂ :=
  (List.ofFn fun j : Fin n =>
    if (n - 1 - j.val) % 2 = 0 then phaseRefl (Φ j) Projt * U
    else phaseRefl (Φ j) Proj * Uᴴ).prod

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 11, (17), p. 15: singular value
decomposition data of the projected unitary `A = Π̃UΠ`. "Let d := rank(Π), d̃ := rank(Π̃),
d_min := min(d, d̃). By singular value decomposition we know that there exist orthonormal bases
(|ψ_i⟩ : i ∈ [d]), (|ψ̃_i⟩ : i ∈ [d̃]) of the subspaces img(Π) and img(Π̃) respectively, such that
A = ∑_{i=1}^{d_min} ς_i|ψ̃_i⟩⟨ψ_i|, (17) and for all i ∈ [d_min]: ς_i ∈ R^+_0. Moreover,
ς_i ≥ ς_j for all i ≤ j ∈ [d_min]."

**Formalization Note.** A term of this structure is *one* singular value decomposition (the
data, not a chosen one). "`(ψ_i)` is an orthonormal basis of img(Π)" is encoded as orthonormality
together with `Π = ∑_i |ψ_i⟩⟨ψ_i|` (the identity the paper itself uses on p. 19); for an
orthogonal projector these are equivalent, and they force `d = rank Π`. The bound `ς_i ≤ 1` is a
consequence of unitarity and is deliberately not a field. `ψ_i` and `ψ̃_i` for `i < d_min` are
`ψ (Fin.castLE _ i)` and `ψt (Fin.castLE _ i)`. -/
structure ProjUnitarySVD {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ)
    where
  /-- `d = rank Π`. -/
  d : ℕ
  /-- `d̃ = rank Π̃`. -/
  dt : ℕ
  /-- The right singular vectors `|ψ_i⟩`, an orthonormal basis of `img Π`. -/
  ψ : Fin d → ι → ℂ
  /-- The left singular vectors `|ψ̃_i⟩`, an orthonormal basis of `img Π̃`. -/
  ψt : Fin dt → ι → ℂ
  /-- The singular values `ς_i`, `i ∈ [d_min]`. -/
  ς : Fin (min d dt) → ℝ
  orthonormal_ψ : ∀ i j, star (ψ i) ⬝ᵥ ψ j = if i = j then 1 else 0
  orthonormal_ψt : ∀ i j, star (ψt i) ⬝ᵥ ψt j = if i = j then 1 else 0
  span_ψ : Proj = ∑ i, vecMulVec (ψ i) (star (ψ i))
  span_ψt : Projt = ∑ i, vecMulVec (ψt i) (star (ψt i))
  ς_nonneg : ∀ i, 0 ≤ ς i
  ς_antitone : Antitone ς
  svd : Projt * U * Proj =
    ∑ i : Fin (min d dt), (ς i : ℂ) •
      vecMulVec (ψt (Fin.castLE (min_le_right d dt) i)) (star (ψ (Fin.castLE (min_le_left d dt) i)))

namespace ProjUnitarySVD

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {U Proj Projt : Matrix ι ι ℂ}

/-- `|ψ_i⟩` for `i ∈ [d_min]`. -/
def ψmin (S : ProjUnitarySVD U Proj Projt) (i : Fin (min S.d S.dt)) : ι → ℂ :=
  S.ψ (Fin.castLE (min_le_left S.d S.dt) i)

/-- `|ψ̃_i⟩` for `i ∈ [d_min]`. -/
def ψtmin (S : ProjUnitarySVD U Proj Projt) (i : Fin (min S.d S.dt)) : ι → ℂ :=
  S.ψt (Fin.castLE (min_le_right S.d S.dt) i)

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 16, p. 18: "for i ∈ [d] \ [d_min] we
define ς_i := 0" — the singular values extended by zero to `i ∈ [d]`. -/
def ςext (S : ProjUnitarySVD U Proj Projt) (i : Fin S.d) : ℝ :=
  if h : i.val < min S.d S.dt then S.ς ⟨i.val, h⟩ else 0

/-- The singular values extended by zero to `j ∈ [d̃]` (the same convention on the left side). -/
def ςextT (S : ProjUnitarySVD U Proj Projt) (j : Fin S.dt) : ℝ :=
  if h : j.val < min S.d S.dt then S.ς ⟨j.val, h⟩ else 0

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 12, p. 15:
`|ψ_i^⊥⟩ := (I − Π)U^†|ψ̃_i⟩ / ‖(I − Π)U^†|ψ̃_i⟩‖ = (I − Π)U^†|ψ̃_i⟩ / √(1 − ς_i²)` for
`i ∈ [r] \ [k]`.

**Formalization Note.** The second printed form is used. It is only meaningful for
`0 < ς_i < 1` (the paper's `i ∈ [r] \ [k]`); at `ς_i = 1` Lean's `(0 : ℂ)⁻¹ = 0` makes it `0`, and
no statement uses it there. -/
def ψperp (S : ProjUnitarySVD U Proj Projt) (i : Fin (min S.d S.dt)) : ι → ℂ :=
  ((Real.sqrt (1 - S.ς i ^ 2) : ℂ))⁻¹ • ((1 - Proj) *ᵥ (Uᴴ *ᵥ S.ψtmin i))

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 12, p. 15:
`|ψ̃_i^⊥⟩ := (I − Π̃)U|ψ_i⟩ / ‖(I − Π̃)U|ψ_i⟩‖ = (I − Π̃)U|ψ_i⟩ / √(1 − ς_i²)` for
`i ∈ [r] \ [k]` (same Formalization Note as `ψperp`). -/
def ψtperp (S : ProjUnitarySVD U Proj Projt) (i : Fin (min S.d S.dt)) : ι → ℂ :=
  ((Real.sqrt (1 - S.ς i ^ 2) : ℂ))⁻¹ • ((1 - Projt) *ᵥ (U *ᵥ S.ψmin i))

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 12 and Table 2, pp. 15–16: the
spanning vectors of the subspaces `H_i (i ∈ [r])`, `H_i^R (i ∈ [d] \ [r])`, `H_i^L
(i ∈ [d̃] \ [r])`: all `|ψ_i⟩ (i ∈ [d])`, the `|ψ_i^⊥⟩ (i ∈ [r] \ [k])` and the
`U^†|ψ̃_j⟩ (j ∈ [d̃] \ [r])`.

**Formalization Note.** `k` is the largest index with `ς_k = 1` and `r = rank(A)` is the number
of positive singular values. Since the `ς_i` are non-increasing, nonnegative and (as a
consequence of unitarity) at most `1`, "`i ∈ [r] \ [k]`" is `0 < ς_i < 1`, and "`j ∈ [d̃] \ [r]`"
is "`ς_j = 0` with `ς` extended by zero beyond `d_min`" (`ςextT`). These predicates replace the
cut-offs `k, r`. -/
def orthoFamily (S : ProjUnitarySVD U Proj Projt) :
    Fin S.d ⊕ {i : Fin (min S.d S.dt) // 0 < S.ς i ∧ S.ς i < 1} ⊕
      {j : Fin S.dt // S.ςextT j = 0} → ι → ℂ
  | .inl i => S.ψ i
  | .inr (.inl i) => S.ψperp i.1
  | .inr (.inr j) => Uᴴ *ᵥ S.ψt j.1

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 12, p. 15: the spanning vectors of the
subspaces `H̃_i (i ∈ [r])`, `H̃_i^R (i ∈ [d] \ [r])`, `H̃_i^L (i ∈ [d̃] \ [r])`: all
`|ψ̃_j⟩ (j ∈ [d̃])`, the `|ψ̃_i^⊥⟩ (i ∈ [r] \ [k])` and the `U|ψ_j⟩ (j ∈ [d] \ [r])`
(same index conventions as `orthoFamily`). -/
def orthoFamilyTilde (S : ProjUnitarySVD U Proj Projt) :
    Fin S.dt ⊕ {i : Fin (min S.d S.dt) // 0 < S.ς i ∧ S.ς i < 1} ⊕
      {j : Fin S.d // S.ςext j = 0} → ι → ℂ
  | .inl j => S.ψt j
  | .inr (.inl i) => S.ψtperp i.1
  | .inr (.inr j) => U *ᵥ S.ψ j.1

end ProjUnitarySVD

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 16, p. 18, odd case: "for odd
function f as f^{(SV)}(A) := ∑_{i=1}^{d_min} f(ς_i)|ψ̃_i⟩⟨ψ_i|", computed from the singular value
decomposition `S` of `A = Π̃UΠ`.

**Formalization Note.** Defined for every `f : ℝ → ℂ`; the statements apply it only to odd `f`.
It is a sum over the SVD data, never the operator expression of Theorem 17 or Corollary 18. -/
def svtOdd {ι : Type*} [Fintype ι] [DecidableEq ι] {U Proj Projt : Matrix ι ι ℂ} (f : ℝ → ℂ)
    (S : ProjUnitarySVD U Proj Projt) : Matrix ι ι ℂ :=
  ∑ i : Fin (min S.d S.dt), f (S.ς i) • vecMulVec (S.ψtmin i) (star (S.ψmin i))

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 16, p. 18, even case: "for even f as
f^{(SV)}(A) := ∑_{i=1}^{d} f(ς_i)|ψ_i⟩⟨ψ_i|, where for i ∈ [d] \ [d_min] we define ς_i := 0".

**Formalization Note.** Defined for every `f : ℝ → ℂ`; the statements apply it only to even
`f`. `ς_i := 0` beyond `d_min` is `ςext`. -/
def svtEven {ι : Type*} [Fintype ι] [DecidableEq ι] {U Proj Projt : Matrix ι ι ℂ} (f : ℝ → ℂ)
    (S : ProjUnitarySVD U Proj Projt) : Matrix ι ι ℂ :=
  ∑ i : Fin S.d, f (S.ςext i) • vecMulVec (S.ψ i) (star (S.ψ i))

/-! ### One ancilla qubit, for (33) -/

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 18, (33), p. 19: the operator
`⟨+| ⊗ M` from `ℂ² ⊗ H_U` to `H_U`, where `|+⟩ = (|0⟩ + |1⟩)/√2`; the ancilla qubit is the first
tensor factor (as in Definition 2's `X ⊗ Π`, p. 7). -/
def plusBra {ι : Type*} (M : Matrix ι ι ℂ) : Matrix ι (Fin 2 × ι) ℂ :=
  Matrix.of fun i bj => ((Real.sqrt 2 : ℂ))⁻¹ * M i bj.2

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 18, (33), p. 19: the operator
`|+⟩ ⊗ M` from `H_U` to `ℂ² ⊗ H_U` (ancilla first). -/
def plusKet {ι : Type*} (M : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) ι ℂ :=
  Matrix.of fun bi j => ((Real.sqrt 2 : ℂ))⁻¹ * M bi.2 j

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 18, (33), p. 19: the controlled
operator `|0⟩⟨0| ⊗ V + |1⟩⟨1| ⊗ W` on `ℂ² ⊗ H_U` (ancilla first). -/
def ctrlSel {ι : Type*} (V W : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  Matrix.kroneckerMap (· * ·) (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) V +
    Matrix.kroneckerMap (· * ·) (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) W

end

end QSVT19.Main


