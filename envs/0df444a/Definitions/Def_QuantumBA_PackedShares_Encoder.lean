-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Encoder
-- name    : QuantumBA_PackedShares_Encoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:50.10018+00:00
-- url     : https://prove2.me/theorems/1f4231c2-f94f-45df-930e-2676d8a4702d
-- title:
--   The share encoder $V_{D,\sigma,p}$ of eq. (4), partial trace, and polynomial decoding
-- statement:
--   Let $F$ be a finite field with $q$ elements and let $\alpha_1,\dots,\alpha_D\in F$ be evaluation points. For $s=(s_0,\dots,s_{p-1})\in F^p$ and $r=(r_0,\dots,r_{\sigma-1})\in F^\sigma$ put
--   $$f_{s,r}(X)=\sum_{j<p}s_jX^j+\sum_{j<\sigma}r_jX^{p+j}.$$
--   The **share encoder** is the linear map $V_{D,\sigma,p}$ from $(\mathbb C^{F})^{\otimes p}$ to $(\mathbb C^{F})^{\otimes D}$ with
--   $$V_{D,\sigma,p}\,|s\rangle=q^{-\sigma/2}\sum_{r\in F^\sigma}\bigotimes_{i=1}^{D}|f_{s,r}(\alpha_i)\rangle ,$$
--   written as a $q^D\times q^p$ matrix in the computational basis (its entry at $(y,s)$ is $q^{-\sigma/2}$ times the number of $r$ whose evaluation vector is $y$).
--
--   For a set $A$ of outputs, $\operatorname{Tr}_{\bar A}$ is the partial trace over the outputs outside $A$. For a degree bound $d_{\mathrm{poly}}<D$ and a report vector $y\in F^D$, $\mathrm{Dec}_{d_{\mathrm{poly}}}(y)$ is the coefficient vector of the polynomial of degree at most $d_{\mathrm{poly}}$ whose evaluation vector lies within Hamming distance $\lfloor (D-d_{\mathrm{poly}}-1)/2\rfloor$ of $y$, and the zero vector if there is none.
--
--   These objects carry the privacy and decoding statements of Lemma 5.1 and are used by every block of QBA:PackedShares.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 23, eq. (4) and the decoding convention of §5.1 (PDF p. 24)

import Mathlib

set_option autoImplicit false

open scoped BigOperators Matrix

namespace QuantumBA.PackedShares

/-! # The share encoder `V_{D,σ,p}` of eq. (4), partial traces, and polynomial decoding (§5.1) -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `f_{s,r}(α) = ∑_{j<p} s_j α^j + ∑_{j<σ} r_j α^{p+j}`. -/
def polyEval {p σ : ℕ} (s : Fin p → F) (r : Fin σ → F) (a : F) : F :=
  ∑ j : Fin p, s j * a ^ (j : ℕ) + ∑ j : Fin σ, r j * a ^ (p + (j : ℕ))

/-- The evaluation vector `(f_{s,r}(α_1), …, f_{s,r}(α_D))`. -/
def evalVec {D p σ : ℕ} (α : Fin D → F) (s : Fin p → F) (r : Fin σ → F) : Fin D → F :=
  fun i => polyEval s r (α i)

/-- The share encoder of eq. (4) as a `q^D × q^p` matrix in the computational basis:
`V_{D,σ,p}|s⟩ = q^{-σ/2} ∑_{r ∈ F^σ} ⊗_{i=1}^D |f_{s,r}(α_i)⟩`, i.e. the entry at `(y, s)` is
`q^{-σ/2}` times the number of `r` with `evalVec α s r = y`. -/
noncomputable def encoder (D σ p : ℕ) (α : Fin D → F) : Matrix (Fin D → F) (Fin p → F) ℂ :=
  fun y s => ((((Fintype.card F : ℝ) ^ (-(σ : ℝ) / 2)) : ℝ) : ℂ) *
    ((Finset.univ.filter (fun r : Fin σ → F => evalVec α s r = y)).card : ℂ)

/-- Glue a label on `A ⊆ Fin D` and a label on its complement. -/
def glue {D : ℕ} (A : Finset (Fin D)) (a : A → F) (c : {i : Fin D // i ∉ A} → F) : Fin D → F :=
  fun i => if h : i ∈ A then a ⟨i, h⟩ else c ⟨i, h⟩

/-- Partial trace `Tr_{Ā}` over the outputs outside `A`, of an operator on `D` registers. -/
def ptraceCompl {D : ℕ} (A : Finset (Fin D)) (Mx : Matrix (Fin D → F) (Fin D → F) ℂ) :
    Matrix (A → F) (A → F) ℂ :=
  fun a b => ∑ c : {i : Fin D // i ∉ A} → F, Mx (glue A a c) (glue A b c)

/-- Evaluation vector of the polynomial with coefficient vector `c` (degree `≤ dpoly`). -/
def codeword {D dpoly : ℕ} (α : Fin D → F) (c : Fin (dpoly + 1) → F) : Fin D → F :=
  fun i => ∑ j : Fin (dpoly + 1), c j * α i ^ (j : ℕ)

/-- `Dec_{dpoly}(y)`: unique decoding to a polynomial of degree at most `dpoly` within radius
`⌊(D - dpoly - 1)/2⌋`, returning its coefficient vector, or the zero vector when no codeword lies
within the radius. (For `dpoly < D` and distinct points the codeword within the radius is
unique, so the choice below is determined.) -/
noncomputable def rsDecode {D : ℕ} (dpoly : ℕ) (α : Fin D → F) (y : Fin D → F) : Fin (dpoly + 1) → F := by
  classical
  exact if h : ∃ c : Fin (dpoly + 1) → F, hammingDist (codeword α c) y ≤ (D - dpoly - 1) / 2
    then h.choose else 0

end QuantumBA.PackedShares


