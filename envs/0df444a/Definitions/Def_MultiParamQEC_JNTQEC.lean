-- Prove2me | Definitions.Def_MultiParamQEC_JNTQEC
-- name    : MultiParamQEC_JNTQEC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:55.449591+00:00
-- url     : https://prove2.me/theorems/dca58bda-0a5c-4e47-b60b-864a7dc10c88
-- title:
--   The JNT-QEC model: orthonormal Hermitian basis, noise span, QEC condition (6), evolution (20) and the JNT-QEC cost set
-- statement:
--   Let $\mathcal H_S=\mathbb C^d$ be the probe, $\mathcal H_A=\mathbb C^a$ an ancilla of any finite dimension $a$, and $G_1,\dots,G_P$ the generators of the parameters.
--
--   1. $\mathbb 1_d/\sqrt d,\{G_i\}_{i=1}^P,\{S_i\}_{i=1}^m,\{R_i\}_{i=1}^r$ form an **orthonormal basis of the Hermitian operators** on $\mathcal H_S$: all are Hermitian, they are orthonormal for the Hilbert–Schmidt product $\langle A,B\rangle=\mathrm{Tr}(AB)$, and there are $1+P+m+r=d^2$ of them.
--   2. The **noise span** is $\mathcal S=\mathrm{span}_{\mathbb R}\{\mathbb 1_d,S_1,\dots,S_m\}$.
--   3. A **code space** $\mathcal H_C\subseteq\mathcal H_S\otimes\mathcal H_A$ is given by its orthogonal projection $\Pi_C$; it satisfies the **QEC condition** (6) for $\mathcal S$ when $\Pi_C(X\otimes\mathbb 1)\Pi_C\propto\Pi_C$ for every $X\in\mathcal S$.
--   4. The **JNT-QEC evolution** (20) of an input $|\psi_{\rm in}\rangle$ for total time $T$ is
--   $$|\psi_{\boldsymbol\omega}\rangle=\exp\Big(-iT\sum_{j=1}^P\omega_j\,\Pi_C(G_j\otimes\mathbb 1)\Pi_C\Big)|\psi_{\rm in}\rangle .$$
--   5. The **JNT-QEC cost set** for a cost matrix $W$ is the set of costs $\mathrm{Tr}(W\Sigma)$ of all protocols: any ancilla dimension $a$, any code space satisfying (6), any unit input state $|\psi_{\rm in}\rangle\in\mathcal H_C$, the evolution (20), and any POVM on $\mathcal H_S\otimes\mathcal H_A$ with an estimator locally unbiased at $\boldsymbol\omega=0$.
--   6. For a code space $\mathcal H_C$ and $|c_0\rangle=|\psi_{\rm in}\rangle$, the **fixed-code frame set** is the set of values $\mathrm{Tr}(W(D^TD)^{-1})$, $D_{ij}=2T\,\mathrm{Im}\langle c_i|(G_j\otimes\mathbb 1)|c_0\rangle$, over orthonormal $|c_1\rangle,\dots,|c_P\rangle\in\mathcal H_C$ orthogonal to $|c_0\rangle$ with $D$ invertible.
--   7. Effective generators $G^R_1,\dots,G^R_P$ on $\mathbb C^{P+1}$ are **achievable with ancilla dimension $a$** when there are orthonormal $|c_0\rangle,\dots,|c_P\rangle\in\mathcal H_S\otimes\mathcal H_A$ whose span satisfies (6) and $[G^R_i]_{kl}=\langle c_k|G_i\otimes\mathbb 1|c_l\rangle$.
--
--   This is the model in which Theorem 2 characterizes the optimal joint error-corrected protocol.
--
--   **Formalization Note** $\mathcal H_S\otimes\mathcal H_A$ has index type `Fin d × Fin a` (probe first) and $X\otimes\mathbb 1$ is the Kronecker product `X ⊗ₖ 1`. The Hilbert–Schmidt product of Hermitian matrices is $\mathrm{Re}\,\mathrm{Tr}(AB)$. The noise span is a real subspace of the complex matrices. The estimation point is $\boldsymbol\omega=0$, as on p.7, so $|c_0\rangle=|\psi_{\boldsymbol\omega=0}\rangle=|\psi_{\rm in}\rangle$. The constraint $\langle c_i|c_0\rangle=0$ in item 6 is omitted in the printed display (21).
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 2–3, pp.2–3, Eq. (6); Theorem 2, p.5 ("where" clause of (8)); Sec. 4.2.2, pp.7–8, Eqs. (20)–(21) and the text above (25)

import Mathlib
import Definitions.Def_MultiParamQEC_Estimation

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-!
# The joint-parameter QEC (JNT-QEC) model

Górecki–Zhou–Jiang–Demkowicz-Dobrzański, *Optimal probes and error-correction schemes in
multi-parameter quantum metrology*, arXiv:1901.00896v4: the generators and the noise span
(Sec. 2–3, pp.2–3), the QEC condition (6) (p.3), the orthonormal Hermitian basis of Theorem 2
(p.5, the "where" clause of (8); p.8 above (25)), the effective evolution (20) (p.7), and the
JNT-QEC protocols of Sec. 4.2.2 (pp.7–8).

The probe space is `H_S = ℂ^d` (index `Fin d`), the ancilla `H_A = ℂ^a` (index `Fin a`) with
**any** `a : ℕ`, and `H_S ⊗ H_A` has index `Fin d × Fin a` (probe first). An operator `X` on
`H_S` acts on `H_S ⊗ H_A` as `X ⊗ₖ 1_a`. A code space `H_C ⊆ H_S ⊗ H_A` is given by its
orthogonal projection `PiC` (Hermitian and idempotent).

**Formalization Note.** The Hilbert–Schmidt product of Hermitian matrices is `Re Tr(AB)`
(`Tr(AB)` is real for Hermitian `A, B`). The noise span `S` is a real subspace of the complex
`d × d` matrices (`Submodule ℝ`). The estimation point is `ω = 0` ("We focus on the estimation
around point ω = [0, …, 0]", p.7), so `|c_0⟩ = |ψ_{ω=0}⟩ = |ψ_in⟩`.
-/

variable {d P m r : ℕ}

/-- The family `1_d/√d, G_1, …, G_P, S_1, …, S_m, R_1, …, R_r` indexed by
`Option (Fin P ⊕ Fin m ⊕ Fin r)` (`none` is `1_d/√d`). -/
noncomputable def basisFamily (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Option (Fin P ⊕ Fin m ⊕ Fin r) → Matrix (Fin d) (Fin d) ℂ :=
  fun o => o.elim ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
    (Sum.elim G (Sum.elim S R))

/-- `1_d/√d, {G_i}_{i=1}^P, {S_i}_{i=P+1}^{P′}, {R_i}_{i=P′+1}^{d²−1}` form an orthonormal basis of
the real space of Hermitian `d × d` matrices under the Hilbert–Schmidt product
(arXiv:1901.00896v4, Theorem 2, p.5; p.8 above Eq. (25)): every member is Hermitian, the family is
orthonormal for `⟨A, B⟩ = Re Tr(AB)`, and it has `d²` members (`m = P′ − P` matrices `S_i`,
`r = d² − 1 − P′` matrices `R_i`). An orthonormal family of `d²` Hermitian matrices is a basis of
that `d²`-dimensional real space. -/
def IsOrthonormalHermitianBasis (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  1 + P + m + r = d ^ 2 ∧ (∀ o, (basisFamily G S R o).IsHermitian) ∧
  ∀ o o', ((basisFamily G S R o * basisFamily G S R o').trace).re = if o = o' then 1 else 0

/-- The noise span `S = span_ℝ{1_d, S_1, …, S_m}` (arXiv:1901.00896v4, Theorem 2, p.5). -/
noncomputable def noiseSpan (S : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  Submodule.span ℝ (insert 1 (Set.range S))

/-- `PiC` is the orthogonal projection onto a code space `H_C ⊆ H_S ⊗ H_A`: Hermitian and
idempotent. -/
def IsCodeProjection {a : ℕ} (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) : Prop :=
  PiC.IsHermitian ∧ PiC * PiC = PiC

/-- The QEC condition (6) (arXiv:1901.00896v4, p.3): `Π_C (X ⊗ 1) Π_C ∝ Π_C` for every `X` in the
noise span `𝒮`. -/
def IsQECCode {a : ℕ} (𝒮 : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ))
    (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) : Prop :=
  ∀ X ∈ 𝒮, ∃ μ : ℂ, PiC * (X ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) * PiC = μ • PiC

/-- The JNT-QEC state family (arXiv:1901.00896v4, Eq. (20), p.7):
`|ψ_ω⟩ = exp(−iT Σ_j ω_j Π_C (G_j ⊗ 1) Π_C) |ψ_in⟩`. -/
noncomputable def jntState {a : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) (ψin : Fin d × Fin a → ℂ) (T : ℝ) :
    (Fin P → ℝ) → Fin d × Fin a → ℂ :=
  fun ω => NormedSpace.exp ((-(Complex.I * (T : ℂ))) •
      ∑ j, ((ω j : ℝ) : ℂ) • (PiC * (G j ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) * PiC)) *ᵥ ψin

/-- The set of costs `Δ²_W ω̃ = Tr(WΣ)` achievable by JNT-QEC protocols (arXiv:1901.00896v4,
Sec. 4.2.2, pp.7–8): any ancilla dimension `a`, any code space (projection `PiC`) satisfying the QEC
condition (6) for the noise span `𝒮`, any unit input state `|ψ_in⟩ ∈ H_C`, the effective evolution
(20) for total time `T`, and any POVM on `H_S ⊗ H_A` with countably many outcomes together with an
estimator locally unbiased at `ω = 0` (Eq. (4)). -/
def jntCostSet (G : Fin P → Matrix (Fin d) (Fin d) ℂ) (𝒮 : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ))
    (W : Matrix (Fin P) (Fin P) ℝ) (T : ℝ) : Set ℝ :=
  {c | ∃ (a : ℕ) (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) (ψin : Fin d × Fin a → ℂ),
      IsCodeProjection PiC ∧ IsQECCode 𝒮 PiC ∧ star ψin ⬝ᵥ ψin = 1 ∧ PiC *ᵥ ψin = ψin ∧
      c ∈ familyCostSet (jntState G PiC ψin T) 0 W}

/-- The matrix `D_ij = 2T Im⟨c_i|(G_j ⊗ 1)|c_0⟩` of Eq. (21) (arXiv:1901.00896v4, p.8). -/
noncomputable def codeFrameMatrix {a : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (c₀ : Fin d × Fin a → ℂ) (T : ℝ) (c : Fin P → Fin d × Fin a → ℂ) :
    Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun i j =>
    2 * T * (star (c i) ⬝ᵥ ((G j ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ c₀)).im

/-- The values `Tr(W(DᵀD)⁻¹)` of the fixed-code program (21) (arXiv:1901.00896v4, p.8) over
orthonormal `c_1, …, c_P ∈ H_C` orthogonal to `|c_0⟩`, with `D` invertible.

**Formalization Note.** As in `frameSet`, the constraint `⟨c_i|c_0⟩ = 0` (the `c_i` span the
`x_i`, which are orthogonal to `|ψ_ω⟩` by (14)) is omitted in the printed display (21), which is
false without it; `D` invertible excludes the junk value `(DᵀD)⁻¹ = 0`. -/
noncomputable def codeFrameSet {a : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (PiC : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ) (c₀ : Fin d × Fin a → ℂ) (T : ℝ)
    (W : Matrix (Fin P) (Fin P) ℝ) : Set ℝ :=
  {t | ∃ c : Fin P → Fin d × Fin a → ℂ, (∀ i j, star (c i) ⬝ᵥ c j = if i = j then 1 else 0) ∧
      (∀ i, PiC *ᵥ c i = c i) ∧ (∀ i, star (c i) ⬝ᵥ c₀ = 0) ∧
      (codeFrameMatrix G c₀ T c).det ≠ 0 ∧
      t = (W * ((codeFrameMatrix G c₀ T c)ᵀ * codeFrameMatrix G c₀ T c)⁻¹).trace}

/-- The orthogonal projection `Σ_k |c_k⟩⟨c_k|` onto `span{c_0, …, c_P}` for orthonormal `c_k`. -/
noncomputable def codeProj {a : ℕ} (c : Fin (P + 1) → Fin d × Fin a → ℂ) :
    Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  ∑ k, Matrix.vecMulVec (c k) (star (c k))

/-- `{G^R_i}` is an achievable set of effective generators on the reference space
`H_R = span{|0⟩, …, |P⟩}` with ancilla dimension `a` (arXiv:1901.00896v4, p.8): there are
orthonormal `c_0, …, c_P ∈ H_S ⊗ H_A` whose span satisfies the QEC condition (6) and
`[G^R_i]_kl = ⟨c_k|G_i ⊗ 1|c_l⟩`. -/
def IsAchievableGenerators (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (𝒮 : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) (a : ℕ)
    (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) : Prop :=
  ∃ c : Fin (P + 1) → Fin d × Fin a → ℂ,
    (∀ k l, star (c k) ⬝ᵥ c l = if k = l then 1 else 0) ∧ IsQECCode 𝒮 (codeProj c) ∧
    ∀ i k l, GR i k l = star (c k) ⬝ᵥ ((G i ⊗ₖ (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ c l)

end MultiParamQEC


