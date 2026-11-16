-- Prove2me | Definitions.Def_GL2QFT_Supplement_TotalA
-- name    : GL2QFT_Supplement_TotalA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:40:17.417033+00:00
-- url     : https://prove2.me/theorems/a4b71030-7268-4b81-8c7b-544a7ed3410a
-- title:
--   The total A-matrix of the Mackey circuit for $B<\mathrm{GL}_2(\mathbb F_q)$, blocks from (70), and its register codes
-- statement:
--   The total A-matrix of the Mackey circuit for $B<G=\mathrm{GL}_2(\mathbb F_q)$ (Definition 5.3, §6.4.3–6.4.4).
--
--   1. The Mackey data of §6.4.3: $\Omega=\{e,w\}$ with $w=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $H_e=B$, $H_w=T$, $U^e_{\rm twist}=I$, and $U^w_{\rm twist}$ by (126): $\chi^w_{\alpha,\beta}=\chi_{\beta,\alpha}$ and $|w_\delta\rangle\mapsto|w_{\delta^{-1}\gamma}\rangle$ on $\rho_\gamma$.
--   2. The $B$-adapted labels of the Gelfand–Tsetlin bases of §6.2 (Lemma 6.7): ${\det}_\alpha$: $\chi_{\alpha,\alpha}$; ${\rm St}_\alpha$: $\chi_{\alpha,\alpha}\mapsto|v^\perp\rangle$, $(\rho_{\alpha^2},\delta)\mapsto|w_\delta\rangle$; $I_{\alpha,\beta}$: $\chi_{\alpha,\beta}\mapsto|\infty\rangle$, $\chi_{\beta,\alpha}\mapsto|v_0\rangle$, $(\rho_{\alpha\beta},\delta)\mapsto|w_\delta\rangle$; $\pi_\theta$: $(\rho_\gamma,\delta)\mapsto|w_\delta\rangle$; and the $T$-adapted labels of the $B$-irreps ($|w_\delta\rangle$ of $\rho_\gamma$ carries $\chi_{\delta,\delta^{-1}\gamma}$).
--   3. The blocks $A_{\lambda,\tilde\lambda}$ by (70) with these data, $[G:B]=q+1$, $[B:B]=1$, $[B:T]=q$, and
--   $$A=\sum_{\lambda,\tilde\lambda\in\widehat B}|\lambda\rangle\langle\lambda|\otimes A_{\lambda,\tilde\lambda}\otimes|\tilde\lambda\rangle\langle\tilde\lambda| ,$$
--   from the registers $(\lambda,\kappa,\omega,\tilde\lambda)$ with $(\kappa,\omega)\in K_{\lambda,\tilde\lambda}$ to the registers $(\lambda,\mu,\tilde\lambda)$.
--   4. Fixed binary codes of these registers: label fields of $\lceil\log_2 q^2\rceil$ bits, $[\lambda,\kappa,\omega,\tilde\lambda]$ at the input and $[\lambda,\mu,\tilde\lambda]$ at the output.
--
--   **Formalization Note** The blocks are computed from (70), not taken from the displays (128)–(145). For $\lambda=\tilde\lambda=\rho_\gamma$ the block agrees with the published `AGamma` (144)–(145), and every block is unitary; this was checked numerically at $q=3,5,7$ (`numerics/a70_check.py`).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1 p.34, Lemma 6.7 p.37, Definition 5.3 eq. (70) p.30, §6.4.3 eq. (126) and §6.4.4 pp.44–46, proof of Theorem 6.14 p.47 (PDF pp.31, 35, 38, 45–48)

import Definitions.Def_GL2QFT_Uniform

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace TotalA

open FieldData QAlgorithms
open scoped ComplexConjugate

variable (D : FieldData)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1, p.34 (PDF p.35): the Weyl representative
`w := (0 1; 1 0)` (`w² = e`), the nontrivial double-coset representative of `B\G/B` (86). -/
def wGL : D.G :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- arXiv:2608.28573, Lemma 6.7, (104)–(107), p.37, in the Gelfand–Tsetlin bases of §6.2 (the basis
of every `G`-irrep is subgroup-adapted to `B`, Definition 3.1): the basis label `P : ν → μ` of the
`G`-irrep `μ` for the `B`-irrep `ν ∈ N⁻(μ)` and `P ∈ B_ν` (`none` if `ν ∉ N⁻(μ)`):
* `det α`: `χ_{α,α} ↦ |v⟩`;
* `St_α`: `χ_{α,α} ↦ |v^⊥⟩`, `(ρ_{α²}, δ) ↦ |w_δ⟩`;
* `I_{α,β}` (`α ≺ β`): `χ_{α,β} ↦ |∞⟩`, `χ_{β,α} ↦ |v₀⟩`, `(ρ_{αβ}, δ) ↦ |w_δ⟩`;
* `π_θ`, `θ|_{F*_q} = χ_γ`: `(ρ_γ, δ) ↦ |w_δ⟩`.

**Formalization Note** These are the block forms of the published `R μ` on `B` (Lemma 6.7, checked
entry by entry, phases included, by `numerics/lean_defs_check.py`, check 3). -/
def labMu : (μ : D.Irr) → (ν : D.BIrr) → D.BBas ν → Option (D.Bas μ)
  | .inl α, .inl ab, _ => if ab = (α, α) then some () else none
  | .inl _, .inr _, _ => none
  | .inr (.inl α), .inl ab, _ => if ab = (α, α) then some (none : Option D.Lab) else none
  | .inr (.inl α), .inr γ, δ =>
      if γ = 2 * α then some (some (show D.Lab from δ) : Option D.Lab) else none
  | .inr (.inr (.inl αβ)), .inl ab, _ =>
      if ab = αβ.1 then some (none : Option (Option D.Lab))
      else if ab = (αβ.1.2, αβ.1.1) then some (some none : Option (Option D.Lab)) else none
  | .inr (.inr (.inl αβ)), .inr γ, δ =>
      if γ = αβ.1.1 + αβ.1.2 then some (some (some (show D.Lab from δ)) : Option (Option D.Lab))
      else none
  | .inr (.inr (.inr _)), .inl _, _ => none
  | .inr (.inr (.inr k)), .inr γ, δ =>
      if γ = D.restrLab k.1 then some (show D.Lab from δ) else none

/-- arXiv:2608.28573, Lemma 6.7, (102)–(103), p.37: the basis of every `B`-irrep is adapted to the
torus `T = H_w`: the basis label of `ν` carrying the `T`-character `κ = χ_{a,b}`
(`χ_{α,β}`: its vector when `κ = χ_{α,β}`; `ρ_γ`: `|w_δ⟩` carries `χ_{δ,δ⁻¹γ}`). -/
def tLab : (ν : D.BIrr) → D.Lab × D.Lab → Option (D.BBas ν)
  | .inl αβ, ab => if ab = αβ then some (show Unit from ()) else none
  | .inr γ, ab => if ab.1 + ab.2 = γ then some (show D.Lab from ab.1) else none

/-- arXiv:2608.28573, §6.4.3, eq. (126), p.45 (PDF p.46): the untwisting map `U^w_twist` for the
cell `w` (one-dimensional block intertwiners the identity): `χ^w_{α,β} = χ_{β,α}`, and on `ρ_γ`,
`|w_δ⟩ ↦ |w_{δ⁻¹γ}⟩`, the summand `χ_{δ⁻¹γ,δ}`. Entry `[U^w_twist]^{κ}_{P}` for the `T`-character
`κ = χ_{a,b}` and the basis label `P` of `λ`. -/
def utwW : (l : D.BIrr) → D.Lab × D.Lab → D.BBas l → ℂ
  | .inl αβ, ab, _ => if ab = (αβ.2, αβ.1) then 1 else 0
  | .inr γ, ab, δ => if ab = (γ - (show D.Lab from δ), (show D.Lab from δ)) then 1 else 0

/-- The entry `[R_μ(x)]^{P'}_{P}` for optional labels (`0` if either label is absent). -/
def Rent (μ : D.Irr) (x : D.G) : Option (D.Bas μ) → Option (D.Bas μ) → ℂ
  | some i, some j => D.R μ x i j
  | _, _ => 0

/-- arXiv:2608.28573, Definition 5.3, eq. (70), p.30 (PDF p.31), instantiated for `B < G = GL₂(F_q)`
with the Mackey data of §6.4.3 (p.44): `Ω = {e, w}`, `H_e = B`, `H_w = T`, `U^e_twist = I`,
`U^w_twist` by (126), `[G : B] = q + 1`, `[B : H_e] = 1`, `[B : H_w] = |U| = q`. The entry
`[A_{λ,λ̃}]^μ_{κ,ω} = √(d_μ [B:H_ω] / (d_κ d_λ d_λ̃ [G:B])) Σ_{P ∈ B_λ, P̃ ∈ B_κ}
[R_μ(ω)]^{P̃:κ→λ̃→μ}_{P:λ→μ} [(U^ω_twist)†]^P_{P̃,κ}`, with `ω = e` (`false`) or `ω = w` (`true`):
* `ω = e`: `κ` is a `B`-irrep, valid when `κ = λ = λ̃` (`N(λ^e) = {λ}`, `N⁻_{B≤B}(λ̃) = {λ̃}`), and
  `P̃ : κ → λ̃` is `P̃` itself;
* `ω = w`: `κ = χ_{a,b}` is a `T`-character (`d_κ = 1`, `B_κ` a point), stored as the `B`-label
  `inl (a, b)`, and `P̃ : κ → λ̃` is `tLab λ̃ κ`.

**Formalization Note** The block is defined from (70), not from the displays (128)–(145); for
`λ = λ̃ = ρ_γ` it agrees with the published `AGamma` (144)–(145), and every block is unitary
(`numerics/a70_check.py`, `q = 3, 5, 7`). -/
def A70 (l lt κ : D.BIrr) (ω : Bool) (μ : D.Irr) : ℂ :=
  if ω then
    match κ with
    | .inl ab =>
        (Real.sqrt ((Fintype.card (D.Bas μ) : ℝ) * D.q /
          (1 * (Fintype.card (D.BBas l) : ℝ) * (Fintype.card (D.BBas lt) : ℝ) * (D.q + 1))) : ℂ) *
          ∑ P : D.BBas l,
            (match (tLab D) lt ab with
              | some Pt => (Rent D) μ (wGL D) ((labMu D) μ lt Pt) ((labMu D) μ l P)
              | none => 0) * conj ((utwW D) l ab P)
    | .inr _ => 0
  else
    if h : κ = l ∧ lt = l then
      (Real.sqrt ((Fintype.card (D.Bas μ) : ℝ) * 1 /
        ((Fintype.card (D.BBas κ) : ℝ) * (Fintype.card (D.BBas l) : ℝ) *
          (Fintype.card (D.BBas lt) : ℝ) * (D.q + 1))) : ℂ) *
        ∑ P : D.BBas l, ∑ Pt : D.BBas κ,
          (Rent D) μ 1 ((labMu D) μ lt (cast (congrArg D.BBas (h.1.trans h.2.symm)) Pt))
              ((labMu D) μ l P) *
            conj (if cast (congrArg D.BBas h.1) Pt = P then (1 : ℂ) else 0)
    else 0

/-- arXiv:2608.28573, eq. (64), p.28, for `B < G` (§6.4.3): `(κ, ω) ∈ K_{λ,λ̃}`:
`ω = e`: `κ = λ = λ̃`; `ω = w`: `κ = χ_{a,b}` with `χ_{a,b} ∈ N(λ^w)` (`λ = χ_{α,β}`: `(a,b) = (β,α)`;
`λ = ρ_γ`: `ab = γ`) and `χ_{a,b} ∈ N⁻_{T≤B}(λ̃)` (`λ̃ = χ_{α,β}`: `(a,b) = (α,β)`; `λ̃ = ρ_γ`:
`ab = γ`). -/
def ValidIn (l κ : D.BIrr) (ω : Bool) (lt : D.BIrr) : Prop :=
  if ω then
    (∃ ab : D.Lab × D.Lab, κ = .inl ab ∧
      (match l with
        | .inl αβ => ab = (αβ.2, αβ.1)
        | .inr γ => ab.1 + ab.2 = γ) ∧
      (match lt with
        | .inl αβ => ab = αβ
        | .inr γ => ab.1 + ab.2 = γ))
  else κ = l ∧ lt = l

/-- The input registers `(λ, κ, ω, λ̃)` of the total A-matrix, restricted to the multiplicity
labels `(κ, ω) ∈ K_{λ,λ̃}` (the domain `⊕_{λ,λ̃} |λ⟩ ⊗ ℂ[K_{λ,λ̃}] ⊗ |λ̃⟩` of `A`). -/
abbrev InReg : Type := {x : D.BIrr × D.BIrr × Bool × D.BIrr // (ValidIn D) x.1 x.2.1 x.2.2.1 x.2.2.2}

/-- The output registers `(λ, μ, λ̃)`, `μ ∈ Ĝ`. -/
abbrev OutReg : Type := D.BIrr × D.Irr × D.BIrr

/-- arXiv:2608.28573, Definition 5.3, p.30, and the proof of Theorem 6.14, p.47: the total A-matrix
`A = Σ_{λ,λ̃ ∈ B̂} |λ⟩⟨λ| ⊗ A_{λ,λ̃} ⊗ |λ̃⟩⟨λ̃|` of the Mackey circuit for `B < GL₂(F_q)`, blocks (70). -/
def totalA : Matrix (OutReg D) (InReg D) ℂ :=
  Matrix.of fun y x =>
    if y.1 = x.1.1 ∧ y.2.2 = x.1.2.2.2 then (A70 D) x.1.1 x.1.2.2.2 x.1.2.1 x.1.2.2.1 y.2.1 else 0

/-- The three label fields `[tag, parameter 1, parameter 2]` of a `B`-irrep (or `T`-character
`χ_{a,b}`): `χ_{α,β} ↦ [0, α, β]`, `ρ_γ ↦ [1, γ, 0]` (as in `bOutCode`). -/
def birrFields : D.BIrr → Fin 3 → ℕ
  | .inl ab => ![0, ab.1.val, ab.2.val]
  | .inr γ => ![1, γ.val, 0]

/-- The input code of the total A-matrix: ten fields of `⌈log₂(q²)⌉` bits,
`[λ (3 fields), κ (3 fields), ω (0 for e, 1 for w), λ̃ (3 fields)]`. -/
def inCodeA (x : (InReg D)) : Qubits (10 * D.labW) :=
  packNat 10 D.labW
    ![(birrFields D) x.1.1 0, (birrFields D) x.1.1 1, (birrFields D) x.1.1 2,
      (birrFields D) x.1.2.1 0, (birrFields D) x.1.2.1 1, (birrFields D) x.1.2.1 2,
      if x.1.2.2.1 then 1 else 0,
      (birrFields D) x.1.2.2.2 0, (birrFields D) x.1.2.2.2 1, (birrFields D) x.1.2.2.2 2]

/-- The output code of the total A-matrix: nine fields, `[λ (3), μ (3, `irrFields`), λ̃ (3)]`. -/
def outCodeA (y : (OutReg D)) : Qubits (9 * D.labW) :=
  packNat 9 D.labW
    ![(birrFields D) y.1 0, (birrFields D) y.1 1, (birrFields D) y.1 2,
      D.irrFields y.2.1 0, D.irrFields y.2.1 1, D.irrFields y.2.1 2,
      (birrFields D) y.2.2 0, (birrFields D) y.2.2 1, (birrFields D) y.2.2 2]

end TotalA

end Supplement

end GL2QFT


