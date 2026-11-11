-- Prove2me | Definitions.Def_GL2QFT_Irreps
-- name    : GL2QFT_Irreps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:44.576229+00:00
-- url     : https://prove2.me/theorems/4fe18b32-405b-424d-9a24-8cede194d928
-- title:
--   The irreducible representations of $\mathrm{GL}_2(\mathbb F_q)$ and of $B$ in their Gelfand–Tsetlin bases (Table 2)
-- statement:
--   The labels, basis index sets and representation matrices of Table 2, and of the Borel subgroup $B$.
--
--   1. **Labels.** $\det_\alpha$ and $\mathrm{St}_\alpha$ for $\alpha\in X_q$; $I_{\alpha,\beta}$ for $\alpha\prec\beta$, where $\prec$ is the order of exponent labels (p.44: "Fix a total order $\prec$ on $X_q$ and represent a principal series by $I_{\alpha,\beta}$ with $\alpha\prec\beta$"); and $\pi_{\theta_k}$ for $k$ regular ($(q+1)\nmid k$, i.e. $\theta^q\neq\theta$) and the smaller representative of its Frobenius orbit $\{k,qk\}$.
--   2. **Bases.** $\det_\alpha$: $|v\rangle$; $\mathrm{St}_\alpha$: $|v^\perp\rangle,|w_\delta\rangle$; $I_{\alpha,\beta}$: $|\infty\rangle,|v_0\rangle,|w_\delta\rangle$ built with $\beta$; $\pi_\theta$: the multiplicative Fourier basis. The dimensions are $1,q,q+1,q-1$.
--   3. **Matrices.** $[R_\mu(g)]^i_j=\langle b_i|M_\mu(g)|b_j\rangle$ for the model $M_\mu$ ($I_{\alpha,\alpha}$, $I_{\alpha,\beta}$ or $\pi_\theta$) and the basis vectors $b$ above.
--   4. **Borel subgroup.** Its irreps are $\chi_{\alpha,\beta}$ (87) and $\rho_\gamma$ in the basis (108); the circuit of Theorem 6.13 parametrizes $B$ by triples $(a,d,b)\in\mathbb F_q^*\times\mathbb F_q^*\times\mathbb F_q$ via $\begin{pmatrix}1&b\\0&1\end{pmatrix}\begin{pmatrix}a&0\\0&d\end{pmatrix}$.
--
--   This family is the "chosen representatives and orthonormal bases" of Proposition 2.7 for $\mathrm{GL}_2(\mathbb F_q)$; the QFT of the goal theorem is taken in it.
--
--   **Formalization Note** The orbit representative is the smaller exponent: $\pi_\theta$ and $\pi_{\theta^q}$ have identical matrices in this model, since $\theta=\theta^q$ on $\mathbb F_q^*$ and $j_\theta=j_{\theta^q}$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1.1 and Table 2, pp.35–36 (PDF pp.36–37); §6.2 pp.37–39; §6.4.4 p.44 (order ≺); §6.4.2 p.43 and (125) p.44 (parametrization of B)

import Definitions.Def_GL2QFT_RepBasics
import Definitions.Def_GL2QFT_Models

noncomputable section

open Classical

namespace GL2QFT

namespace FieldData

variable (D : FieldData)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), p.36: the exponent label `k` of `θ = θ_k ∈
X_{q²}` is a cuspidal label if `θ` is regular (`θ^q ≠ θ`, i.e. `(q+1) ∤ k`) and `k` is the chosen
representative of its Frobenius orbit `{θ, θ^q}`: `k ≤ qk mod (q²−1)` as integers in `[0, q²−2]`.

**Formalization Note** `π_θ ≃ π_{θ^q}`, and in the model (99)–(100) the two have identical matrices
(`θ = θ^q` on `F*_q`, and `j_θ = j_{θ^q}` by `v ↦ v^q`), so the orbit is represented by its smaller
exponent. -/
def IsCuspLabel (k : D.Lab2) : Prop :=
  ¬ (D.q + 1 ∣ k.val) ∧ k.val ≤ ((D.q : D.Lab2) * k).val

instance (k : D.Lab2) : Decidable (D.IsCuspLabel k) := by
  unfold IsCuspLabel; infer_instance

/-- arXiv:2608.28573, Table 2, p.36 (PDF p.37), with the order `≺` of p.44: the labels of the
irreducible representations of `GL₂(F_q)`:
1. `det α` (`χ_α ∘ det`, dimension 1), `α ∈ X_q`;
2. `st α` (`St_α`, dimension `q`), `α ∈ X_q`;
3. `ps (α, β)` (`I_{α,β}`, dimension `q+1`) for `α ≺ β`;
4. `cusp k` (`π_{θ_k}`, dimension `q−1`) for a cuspidal label `k` (`IsCuspLabel`).

**Formalization Note** `Irr D` is the sum `Lab ⊕ Lab ⊕ {(α,β) // α ≺ β} ⊕ {k // IsCuspLabel k}`,
in this order. The total order `≺` on `X_q` ("Fix a total order `≺` on `X_q` and represent a
principal series by `I_{α,β}` with `α ≺ β`", p.44) is the order of exponent labels
`α.val < β.val`. -/
abbrev Irr : Type :=
  D.Lab ⊕ D.Lab ⊕ {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} ⊕ {k : D.Lab2 // D.IsCuspLabel k}

/-- The orthonormal-basis index type of each irrep (dimensions `1, q, q+1, q−1`, Table 2):
`det`: `Unit`; `st`: `Option Lab` (`|v^⊥⟩`, `|w_δ⟩`), (112); `ps`: `Option (Option Lab)`
(`|∞⟩`, `|v₀⟩`, `|w_δ⟩`), (110); `cusp`: `Lab` (`|w_δ⟩`), (108). -/
def Bas : D.Irr → Type
  | .inl _ => Unit
  | .inr (.inl _) => Option D.Lab
  | .inr (.inr (.inl _)) => Option (Option D.Lab)
  | .inr (.inr (.inr _)) => D.Lab

instance instFintypeBas : ∀ μ : D.Irr, Fintype (D.Bas μ)
  | .inl _ => inferInstanceAs (Fintype Unit)
  | .inr (.inl _) => inferInstanceAs (Fintype (Option D.Lab))
  | .inr (.inr (.inl _)) => inferInstanceAs (Fintype (Option (Option D.Lab)))
  | .inr (.inr (.inr _)) => inferInstanceAs (Fintype D.Lab)

instance instDecEqBas : ∀ μ : D.Irr, DecidableEq (D.Bas μ)
  | .inl _ => inferInstanceAs (DecidableEq Unit)
  | .inr (.inl _) => inferInstanceAs (DecidableEq (Option D.Lab))
  | .inr (.inr (.inl _)) => inferInstanceAs (DecidableEq (Option (Option D.Lab)))
  | .inr (.inr (.inr _)) => inferInstanceAs (DecidableEq D.Lab)

/-- arXiv:2608.28573, §6.1–6.2, pp.35–39: the chosen representative `R_μ` of each irrep of
`GL₂(F_q)`, written in its Gelfand–Tsetlin basis: the entry `[R_μ(g)]^i_j = ⟨b_i|M_μ(g)|b_j⟩`, where
`M_μ` is the explicit model and `b` the explicit basis:
* `det α`: `M = I_{α,α}` (94), `b = |v⟩` (97)/(111); this is `χ_α(det g)` by (98);
* `st α`: `M = I_{α,α}`, `b = |v^⊥⟩, |w_δ⟩` (112);
* `ps (α, β)`, `α ≺ β`: `M = I_{α,β}`, `b = |∞⟩, |v₀⟩, |w_δ⟩` (110) (built with `β`);
* `cusp k`: `M = π_{θ_k}` (99)–(100), `b = |w_δ⟩` (108).

**Formalization Note** The matrix argument is `g` viewed as a `2 × 2` matrix. -/
def R : (μ : D.Irr) → D.G → Matrix (D.Bas μ) (D.Bas μ) ℂ
  | .inl α => fun g _ _ =>
      matEntry (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) (D.detVec α) (D.detVec α)
  | .inr (.inl α) => fun g i j =>
      matEntry (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) (D.stVec α i) (D.stVec α j)
  | .inr (.inr (.inl ab)) => fun g i j =>
      matEntry (D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.psVec ab.1.2 i) (D.psVec ab.1.2 j)
  | .inr (.inr (.inr k)) => fun g i j =>
      matEntry (D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq)) (D.multVec i) (D.multVec j)

/-! ### The Borel subgroup -/

/-- arXiv:2608.28573, §6.1.1, p.35: the labels of the irreducible representations of the Borel
subgroup `B`: `inl (α, β)` is the character `χ_{α,β}` (87), `inr γ` is `ρ_γ` (89). -/
abbrev BIrr : Type := (D.Lab × D.Lab) ⊕ D.Lab

/-- Basis index types for the irreps of `B`: `χ_{α,β}`: `Unit`; `ρ_γ`: `Lab` (`|w_δ⟩`, (108)). -/
def BBas : D.BIrr → Type
  | .inl _ => Unit
  | .inr _ => D.Lab

instance instFintypeBBas : ∀ ν : D.BIrr, Fintype (D.BBas ν)
  | .inl _ => inferInstanceAs (Fintype Unit)
  | .inr _ => inferInstanceAs (Fintype D.Lab)

instance instDecEqBBas : ∀ ν : D.BIrr, DecidableEq (D.BBas ν)
  | .inl _ => inferInstanceAs (DecidableEq Unit)
  | .inr _ => inferInstanceAs (DecidableEq D.Lab)

/-- arXiv:2608.28573, (87), (89), (108), pp.35–37: the irreps of `B` in their bases, evaluated at an
upper triangular matrix `M = (a b; 0 d)`: `χ_{α,β}(M) = χ_α(a)χ_β(d)`, and `ρ_γ(M)` in the
multiplicative Fourier basis (108), `[ρ_γ(M)]^δ_{δ'} = ⟨w_δ|ρ_γ(M)|w_{δ'}⟩`.

**Formalization Note** `M` is any `2 × 2` matrix; only `M 0 0`, `M 0 1`, `M 1 1` are read, so the
value is meaningful on `B` (`M 1 0 = 0`). -/
def RB : (ν : D.BIrr) → Matrix (Fin 2) (Fin 2) D.Fq → Matrix (D.BBas ν) (D.BBas ν) ℂ
  | .inl ab => fun M _ _ => D.chi ab.1 (M 0 0) * D.chi ab.2 (M 1 1)
  | .inr γ => fun M i j => matEntry (D.borelModel γ (M 0 0) (M 0 1) (M 1 1)) (D.multVec i) (D.multVec j)

/-- arXiv:2608.28573, §6.4.2, p.43 and (125), p.44: the parametrization of `B` used by the circuit
of Theorem 6.13: the triple `(a, d, b) ∈ F*_q × F*_q × F_q` encodes
`(1 b; 0 1)(a 0; 0 d) = (a, bd; 0, d)`. -/
abbrev BElt : Type := D.Fqˣ × D.Fqˣ × D.Fq

/-- The matrix `(1 b; 0 1)(a 0; 0 d) = (a, bd; 0, d)` of `(a, d, b) : BElt D`. -/
def bmat (x : D.BElt) : Matrix (Fin 2) (Fin 2) D.Fq :=
  !![(x.1 : D.Fq), x.2.2 * (x.2.1 : D.Fq); 0, (x.2.1 : D.Fq)]

end FieldData

end GL2QFT


